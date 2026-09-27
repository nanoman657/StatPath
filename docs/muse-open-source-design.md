# Open Muse: a Muse-style assistant on open-weight models, kept in the US

Status: design draft, September 2026

## 1. Goal

Build a personal assistant with the main features of Meta AI running on **Muse Spark**. It should run on a single **DigitalOcean droplet** and use **GLM 5.3** (Z.ai's open-weight model) through **OpenRouter**. Every prompt, file, and completion must stay **inside the United States** from start to finish.

### What we are copying from Muse Spark

Meta launched Muse Spark in April 2026. It powers Meta AI in the Meta AI app and across WhatsApp, Instagram, Facebook, Messenger, and Threads. The features users see are:

| Muse / Meta AI feature | Scope for Open Muse v1 |
|---|---|
| Multimodal chat with visible reasoning and a long context | Yes |
| Voice conversation you can interrupt, with language switching | Yes (turn-based in v1, interruptible in v2) |
| "Live AI": point the camera at something and ask about it | Yes, as a photo or video frame sent to the model (continuous video in v2) |
| Agentic tasks: planning, email and calendar, making slides | Yes, with a confirmation step before any action that changes something |
| Memory and personalization | Yes |
| Web search with citations | Yes |
| Image generation ("Imagine") | v2 |
| Embedding in social apps | No. We ship one web app (PWA) |
| Muse Code terminal agent | No |

## 2. The residency guarantee: where data goes

```
 Browser (PWA) ──TLS──▶ DO droplet, NYC3 or SFO3 ──TLS──▶ us.openrouter.ai ──▶ US-hosted GLM 5.3 provider
                              │
                              ├─ Postgres + pgvector (on the droplet)
                              ├─ DO Spaces bucket, same US region (uploads)
                              └─ Speech-to-text and text-to-speech run on the droplet
```

Four rules together keep data in the US:

1. **Compute.** The droplet and the Spaces bucket live in a US region: `nyc3` or `sfo3`. Both regions offer droplets and Spaces. Do not use `tor1`, which is in Canada, or any EU or APAC region. Pick the region once, in Terraform, and check it in CI.
2. **No edge proxy outside the US.** Do not put Cloudflare's orange-cloud proxy, or any other global CDN, in front of the app. A global proxy terminates TLS at whichever point of presence is nearest the user, and that can be outside the US. Caddy on the droplet terminates TLS itself. A DigitalOcean Cloud Firewall allows only ports 80 and 443 from anywhere, and port 22 only from an admin IP.
3. **Model traffic uses OpenRouter's US in-region endpoint.** Requests go to `https://us.openrouter.ai/api/v1`. That endpoint decrypts and processes the request inside the US, sends it only to US provider endpoints, and **rejects the request with a 404** when no US provider is available. It never falls back to a provider outside the US. In-region routing requires an OpenRouter **Business or Enterprise** plan.
4. **No retention, no training.** Every request also sends `provider.zdr: true` (zero data retention) and `provider.data_collection: "deny"`. We also block Z.ai's own first-party endpoint by name. The US endpoint already excludes it, and the explicit block covers us if someone misconfigures the base URL later.

On a Free or Pay-as-you-go OpenRouter plan, the fallback is a `provider.only` allow-list of US providers (see §4.2) with `allow_fallbacks: false`. Treat that as the weaker option. It picks providers by company, but it does not *enforce* where the request is processed. A provider that also runs data centers abroad is not guaranteed to serve us from the US.

**The model is Chinese; the hosting is not.** GLM 5.3 is open weights, published on Hugging Face under the GLM-5.3 License. That license is MIT-style, with one extra condition: model-as-a-service operators earning more than $10B a year need a Z.ai review. A US provider runs the weights on US hardware, so no request, prompt, or telemetry reaches Z.ai. The residency argument rests on where the model runs, not on who trained it.

## 3. Model lineup (all through OpenRouter)

| Role | Model | Why |
|---|---|---|
| Main reasoning and agent loop | `z-ai/glm-5.3` | ~744B mixture-of-experts with ~40B active, 1M-token context, 128K max output. Strong at tool use and coding. Released 14 Aug 2026; weights published 28 Aug. |
| Vision (camera, photos, screenshots) and fast calls | `z-ai/glm-5.3-flash` | Natively multimodal, MIT license. Also handles the cheap calls: chat titles, memory extraction, deciding which model a message needs. |
| Low-latency voice replies | `z-ai/glm-5.3-flashx` | High-speed variant of Flash, used when speed matters more than depth. |

Model IDs, and which providers serve each model in the US, change often. The app reads them from config, not code. A nightly job calls `GET /api/v1/models` and `.../endpoints` on the US endpoint and raises an alert if a model loses all its US providers.

**Routing between models.** A small classifier call to Flash, or plain rules (an image is attached → Flash; voice mode → FlashX; everything else → GLM 5.3), picks the model for each message. The user can override the choice with a "Think harder" toggle, which forces GLM 5.3 with reasoning turned on. This is the same idea as Muse Spark's instant and thinking modes.

## 4. System architecture

### 4.1 One droplet running Docker Compose

Size: a **General Purpose droplet with 4 vCPU and 16 GB RAM** in `nyc3`, plus weekly backups. The model runs remotely, so the droplet does no inference except speech on the CPU. Upgrade to 8 vCPU when speech-to-text becomes the bottleneck.

```
caddy        :80/:443   TLS (Let's Encrypt), HTTP/2 + HTTP/3, serves the PWA, proxies /api and /ws
web          static     SvelteKit PWA: chat, voice, camera, settings, memory manager
api          :8000      FastAPI: auth, conversations, streaming (SSE), agent loop, tool runners
worker       -          same image as api; runs long agent tasks, scheduled reminders, file processing (Redis queue)
postgres     :5432      Postgres 16 + pgvector: users, conversations, messages, memories, tool grants, audit log
redis        :6379      queue, rate limits, streaming fan-out
speech       :9000      faster-whisper (small.en / multilingual small, int8, CPU) + Kokoro-82M TTS (Apache-2.0)
embed        :9100      bge-small-en-v1.5 through fastembed on the CPU (for memory and file retrieval)
```

Speech and embeddings run on the droplet because that is the simplest way to keep voice and memory data in the US. No external speech or embedding API gets involved.

Backups: the nightly `pg_dump` is encrypted with `age` and uploaded to a **Spaces bucket in the same region**. Weekly droplet snapshots stay in the same region.

### 4.2 The OpenRouter client

All model calls go through one wrapper, so the residency settings cannot be left out by accident:

```python
OPENROUTER_BASE = "https://us.openrouter.ai/api/v1"   # in-region endpoint; never the global one

PROVIDER_POLICY = {
    "zdr": True,
    "data_collection": "deny",
    "ignore": ["z-ai"],            # never Z.ai's own endpoint
    "allow_fallbacks": True,       # fallbacks are safe: the US endpoint only falls back among US providers
    "require_parameters": True,    # only providers that support tools / reasoning we send
    "sort": "throughput",          # voice path; "price" for background jobs
}

# Fallback for non-Business plans: the weaker allow-list option from §2
PROVIDER_POLICY_ALLOWLIST = {
    **PROVIDER_POLICY,
    "only": ["deepinfra", "fireworks", "together", "baseten"],  # verify each serves GLM 5.3 before enabling
    "allow_fallbacks": False,
}

async def chat(messages, *, model, tools=None, reasoning=None, stream=True):
    body = {"model": model, "messages": messages, "stream": stream,
            "provider": PROVIDER_POLICY, "usage": {"include": True}}
    if tools: body["tools"] = tools
    if reasoning: body["reasoning"] = reasoning         # {"effort": "high"} for "Think harder"
    return await http.post(f"{OPENROUTER_BASE}/chat/completions", json=body,
                           headers={"Authorization": f"Bearer {OR_KEY}",
                                    "X-Title": "Open Muse"})
```

- A 404 from the US endpoint means no compliant provider is available. The app shows "the model is temporarily unavailable" and retries with backoff. It **never** retries against the global endpoint.
- Streamed tokens go from OpenRouter's SSE stream to the api service, then to the browser as SSE. Reasoning tokens are shown in a collapsible "Thinking" section, like Muse's visible reasoning.
- Usage returned in each response (tokens and cost) is saved per message and feeds each user's budget.

### 4.3 The agent loop

A standard tool-calling loop runs in `api`. Tasks longer than about 30 seconds move to `worker`.

1. Build the context: system prompt, the user's top-k memories (pgvector), and recent turns. Older turns are summarized. The 1M-token window is a ceiling, not a target, because cost and latency grow with length.
2. Call GLM 5.3 with the tools.
3. Run each tool call. **Tools that change something need approval**: the loop pauses and the UI shows an approval card ("Send this email to Dana?"). The loop resumes only when the user approves.
4. Stop after 15 steps or when the per-task token budget runs out.

| Tool | Side effects | Implementation |
|---|---|---|
| `web_search` | no | Brave Search API (US company). Results are cited in the answer. |
| `fetch_url` | no | httpx plus readability, run on the droplet. Only public addresses (SSRF guard); 2 MB cap. |
| `calendar.list / calendar.create` | create: yes | Google Calendar or Microsoft Graph through per-user OAuth. Tokens are encrypted at rest. |
| `email.search / email.draft / email.send` | send: yes | Gmail or Graph. `draft` is the default and `send` always asks for approval. |
| `slides.create` | writes a file | The model outputs a JSON outline, python-pptx builds the .pptx, and the file is saved to Spaces behind a signed link. |
| `memory.save / memory.forget` | yes (quietly) | Postgres. Every memory is shown and editable in Settings → Memory. |
| `reminder.create` | yes | A row the worker schedules. Delivered by web push. |
| `image.describe` | no | Calls Flash on an uploaded image or camera frame. |

**Prompt injection.** Text that comes back from `fetch_url`, `web_search`, and email is wrapped as untrusted data. It cannot trigger an action on its own: every action needs user approval anyway, and the approval card shows the exact recipient and content.

### 4.4 Voice

- **v1, turn-based.** The browser records with MediaRecorder, and voice-activity detection runs in the browser (Silero VAD in WASM). The clip goes to `speech/stt` (faster-whisper), the text goes to FlashX (streamed), and each sentence goes to `speech/tts` (Kokoro) as soon as it is complete, then plays in the browser. Target: under 2 seconds to the first audio.
- **Interrupting.** When the user starts speaking during playback, the client stops the audio and cancels the running stream (the SSE is aborted and OpenRouter's stream is closed). This covers most of Muse's "interrupt anytime" behavior.
- **v2.** A WebSocket duplex stream with partial transcripts. Consider a GPU droplet for a larger Whisper model, but only in `nyc2` or `atl1`, never `tor1`.

### 4.5 Camera ("Live AI")

In v1 the PWA's camera view takes a frame when the user taps or asks a question by voice. The frame is downscaled to 1024 px and sent to GLM 5.3 Flash with the question. In v2, "live" mode samples one frame every 2 seconds while the user talks, and only the latest few frames go into the context.

### 4.6 Memory

- After each conversation, Flash extracts durable facts (preferences, people, projects) as JSON. Each fact is embedded, deduplicated by cosine similarity above 0.9, and stored along with the message it came from.
- Retrieval: the 8 memories most similar to the current message are injected as a `Known about the user` block.
- The user controls memory completely: they can view, edit, delete, pause, and export it. Incognito chats neither read nor write memory.

### 4.7 Accounts and limits

- Sign-in uses passkeys (WebAuthn) with an email magic link as a backup. Sessions are HTTP-only cookies.
- Each user has a per-minute rate limit in Redis and a **monthly spend cap** in dollars, computed from OpenRouter's `usage.cost`. Only admins can raise the cap.
- The audit log records every tool action: who approved it, and what was sent.

## 5. Deployment

- **Terraform (DigitalOcean provider):** the droplet (`region = "nyc3"`), a Cloud Firewall, a reserved IP, the Spaces bucket (`nyc3`), a project, and DNS records. A CI check fails if any region is not in `["nyc1","nyc3","sfo2","sfo3","atl1"]`.
- **Provisioning:** cloud-init installs Docker, creates a non-root deploy user, turns off password SSH, and enables unattended-upgrades and fail2ban.
- **Releases:** GitHub Actions builds the images, pushes them to DigitalOcean Container Registry (region `nyc3`), then runs `docker compose pull && docker compose up -d` over SSH. The deploy fails if the health check at `/api/health` does not pass.
- **Secrets:** `OPENROUTER_API_KEY`, `BRAVE_API_KEY`, the OAuth client secrets, and the database and encryption keys live in a root-only `.env` on the droplet, pushed from GitHub Actions secrets. The OpenRouter key has a credit limit set in the OpenRouter dashboard.
- **Observability:** the DigitalOcean monitoring agent handles CPU, memory, and disk alerts. Logs are structured JSON and rotated locally. **Prompts and completions are never logged.** Only IDs, token counts, latency, and the provider that served each request are logged. OpenRouter returns that provider in the response metadata, which also lets us audit that every request was served in the US.

## 6. Cost model (to fill in with current prices)

| Item | Monthly |
|---|---|
| Droplet, 4 vCPU / 16 GB, plus backups | about $100 |
| Spaces (250 GB included) | $5 |
| Container Registry (Basic) | $5 |
| OpenRouter Business plan | per contract |
| Model tokens | `users × msgs/day × 30 × (in_tok × $in + out_tok × $out) / 1e6` |
| Brave Search | by query volume |

Look up current GLM 5.3, Flash, and FlashX prices per million tokens for **US providers only** on OpenRouter before budgeting. US providers can cost more than the cheapest provider worldwide. Most token spend will come from the agent loop's repeated context, so summarize history aggressively and use prompt caching where the provider supports it.

## 7. Risks and open questions

1. **Few US providers.** If every US host drops GLM 5.3, in-region routing returns 404s. Mitigation: `models` in the request lists `z-ai/glm-5.3` first, then an equally capable open model that is available in the US. The nightly check from §3 raises an alert early.
2. **Plan requirement.** US in-region routing needs an OpenRouter Business or Enterprise plan. The allow-list fallback exists, but it proves less about where requests are processed. Decide which one we need before launch.
3. **Muse's features, not Meta's scale.** One droplet serves roughly hundreds of active users; speech-to-text load is the first bottleneck. Beyond that, split `speech` onto its own droplet, move Postgres to DigitalOcean Managed Postgres (same region), and put a DigitalOcean Load Balancer in front of two or more `api` droplets.
4. **License.** The GLM-5.3 License is permissive at our size. Record it in `THIRD_PARTY.md` and check it again if the business grows.
5. **Self-hosting later.** Running GLM 5.3 ourselves (for example with vLLM on 8×H100 DigitalOcean GPU droplets in `nyc2` or `atl1`) would remove OpenRouter from the data path. It costs far more than paying per token at small scale. Revisit only when a compliance requirement or steady high volume justifies it.

## 8. Milestones

1. **Week 1–2:** Terraform setup, Compose stack, auth, streaming text chat with the US-routed OpenRouter client, and a residency check in CI.
2. **Week 3:** Memory, web search and fetch, image upload through Flash.
3. **Week 4:** Voice (turn-based) and camera capture.
4. **Week 5–6:** Agent tools (calendar, email, slides, reminders) with approval cards and the audit log.
5. **Week 7:** Spend caps, monitoring, backups, load test, and a hardening pass.

## Sources

- Meta: [Introducing Muse Spark](https://about.fb.com/news/2026/04/introducing-muse-spark-meta-superintelligence-labs/), [Meta AI doesn't just think, it acts](https://about.fb.com/news/2026/07/meta-ai-muse-spark-doesnt-just-think-it-acts/), [9to5Mac on the Muse-powered Meta AI app](https://9to5mac.com/2026/05/12/meta-ai-app-enhanced-with-new-features-using-muse-spark-heres-whats-new/)
- OpenRouter: [US in-region routing](https://openrouter.ai/blog/announcements/us-in-region-routing/), [Sovereign AI / in-region routing docs](https://openrouter.ai/docs/guides/features/sovereign-ai), [Data residency at the routing layer](https://openrouter.ai/blog/insights/ai-data-residency/), [GLM 5.3](https://openrouter.ai/z-ai/glm-5.3), [GLM 5.3 Flash](https://openrouter.ai/z-ai/glm-5.3-flash), [GLM 5.3 FlashX](https://openrouter.ai/z-ai/glm-5.3-flashx)
- Z.ai: [GLM-5.3 on Hugging Face](https://huggingface.co/zai-org/GLM-5.3), [GLM-5.3-Flash/FlashX docs](https://docs.z.ai/guides/vlm/glm-5.3-flash), [GLM-5.3 license notes](https://runaihome.com/blog/glm-5-3-open-weights-live-hardware-guide-2026/)
