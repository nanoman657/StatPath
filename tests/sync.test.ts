import { afterEach, describe, expect, it, vi } from "vitest";
import { GIST_FILENAME, SyncError, defaultSync, syncNow } from "../src/engine/sync";
import { completeLesson, defaultProgress, type Progress } from "../src/engine/progress";

const T = Date.UTC(2026, 4, 10, 12);
const TOKEN = "ghp_pretend_token_value";

const play = (p: Progress, lessonId: string, at: number): Progress =>
  completeLesson(p, { lessonId, correct: 10, total: 10, answers: [{ id: `${lessonId}.a`, correct: true }], perfect: true }, at).progress;

/** Minimal in-memory stand-in for the Gists API, recording every call. */
function stubGitHub(opts: { gists?: Record<string, Progress>; status?: number; body?: string } = {}) {
  const store: Record<string, Progress> = { ...(opts.gists ?? {}) };
  const calls: { method: string; path: string; body?: string; auth?: string }[] = [];
  let nextId = 100;
  const fetchStub = vi.fn(async (url: string, init: RequestInit = {}) => {
    const path = url.replace("https://api.github.com", "");
    const method = init.method ?? "GET";
    const headers = init.headers as Record<string, string>;
    calls.push({ method, path, body: init.body as string | undefined, auth: headers?.Authorization });
    const json = (status: number, data: unknown) =>
      ({ ok: status < 400, status, json: async () => data, text: async () => JSON.stringify(data) }) as Response;
    if (opts.status) return { ok: false, status: opts.status, json: async () => ({}), text: async () => opts.body ?? "" } as Response;
    if (method === "GET" && path.startsWith("/gists?")) {
      return json(200, Object.keys(store).map((id) => ({ id, files: { [GIST_FILENAME]: {} } })));
    }
    if (method === "GET" && path.startsWith("/gists/")) {
      const id = path.split("/")[2];
      if (!store[id]) return json(404, { message: "Not Found" });
      return json(200, { id, files: { [GIST_FILENAME]: { content: JSON.stringify(store[id]) } } });
    }
    if (method === "POST" && path === "/gists") {
      const id = String(nextId++);
      store[id] = JSON.parse(JSON.parse(init.body as string).files[GIST_FILENAME].content);
      return json(201, { id });
    }
    if (method === "PATCH" && path.startsWith("/gists/")) {
      const id = path.split("/")[2];
      store[id] = JSON.parse(JSON.parse(init.body as string).files[GIST_FILENAME].content);
      return json(200, { id });
    }
    return json(404, { message: "Not Found" });
  });
  vi.stubGlobal("fetch", fetchStub);
  return { store, calls };
}

afterEach(() => vi.unstubAllGlobals());

describe("syncNow", () => {
  it("creates the gist on first use", async () => {
    const { store, calls } = stubGitHub();
    const local = play(defaultProgress(), "u1.1", T);
    const out = await syncNow(local, { ...defaultSync(), token: TOKEN }, T);
    expect(out.action).toBe("created");
    expect(out.settings.gistId).toBeTruthy();
    expect(store[out.settings.gistId!].lessons["u1.1"].crowns).toBe(1);
    expect(calls.every((c) => c.auth === `Bearer ${TOKEN}`)).toBe(true);
  });

  it("finds an existing gist so a second device needs only the token", async () => {
    const remote = play(defaultProgress(), "u1.1", T);
    stubGitHub({ gists: { g1: remote } });
    const out = await syncNow(defaultProgress(), { ...defaultSync(), token: TOKEN }, T);
    expect(out.settings.gistId).toBe("g1");
    expect(out.progress.lessons["u1.1"].crowns).toBe(1); // pulled onto the fresh device
  });

  it("combines work from both sides rather than overwriting", async () => {
    const base = play(defaultProgress(), "u1.1", T);
    const remote = play(base, "u1.2", T + 86400000);
    const { store } = stubGitHub({ gists: { g1: remote } });
    const local = play(base, "u1.3", T + 86400000);
    const out = await syncNow(local, { ...defaultSync(), token: TOKEN, gistId: "g1" }, T);
    for (const id of ["u1.1", "u1.2", "u1.3"]) {
      expect(out.progress.lessons[id].crowns, id).toBe(1);
      expect(store.g1.lessons[id].crowns, `${id} pushed`).toBe(1);
    }
  });

  it("reports being up to date without writing", async () => {
    const same = play(defaultProgress(), "u1.1", T);
    const { calls } = stubGitHub({ gists: { g1: same } });
    const out = await syncNow(same, { ...defaultSync(), token: TOKEN, gistId: "g1" }, T);
    expect(out.action).toBe("in-sync");
    expect(calls.some((c) => c.method === "PATCH")).toBe(false);
  });

  it("recreates the gist if it was deleted on GitHub", async () => {
    const { store } = stubGitHub();
    const local = play(defaultProgress(), "u1.1", T);
    const out = await syncNow(local, { ...defaultSync(), token: TOKEN, gistId: "gone" }, T);
    expect(out.action).toBe("created");
    expect(out.settings.gistId).not.toBe("gone");
    expect(Object.keys(store)).toContain(out.settings.gistId!);
  });

  it("never uploads the token", async () => {
    const { calls, store } = stubGitHub();
    const out = await syncNow(play(defaultProgress(), "u1.1", T), { ...defaultSync(), token: TOKEN }, T);
    for (const c of calls) expect(c.body ?? "").not.toContain(TOKEN);
    expect(JSON.stringify(store[out.settings.gistId!])).not.toContain(TOKEN);
  });

  it("explains a rejected token instead of surfacing a raw status", async () => {
    stubGitHub({ status: 401 });
    await expect(syncNow(defaultProgress(), { ...defaultSync(), token: "bad" }, T)).rejects.toThrow(/rejected the token/i);
  });

  it("explains a missing gist scope", async () => {
    stubGitHub({ status: 403, body: "{}" });
    await expect(syncNow(defaultProgress(), { ...defaultSync(), token: TOKEN }, T)).rejects.toThrow(/gist scope/i);
  });

  it("distinguishes a rate limit from a scope problem", async () => {
    stubGitHub({ status: 403, body: '{"message":"API rate limit exceeded"}' });
    await expect(syncNow(defaultProgress(), { ...defaultSync(), token: TOKEN }, T)).rejects.toThrow(/rate limit/i);
  });

  it("refuses to run without a token", async () => {
    await expect(syncNow(defaultProgress(), defaultSync(), T)).rejects.toBeInstanceOf(SyncError);
  });
});
