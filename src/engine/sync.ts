/**
 * Cross-device sync through a secret GitHub Gist.
 *
 * There is no server: the browser talks to the GitHub API directly, using a
 * token the learner pastes in once per device. The gist holds one JSON file
 * with the same shape that is kept in local storage.
 *
 * The token is deliberately stored under its own key, separate from progress,
 * so it can never be serialized into the gist or shipped to another device.
 *
 * NOTE ON TOKEN TYPE: the Gists API does not accept fine-grained personal
 * access tokens. A classic token with only the `gist` scope is required. It may
 * be created with no expiry, so it never needs rotating.
 */
import { defaultProgress, type Progress } from "./progress";
import { mergeProgress } from "./merge";

export const GIST_FILENAME = "statpath-progress.json";
export const GIST_DESCRIPTION = "StatPath progress (synced automatically; safe to delete to reset)";
export const SYNC_KEY = "statpath.sync.v1";
/** Prefilled classic-token page: gist scope only, no expiry chosen by the user. */
export const TOKEN_URL = "https://github.com/settings/tokens/new?scopes=gist&description=StatPath%20sync";

const API = "https://api.github.com";

export interface SyncSettings {
  token: string;
  /** Discovered on first sync, then reused. */
  gistId: string | null;
  lastSyncedAt: number | null;
  lastError: string | null;
}

export const defaultSync = (): SyncSettings => ({ token: "", gistId: null, lastSyncedAt: null, lastError: null });

export const loadSync = (): SyncSettings => {
  try {
    const raw = typeof localStorage !== "undefined" ? localStorage.getItem(SYNC_KEY) : null;
    return raw ? { ...defaultSync(), ...(JSON.parse(raw) as SyncSettings) } : defaultSync();
  } catch {
    return defaultSync();
  }
};

export const saveSync = (s: SyncSettings): void => {
  try {
    if (typeof localStorage !== "undefined") localStorage.setItem(SYNC_KEY, JSON.stringify(s));
  } catch {
    /* ignore quota / private mode */
  }
};

export const clearSync = (): void => {
  try {
    if (typeof localStorage !== "undefined") localStorage.removeItem(SYNC_KEY);
  } catch {
    /* ignore */
  }
};

/** A failure worth showing the learner, rather than a raw HTTP error. */
export class SyncError extends Error {
  constructor(message: string, readonly status?: number) {
    super(message);
    this.name = "SyncError";
  }
}

const request = async (token: string, path: string, init: RequestInit = {}): Promise<any> => {
  let res: Response;
  try {
    res = await fetch(`${API}${path}`, {
      ...init,
      headers: {
        Authorization: `Bearer ${token}`,
        Accept: "application/vnd.github+json",
        "X-GitHub-Api-Version": "2022-11-28",
        ...(init.body ? { "Content-Type": "application/json" } : {}),
      },
    });
  } catch {
    throw new SyncError("Could not reach GitHub. Check your connection.");
  }
  if (res.status === 401) throw new SyncError("GitHub rejected the token. Create a new one and paste it again.", 401);
  if (res.status === 403) {
    const body = await res.text();
    throw new SyncError(
      /rate limit/i.test(body)
        ? "GitHub rate limit reached. Try again in a few minutes."
        : "The token is missing the gist scope. It must be a classic token with 'gist' ticked.",
      403,
    );
  }
  if (res.status === 404) throw new SyncError("Not found.", 404);
  if (!res.ok) throw new SyncError(`GitHub returned ${res.status}.`, res.status);
  return res.status === 204 ? null : res.json();
};

const fileFrom = (gist: any): string | undefined => gist?.files?.[GIST_FILENAME]?.content;

/**
 * Stable serialization with sorted keys, used only to decide whether anything
 * actually changed. Merging rebuilds the object, so plain JSON.stringify would
 * differ by key order alone and make every sync look like a change.
 */
export const canonical = (v: unknown): string => {
  if (v === null || typeof v !== "object") return JSON.stringify(v) ?? "null";
  if (Array.isArray(v)) return `[${v.map(canonical).join(",")}]`;
  const o = v as Record<string, unknown>;
  return `{${Object.keys(o).sort().map((k) => `${JSON.stringify(k)}:${canonical(o[k])}`).join(",")}}`;
};

const body = (p: Progress) => JSON.stringify({
  description: GIST_DESCRIPTION,
  files: { [GIST_FILENAME]: { content: JSON.stringify(p, null, 1) } },
});

/** Locate an existing StatPath gist on this account, so a second device needs only the token. */
export const findGist = async (token: string): Promise<string | null> => {
  const gists = await request(token, "/gists?per_page=100");
  const match = (gists as any[]).find((g) => g?.files && Object.keys(g.files).includes(GIST_FILENAME));
  return match?.id ?? null;
};

export const readGist = async (token: string, gistId: string): Promise<Progress | null> => {
  const gist = await request(token, `/gists/${gistId}`);
  const content = fileFrom(gist);
  if (!content) return null;
  try {
    return { ...defaultProgress(), ...(JSON.parse(content) as Progress) };
  } catch {
    throw new SyncError("The synced file is not readable. Disconnect and sync again to replace it.");
  }
};

export const createGist = async (token: string, p: Progress): Promise<string> => {
  const gist = await request(token, "/gists", { method: "POST", body: JSON.stringify({ ...JSON.parse(body(p)), public: false }) });
  return gist.id as string;
};

export const updateGist = async (token: string, gistId: string, p: Progress): Promise<void> => {
  await request(token, `/gists/${gistId}`, { method: "PATCH", body: body(p) });
};

export interface SyncOutcome {
  progress: Progress;
  settings: SyncSettings;
  /** What actually happened, for the status line. */
  action: "created" | "pushed" | "pulled" | "in-sync";
}

/**
 * Pull the shared copy, merge it with this device's, and push the result back
 * when it differs. Safe to call at any time; merging means a stale device can
 * never clobber work done elsewhere.
 */
export const syncNow = async (local: Progress, settings: SyncSettings, now: number = Date.now()): Promise<SyncOutcome> => {
  if (!settings.token) throw new SyncError("No token saved.");

  let gistId = settings.gistId ?? (await findGist(settings.token));
  if (!gistId) {
    gistId = await createGist(settings.token, local);
    return { progress: local, settings: { ...settings, gistId, lastSyncedAt: now, lastError: null }, action: "created" };
  }

  let remote: Progress | null;
  try {
    remote = await readGist(settings.token, gistId);
  } catch (e) {
    // The gist was deleted on GitHub; start a fresh one rather than failing.
    if (e instanceof SyncError && e.status === 404) {
      gistId = await createGist(settings.token, local);
      return { progress: local, settings: { ...settings, gistId, lastSyncedAt: now, lastError: null }, action: "created" };
    }
    throw e;
  }

  const merged = remote ? mergeProgress(local, remote) : local;
  const changedRemotely = !remote || canonical(merged) !== canonical(remote);
  const changedLocally = canonical(merged) !== canonical(local);
  if (changedRemotely) await updateGist(settings.token, gistId, merged);

  return {
    progress: merged,
    settings: { ...settings, gistId, lastSyncedAt: now, lastError: null },
    action: changedRemotely ? "pushed" : changedLocally ? "pulled" : "in-sync",
  };
};
