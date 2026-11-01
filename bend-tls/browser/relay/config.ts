// The relay's configuration (RELAY.md): where it listens, who may use it, which origins may reach
// it, what it may connect to, and the limits it keeps. loadConfig checks every field and throws a
// ConfigError that names what is wrong, so a relay does not start with a setting it did not read.

import { existsSync } from "node:fs";

export type Allow = { host: string; ports: number[] };
export type Token = { name: string; sha256: string };
export type Limits = {
  maxConnections: number;       // open connections per WebSocket
  maxConnectionsTotal: number;  // open connections in the whole relay
  maxSessions: number;          // WebSockets open at once
  upgradesPerMinute: number;    // WebSocket upgrades from one client address, per minute
  connectsPerSecond: number;    // CONNECTs per WebSocket, per second (a burst of twice that)
  bytesPerSecond: number;       // bytes per WebSocket, per second, both ways together
  authSeconds: number;          // time allowed for AUTH after the WebSocket opens
  idleSeconds: number;          // a WebSocket with no frames or pings for this long is closed (at most 255)
  maxBufferedBytes: number;     // a WebSocket's send buffer past this stops reading its connections
};
export type Config = {
  host: string;
  port: number;
  tls: { cert: string; key: string } | null;  // file paths; with TLS the relay serves wss://
  origins: string[];                          // the Origin values that may connect, exactly
  tokens: Token[];                            // who may use the relay: the SHA-256 of each token
  allow: Allow[];                             // where the relay may connect (default-deny)
  limits: Limits;
};

export class ConfigError extends Error {
  constructor(problems: string[]) {
    super("relay configuration: " + problems.join("; "));
    this.name = "ConfigError";
  }
}

export const DEFAULT_LIMITS: Limits = {
  maxConnections: 64,
  maxConnectionsTotal: 1024,
  maxSessions: 256,
  upgradesPerMinute: 60,
  connectsPerSecond: 20,
  bytesPerSecond: 16 * 1024 * 1024,
  authSeconds: 10,
  idleSeconds: 120,
  maxBufferedBytes: 1024 * 1024,
};

// the digest the example config carries: loading it is refused until a real token replaces it
export const PLACEHOLDER_DIGEST = "0".repeat(64);

export function isLoopback(host: string): boolean {
  return host === "127.0.0.1" || host === "::1" || host === "localhost";
}

const TOP = ["host", "port", "tls", "origins", "tokens", "allow", "limits"];
const LIMITS = Object.keys(DEFAULT_LIMITS);

const isObject = (v: unknown): v is Record<string, unknown> =>
  typeof v === "object" && v !== null && !Array.isArray(v);

// loadConfig checks a parsed config. It throws a ConfigError listing every problem it finds.
export function loadConfig(raw: unknown): Config {
  const problems: string[] = [];
  if (!isObject(raw)) throw new ConfigError(["the configuration must be a JSON object"]);
  for (const k of Object.keys(raw)) if (!TOP.includes(k)) problems.push(`unknown setting "${k}"`);

  const host = raw.host ?? "127.0.0.1";
  if (typeof host !== "string" || host.length === 0) problems.push("host must be a non-empty string");

  const port = raw.port;
  if (!Number.isInteger(port) || (port as number) < 0 || (port as number) > 65535) {
    problems.push("port must be an integer from 0 to 65535");
  }

  let tls: Config["tls"] = null;
  if (raw.tls !== undefined) {
    const t = raw.tls;
    if (!isObject(t) || typeof t.cert !== "string" || typeof t.key !== "string" || !t.cert || !t.key) {
      problems.push("tls must be { cert, key }, two file paths");
    } else {
      for (const f of [t.cert, t.key]) if (!existsSync(f)) problems.push(`tls file not found: ${f}`);
      tls = { cert: t.cert, key: t.key };
    }
  }
  if (typeof host === "string" && !isLoopback(host) && tls === null) {
    problems.push(`host ${host} is not this machine: a relay that listens beyond it needs tls`);
  }

  const origins = raw.origins;
  if (!Array.isArray(origins) || origins.length === 0) {
    problems.push("origins must list the pages that may use the relay, e.g. [\"https://page.example\"]");
  } else {
    for (const o of origins) {
      let ok = false;
      if (typeof o === "string") {
        try {
          const u = new URL(o);
          ok = (u.protocol === "https:" || u.protocol === "http:") && u.origin === o;
        } catch {
          ok = false;
        }
      }
      if (!ok) problems.push(`origin ${JSON.stringify(o)} must be exactly scheme://host[:port], e.g. https://page.example`);
    }
  }

  const tokens = raw.tokens;
  const tokenList: Token[] = [];
  if (!Array.isArray(tokens) || tokens.length === 0) {
    problems.push("tokens must list who may use the relay (make one with relay/token.ts)");
  } else {
    for (const t of tokens) {
      if (!isObject(t) || typeof t.name !== "string" || !/^[A-Za-z0-9._-]{1,64}$/.test(t.name)) {
        problems.push("each token needs a name of 1 to 64 letters, digits, '.', '_' or '-'");
      } else if (typeof t.sha256 !== "string" || !/^[0-9a-f]{64}$/.test(t.sha256)) {
        problems.push(`token ${t.name}: sha256 must be 64 lowercase hex digits`);
      } else if (t.sha256 === PLACEHOLDER_DIGEST) {
        problems.push(`token ${t.name}: the example digest is a placeholder; make a token with relay/token.ts`);
      } else {
        tokenList.push({ name: t.name, sha256: t.sha256 });
      }
    }
  }

  const allow = raw.allow;
  const allowList: Allow[] = [];
  if (!Array.isArray(allow) || allow.length === 0) {
    problems.push("allow must list at least one destination (the relay connects to nothing else)");
  } else {
    for (const a of allow) {
      if (!isObject(a) || typeof a.host !== "string" || a.host.length === 0 || a.host.length > 255) {
        problems.push("each allow entry needs a host name of 1 to 255 characters");
        continue;
      }
      const ports = a.ports;
      if (!Array.isArray(ports) || ports.length === 0
        || !ports.every((p) => Number.isInteger(p) && p >= 1 && p <= 65535)) {
        problems.push(`allow ${a.host}: ports must be a non-empty list of integers from 1 to 65535`);
        continue;
      }
      allowList.push({ host: a.host, ports: ports as number[] });
    }
  }

  const limits: Limits = { ...DEFAULT_LIMITS };
  if (raw.limits !== undefined) {
    if (!isObject(raw.limits)) {
      problems.push("limits must be an object");
    } else {
      for (const [k, v] of Object.entries(raw.limits)) {
        if (!LIMITS.includes(k)) {
          problems.push(`unknown limit "${k}"`);
        } else if (!Number.isInteger(v) || (v as number) < 1 || (v as number) > 2 ** 31 - 1) {
          problems.push(`limit ${k} must be a whole number from 1 up`);
        } else {
          (limits as Record<string, number>)[k] = v as number;
        }
      }
    }
  }
  if (limits.idleSeconds > 255) problems.push("limit idleSeconds must be at most 255");

  if (problems.length > 0) throw new ConfigError(problems);
  return {
    host: host as string,
    port: port as number,
    tls,
    origins: origins as string[],
    tokens: tokenList,
    allow: allowList,
    limits,
  };
}

// the configuration in a JSON file
export async function readConfig(path: string): Promise<Config> {
  let raw: unknown;
  try {
    raw = JSON.parse(await Bun.file(path).text());
  } catch (e) {
    throw new ConfigError([`${path} is not readable JSON (${(e as Error).message})`]);
  }
  return loadConfig(raw);
}
