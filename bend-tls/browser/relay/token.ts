// Makes a token for a user of the relay (RELAY.md). The token is shown once: give it to the user,
// and put only its SHA-256 digest in the relay's configuration.
//
//   bun relay/token.ts <name>

import { randomBytes, createHash } from "node:crypto";

export function newToken(): string {
  return randomBytes(32).toString("base64url");
}

export function digestOf(token: string): string {
  return createHash("sha256").update(token).digest("hex");
}

if (import.meta.main) {
  const name = process.argv[2];
  if (!name || !/^[A-Za-z0-9._-]{1,64}$/.test(name)) {
    console.error("usage: bun relay/token.ts <name>   (a name of 1 to 64 letters, digits, '.', '_' or '-')");
    process.exit(2);
  }
  const token = newToken();
  console.log(`token (give this to ${name} once, and keep it secret): ${token}`);
  console.log(`config entry (put this in the relay's tokens list): ${JSON.stringify({ name, sha256: digestOf(token) })}`);
}
