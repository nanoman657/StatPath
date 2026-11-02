// The reference for the differential test: the meaning of a generated program in unbounded Nat, which is what Bend's
// definitions say, with one refusal the runtime has: a sum past the largest immediate Nat (2^48 - 1, nat_chk). The
// evaluation is strict in arguments (the compiled call evaluates them before the call, even one the callee does not
// use) and demand-driven for lets: a let is evaluated only when a used value needs it, since Bend's guide says dropping
// an unused affine binder is free, and the compiled output drops it. A match evaluates only the arm it takes.
// It is written from the generator's shapes, not from the compiler's code.
import type { Def, Expr } from "./gen.ts";

export const LIMIT = 281474976710655n; // 2^48 - 1

export class Refuse extends Error {}

function add(a: bigint, b: bigint): bigint {
  const s = a + b;
  if (s > LIMIT) throw new Refuse("a sum past the immediate limit");
  return s;
}

function ev(defs: Def[], e: Expr, env: Map<string, () => bigint>): bigint {
  switch (e.k) {
    case "var": {
      const v = env.get(e.name);
      if (v === undefined) throw new Error(`unbound ${e.name}`);
      return v();
    }
    case "lit":
      return e.n;
    case "bin": {
      const a = ev(defs, e.a, env);
      const b = ev(defs, e.b, env);
      switch (e.op) {
        case "add": return add(a, b);
        case "sub": return a > b ? a - b : 0n;
        case "min": return a < b ? a : b;
        case "max": return a > b ? a : b;
      }
      break;
    }
    case "call": {
      const args = e.args.map((x) => ev(defs, x, env));
      return evalDef(defs, e.f, args);
    }
    case "sel": {
      const a = ev(defs, e.a, env);
      const b = ev(defs, e.b, env);
      const x = ev(defs, e.x, env);
      const y = ev(defs, e.y, env);
      if (a < b) return x;
      if (a === b) return y;
      return add(x, y);
    }
  }
  throw new Error("unreachable");
}

// the value of definition index on the arguments, or a Refuse
export function evalDef(defs: Def[], index: number, args: bigint[]): bigint {
  const d = defs[index];
  const env = new Map<string, () => bigint>();
  d.params.forEach((p, k) => env.set(p, () => args[k]));
  for (const l of d.lets) {
    let memo: bigint | undefined;
    env.set(l.name, () => (memo ??= ev(defs, l.e, env)));
  }
  if (d.body.k === "expr") return ev(defs, d.body.e, env);
  const v = env.get(d.body.param);
  if (v === undefined) throw new Error(`unbound ${d.body.param}`);
  const n = v();
  if (n === 0n) return ev(defs, d.body.zero, env);
  const q = n - 1n;
  const inner = new Map(env);
  inner.set("q", () => q);
  return add(q, ev(defs, d.body.succ, inner));
}
