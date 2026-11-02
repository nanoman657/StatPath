// Random Bend programs over Nat, for the differential test of the Bend compiler (fuzz.ts). A program is a batch of
// definitions f0, f1, ...; each takes Nat parameters and returns Nat, and calls only earlier definitions, so every
// program terminates. The shapes are the ones the compiler must translate: Nat.add/sub/min/max, literals, lets,
// calls, a comparison (through sel_cmp, since Bend does not match on a computed value), and a match on a parameter.
// Bend's checker requires that a match scrutinise a parameter, and that a binder be used at most once, so the
// generator marks parameters and lets reusable (+) and uses a match's predecessor once.

export type Expr =
  | { k: "var"; name: string }
  | { k: "lit"; n: bigint }
  | { k: "bin"; op: "add" | "sub" | "min" | "max"; a: Expr; b: Expr }
  | { k: "call"; f: number; args: Expr[] }
  | { k: "sel"; a: Expr; b: Expr; x: Expr; y: Expr }; // sel_cmp(Nat.cmp(a, b), x, y)

export type Body =
  | { k: "expr"; e: Expr }
  | { k: "match"; param: string; zero: Expr; succ: Expr }; // match param: 0n -> zero; 1n+q -> Nat.add(q, succ)

export interface Def {
  index: number;
  name: string; // f<index>
  params: string[];
  lets: { name: string; e: Expr }[];
  body: Body;
}

// the largest Nat literal the source uses (Bend writes a literal past 256n through U32, up to this value)
export const BIG_LITERAL = 4294967295n;

// a seeded generator: the same seed gives the same programs
export function rng(seed: number): () => number {
  let a = seed >>> 0;
  return () => {
    a = (a + 0x6d2b79f5) >>> 0;
    let t = a;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

export interface GenOptions {
  defs: number; // definitions in the batch
  bigLiterals: boolean; // whether literals may be BIG_LITERAL (BendTT's unary numbers cannot take them)
}

export function genBatch(r: () => number, opts: GenOptions): Def[] {
  const defs: Def[] = [];
  const pick = <T>(xs: T[]): T => xs[Math.floor(r() * xs.length)];
  const int = (lo: number, hi: number) => lo + Math.floor(r() * (hi - lo + 1));

  const genExpr = (depth: number, scope: string[], callable: Def[]): Expr => {
    const leaf = (): Expr => {
      if (scope.length > 0 && r() < 0.6) return { k: "var", name: pick(scope) };
      if (opts.bigLiterals && r() < 0.05) return { k: "lit", n: BIG_LITERAL };
      return { k: "lit", n: BigInt(int(0, 20)) };
    };
    if (depth <= 0 || r() < 0.25) return leaf();
    const c = r();
    if (c < 0.4) {
      return { k: "bin", op: pick(["add", "sub", "min", "max"] as const), a: genExpr(depth - 1, scope, callable), b: genExpr(depth - 1, scope, callable) };
    }
    if (c < 0.6 && callable.length > 0) {
      const f = pick(callable);
      return { k: "call", f: f.index, args: f.params.map(() => genExpr(depth - 1, scope, callable)) };
    }
    if (c < 0.75) {
      return { k: "sel", a: genExpr(depth - 1, scope, callable), b: genExpr(depth - 1, scope, callable), x: genExpr(depth - 1, scope, callable), y: genExpr(depth - 1, scope, callable) };
    }
    return leaf();
  };

  for (let i = 0; i < opts.defs; i++) {
    const arity = int(1, 3);
    const params = Array.from({ length: arity }, (_, k) => `p${k}`);
    const callable = defs.slice();
    // a match on a parameter comes first in a body (Bend cannot match a parameter after a local statement), so a
    // match body has no lets; the predecessor q is not in scope in its arms, it is only added to
    const lets: { name: string; e: Expr }[] = [];
    const scope = params.slice();
    let body: Body;
    if (r() < 0.35) {
      body = {
        k: "match",
        param: pick(params),
        zero: genExpr(3, scope.slice(), callable),
        succ: genExpr(3, scope.slice(), callable),
      };
    } else {
      for (let l = int(0, 2); l > 0; l--) {
        const name = `v${lets.length}`;
        lets.push({ name, e: genExpr(3, scope.slice(), callable) });
        scope.push(name);
      }
      body = { k: "expr", e: genExpr(4, scope.slice(), callable) };
    }
    defs.push({ index: i, name: `f${i}`, params, lets, body });
  }
  return defs;
}

const printExpr = (e: Expr): string => {
  switch (e.k) {
    case "var": return e.name;
    case "lit": return `${e.n}n`;
    case "bin": return `Nat.${e.op}(${printExpr(e.a)}, ${printExpr(e.b)})`;
    case "call": return `f${e.f}(${e.args.map(printExpr).join(", ")})`;
    case "sel": return `sel_cmp(Nat.cmp(${printExpr(e.a)}, ${printExpr(e.b)}), ${printExpr(e.x)}, ${printExpr(e.y)})`;
  }
};

// the helper every program carries: the comparison's three cases, the sum on GT
export const HELPER = [
  "def sel_cmp(+c: Cmp, +x: Nat, +y: Nat) -> Nat:",
  "  match c:",
  "    case LT{}:",
  "      x",
  "    case EQ{}:",
  "      y",
  "    case GT{}:",
  "      Nat.add(x, y)",
  "",
].join("\n");

export function printProgram(defs: Def[]): string {
  const out: string[] = ["import Base", "", HELPER];
  for (const d of defs) {
    out.push(`def ${d.name}(${d.params.map((p) => `+${p}: Nat`).join(", ")}) -> Nat:`);
    for (const l of d.lets) out.push(`  +${l.name}: Nat = ${printExpr(l.e)}`);
    if (d.body.k === "expr") {
      out.push(`  ${printExpr(d.body.e)}`);
    } else {
      out.push(`  match ${d.body.param}:`);
      out.push("    case 0n:");
      out.push(`      ${printExpr(d.body.zero)}`);
      out.push("    case 1n+q:");
      out.push(`      Nat.add(q, ${printExpr(d.body.succ)})`);
    }
    out.push("");
  }
  return out.join("\n");
}
