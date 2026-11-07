import { describe, expect, it } from "vitest";
import { execFileSync } from "node:child_process";
import { mkdtempSync, readFileSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import layout from "../docs/chromium-layout/layout.mjs";

// Differential conformance and translation-validation tests for the Chromium Blink LayoutNG
// formalization (docs/chromium-layout/layout.bend, compiled to docs/chromium-layout/layout.mjs)
// against the Lean 4 model (docs/chromium-layout/LayoutTypes.lean, LayoutBlock.lean, LayoutInline.lean,
// Layout.lean) and the extended translation-validation checker (docs/chromium-layout/CompilerCheck.lean).

const ROOT = join(__dirname, "..", "docs", "chromium-layout");
const BEND_BIN = process.env.BEND_BIN ?? "/root/.bend/bin/bend";

const list = (xs: unknown[]): any =>
  xs.reduceRight<any>((tail, head) => ({ $: "Con", head, tail }), { $: "Nil" });

const unList = (l: any): any[] => {
  const xs: any[] = [];
  for (let x = l; x && x.$ === "Con"; x = x.tail) xs.push(x.head);
  return xs;
};

const strut = (inline_start = 0, inline_end = 0, block_start = 0, block_end = 0) => ({
  $: "Strut",
  inline_start,
  inline_end,
  block_start,
  block_end,
});

const mstrut = (pos = 0, neg = 0) => ({ $: "MStrut", pos, neg });
const fheight = (ascent = 0, descent = 0) => ({ $: "FHeight", ascent, descent });
const someNat = (val: number) => ({ $: "SomeNat", val });
const noneNat = () => ({ $: "NoneNat" });
const maybeNat = (v: number | null | undefined) => (v === null || v === undefined ? noneNat() : someNat(v));
const showMaybeNat = (m: any): string => (m.$ === "NoneNat" ? "-" : String(m.val));

// Child catalog matching docs/chromium-layout/model_vectors.py `mkChildFromCode`
function mkChildFromCode(code: number): any {
  if (code === 0) {
    return {
      $: "BlockChild",
      node_id: 10,
      border: strut(),
      padding: strut(),
      margin: strut(0, 0, 10, 20),
      explicit_inline_size: someNat(100),
      explicit_block_size: noneNat(),
      is_new_bfc: false,
      content_block_size: 0,
      has_inflow_content: false,
      inner_start_strut: mstrut(0, 0),
      inner_end_strut: mstrut(0, 0),
    };
  }
  if (code === 1) {
    return {
      $: "BlockChild",
      node_id: 11,
      border: strut(),
      padding: strut(),
      margin: strut(0, 0, 10, 20),
      explicit_inline_size: someNat(100),
      explicit_block_size: someNat(30),
      is_new_bfc: false,
      content_block_size: 30,
      has_inflow_content: true,
      inner_start_strut: mstrut(0, 0),
      inner_end_strut: mstrut(0, 0),
    };
  }
  if (code === 2) {
    return {
      $: "BlockChild",
      node_id: 12,
      border: strut(),
      padding: strut(),
      margin: strut(0, 0, 25, 15),
      explicit_inline_size: someNat(100),
      explicit_block_size: noneNat(),
      is_new_bfc: false,
      content_block_size: 45,
      has_inflow_content: true,
      inner_start_strut: mstrut(40, 0),
      inner_end_strut: mstrut(35, 0),
    };
  }
  return {
    $: "BlockChild",
    node_id: 13,
    border: strut(0, 0, 1, 2),
    padding: strut(0, 0, 2, 3),
    margin: strut(0, 0, 15, 25),
    explicit_inline_size: someNat(100),
    explicit_block_size: noneNat(),
    is_new_bfc: false,
    content_block_size: 40,
    has_inflow_content: true,
    inner_start_strut: mstrut(50, 0),
    inner_end_strut: mstrut(50, 0),
  };
}

// InlineItem catalog matching docs/chromium-layout/model_vectors.py `mkItemFromCode`
function mkItemFromCode(idx: number, code: number): any {
  if (code === 0) {
    return {
      $: "TextSeg",
      item_id: idx,
      inline_size: 35,
      font_height: fheight(10, 4),
      can_break_after: true,
      is_trailing_space: false,
    };
  }
  if (code === 1) {
    return {
      $: "TextSeg",
      item_id: idx,
      inline_size: 15,
      font_height: fheight(10, 4),
      can_break_after: true,
      is_trailing_space: true,
    };
  }
  if (code === 2) {
    return {
      $: "TextSeg",
      item_id: idx,
      inline_size: 60,
      font_height: fheight(14, 6),
      can_break_after: true,
      is_trailing_space: false,
    };
  }
  if (code === 3) {
    return {
      $: "TextSeg",
      item_id: idx,
      inline_size: 110,
      font_height: fheight(12, 5),
      can_break_after: true,
      is_trailing_space: false,
    };
  }
  if (code === 4) {
    return {
      $: "ForcedBreak",
      item_id: idx,
    };
  }
  if (code === 5) {
    return {
      $: "OpenTag",
      item_id: idx,
      border_inline_start: 4,
      padding_inline_start: 0,
      margin_inline_start: 0,
      font_height: fheight(16, 7),
    };
  }
  return {
    $: "CloseTag",
    item_id: idx,
    border_inline_end: 4,
    padding_inline_end: 0,
    margin_inline_end: 0,
  };
}

function buildItemsFromCodes(codes: number[]): any {
  return list(codes.map((c, i) => mkItemFromCode(i + 1, c)));
}

describe("the compiled Bend layout model against the Lean model on all bounded vectors", () => {
  const VECTORS = join(ROOT, "model_vectors.txt");

  it("agrees with the Lean model on all 650 M1, M2, M3, and M4 vectors", () => {
    const rows = readFileSync(VECTORS, "utf8")
      .split("\n")
      .filter((l) => l.startsWith("V|"));
    expect(rows.length).toBe(650);
    const mismatches: string[] = [];

    for (const row of rows) {
      const parts = row.split("|");
      const kind = parts[1];

      if (kind === "M") {
        const [ap, an] = parts[2].split(",").map(Number);
        const [bp, bn] = parts[3].split(",").map(Number);
        const want = parts[4];
        const a = mstrut(ap, an);
        const b = mstrut(bp, bn);
        const ab = layout.margin_strut_append(a, b);
        const sum = layout.margin_strut_sum(ab);
        const applied = layout.margin_strut_apply_offset(100, ab);
        const got = `${ab.pos},${ab.neg},${sum},${applied}`;
        if (got !== want) mismatches.push(`${row}\n  got: ${got}`);
      } else if (kind === "B") {
        const [hdr, seqStr] = parts[2].split(":");
        const [padStartStr, padEndStr, bfcStr, expHStr, spacePosStr] = hdr.split(",");
        const want = `${parts[3]}|${parts[4]}`;
        const codes = seqStr === "" ? [] : seqStr.split(",").map(Number);
        const cs = list(codes.map(mkChildFromCode));
        const space = {
          $: "CSpace",
          available_inline_size: 200,
          available_block_size: noneNat(),
          bfc_line_offset: 0,
          bfc_block_offset: 10,
          margin_strut: mstrut(+spacePosStr, 0),
          is_new_bfc: false,
        };
        const node = {
          $: "BlockContainer",
          node_id: 1,
          border: strut(),
          padding: strut(0, 0, +padStartStr, +padEndStr),
          margin: strut(),
          explicit_inline_size: someNat(100),
          explicit_block_size: expHStr === "-" ? noneNat() : someNat(+expHStr),
          is_new_bfc: bfcStr === "1",
          children: cs,
        };
        const res = layout.layout_block(space, node);
        const flow = layout.total_collapsed_flow_block_size(100, cs);
        const frags = unList(res.fragment.children)
          .map((f: any) => `${f.node_id}:${f.offset.block_offset}:${f.border_box_size.block_size}`)
          .join(";");
        const got = `${showMaybeNat(res.bfc_block_offset)},${res.intrinsic_block_size},${res.fragment.border_box_size.block_size},${res.end_margin_strut.pos},${res.end_margin_strut.neg},${flow}|${frags}`;
        if (got !== want) mismatches.push(`${row}\n  got: ${got}`);
      } else if (kind === "L") {
        const avail = +parts[2];
        const codes = parts[3].split(",").map(Number);
        const want = parts[4];
        const items = buildItemsFromCodes(codes);
        const lines = unList(layout.break_lines(avail, items));
        const got = lines
          .map((l: any) => {
            const ids = unList(l.items)
              .map((it: any) => String(layout.inline_item_id(it)))
              .join(",");
            return `${l.inline_size}:${l.non_break_item_count}:[${ids}]`;
          })
          .join(";");
        if (got !== want) mismatches.push(`${row}\n  got: ${got}`);
      } else if (kind === "I") {
        const [sa, sd] = parts[2].split(",").map(Number);
        const codes = parts[3].split(",").map(Number);
        const want = `${parts[4]}|${parts[5]}|${parts[6]}`;
        const st = fheight(sa, sd);
        const items = buildItemsFromCodes(codes);
        const li = { $: "LInfo", items, inline_size: 80, non_break_item_count: codes.length };
        const lb = layout.create_line_box(st, li);
        const stMetrics = layout.apply_box_state_stack(st, items);
        const stackedRes = layout.stack_line_boxes(layout.break_lines(80, items), st, 5);
        const stackedSpec = unList(stackedRes.lines)
          .map((lf: any) => `${lf.bfc_offset.block_offset}:${layout.font_height_line_height(lf.metrics)}`)
          .join(",");
        const placedSpec = unList(lb.items)
          .map((p: any) => `${p.item_id}:${p.inline_offset}:${p.block_offset}:${p.inline_size}:${p.block_size}`)
          .join(";");
        const got = `${lb.metrics.ascent},${lb.metrics.descent},${stMetrics.ascent},${stMetrics.descent},${stackedRes.total_block_size}|[${stackedSpec}]|${placedSpec}`;
        if (got !== want) mismatches.push(`${row}\n  got: ${got}`);
      }
    }

    expect(mismatches.slice(0, 3)).toEqual([]);
  });

  it("model_vectors.txt is the output of model_vectors.py from LayoutTypes.lean", () => {
    const dir = mkdtempSync(join(tmpdir(), "cl-vectors-"));
    try {
      const out = join(dir, "vectors.txt");
      execFileSync("python3", [join(ROOT, "model_vectors.py"), "--out", out], {
        stdio: "pipe",
        timeout: 600_000,
      });
      expect(readFileSync(out, "utf8")).toBe(readFileSync(VECTORS, "utf8"));
    } finally {
      rmSync(dir, { recursive: true, force: true });
    }
  }, 700_000);
});

describe("transcribed Chromium blink_unittests vectors on the compiled Bend model", () => {
  it("passes M1 box_strut_test.cc and margin_strut_test.cc vectors", () => {
    const s1 = strut(10, 20, 30, 40);
    const s2 = strut(1, 2, 3, 4);
    expect(layout.box_strut_inline_sum(s1)).toBe(30);
    expect(layout.box_strut_block_sum(s1)).toBe(70);
    expect(layout.box_strut_add(s1, s2)).toEqual(strut(11, 22, 33, 44));

    const m1 = layout.margin_strut_append(mstrut(20, 0), mstrut(30, 15));
    expect(m1).toEqual(mstrut(30, 15));
    expect(layout.margin_strut_sum(m1)).toBe(15);
    expect(layout.margin_strut_apply_offset(100, mstrut(10, 25))).toBe(85);
  });

  it("passes M2 block_layout_algorithm_test.cc vectors (siblings, self-collapsing, parent-child collapsing)", () => {
    // CollapsingWithSibling: two children with height 20 and margins (10..20) and (30..40)
    const c1 = {
      $: "BlockChild",
      node_id: 1,
      border: strut(),
      padding: strut(),
      margin: strut(0, 0, 10, 20),
      explicit_inline_size: someNat(100),
      explicit_block_size: someNat(20),
      is_new_bfc: false,
      content_block_size: 20,
      has_inflow_content: true,
      inner_start_strut: mstrut(),
      inner_end_strut: mstrut(),
    };
    const c2 = {
      ...c1,
      node_id: 2,
      margin: strut(0, 0, 30, 40),
    };
    const space = {
      $: "CSpace",
      available_inline_size: 200,
      available_block_size: noneNat(),
      bfc_line_offset: 0,
      bfc_block_offset: 0,
      margin_strut: mstrut(),
      is_new_bfc: false,
    };
    const node = {
      $: "BlockContainer",
      node_id: 100,
      border: strut(),
      padding: strut(),
      margin: strut(),
      explicit_inline_size: someNat(100),
      explicit_block_size: noneNat(),
      is_new_bfc: true,
      children: list([c1, c2]),
    };
    const res = layout.layout_block(space, node);
    const frags = unList(res.fragment.children);
    expect(frags[0].offset.block_offset).toBe(10);
    expect(frags[1].offset.block_offset).toBe(60);
    expect(res.intrinsic_block_size).toBe(120);
  });

  it("passes M3 and M4 inline_layout_algorithm_test.cc vectors (breaking, trailing space hang, box state)", () => {
    const it1 = mkItemFromCode(1, 0); // w=35, fh=(10,4)
    const it2 = mkItemFromCode(2, 1); // w=15, trailing space
    const it3 = mkItemFromCode(3, 2); // w=60, fh=(14,6)
    const lines = unList(layout.break_lines(80, list([it1, it2, it3])));
    expect(lines.length).toBe(2);
    expect(lines[0].inline_size).toBe(35);
    expect(lines[1].inline_size).toBe(60);

    const open = mkItemFromCode(1, 5); // OpenTag fh=(16,7)
    const close = mkItemFromCode(3, 6);
    const spanItems = list([open, it1, close]);
    const lb = layout.create_line_box(fheight(10, 4), {
      $: "LInfo",
      items: spanItems,
      inline_size: 43,
      non_break_item_count: 3,
    });
    expect(lb.metrics).toEqual(fheight(16, 7));
    expect(layout.apply_box_state_stack(fheight(10, 4), spanItems)).toEqual(fheight(16, 7));
  });
});

const bendInstalled = (() => {
  try {
    execFileSync(BEND_BIN, ["version"], { stdio: "ignore" });
    return true;
  } catch {
    return false;
  }
})();

describe("the generated layout.mjs module and Bend proofs", () => {
  it("is the output of the current layout.bend (regenerate with docs/chromium-layout/gen.sh)", () => {
    if (!bendInstalled) throw new Error("bend is not installed: install it to check that layout.mjs is current");
    const dir = mkdtempSync(join(tmpdir(), "layout-bend-"));
    try {
      const out = join(dir, "layout.mjs");
      execFileSync(BEND_BIN, [join(ROOT, "layout.bend"), "-o", out], { stdio: "ignore", timeout: 120_000 });
      expect(readFileSync(out, "utf8")).toBe(readFileSync(join(ROOT, "layout.mjs"), "utf8"));
    } finally {
      rmSync(dir, { recursive: true, force: true });
    }
  }, 150_000);

  it("compiler_check_report.txt is the output of compiler_check.py and validates Nat.max and records", () => {
    const dir = mkdtempSync(join(tmpdir(), "cl-compiler-check-"));
    try {
      const out = join(dir, "report.txt");
      execFileSync("python3", [join(ROOT, "compiler_check.py"), "--out", out], {
        stdio: "pipe",
        timeout: 600_000,
      });
      const text = readFileSync(out, "utf8");
      expect(text).toBe(readFileSync(join(ROOT, "compiler_check_report.txt"), "utf8"));
      expect(text).toContain("extractedMJS == layoutJSText: true");
      expect(text).toContain("parseRecJS extractedMJS == some layoutJSRecAST: true");
      expect(text).toContain("checkAllRec layoutBendRecDefs layoutJSRecAST: true");
      expect(text).toContain("fn lp_max: checkRecFn = true");
    } finally {
      rmSync(dir, { recursive: true, force: true });
    }
  }, 700_000);

  it("Phase 6 transcription audit table and WPT layout geometry check pass", () => {
    const auditOut = execFileSync("python3", [join(ROOT, "verify_transcription.py")], {
      encoding: "utf8",
      timeout: 30_000,
    });
    expect(auditOut).toContain("OK: 36 transcription audit rows verified");

    const wptOut = execFileSync(process.execPath, [join(ROOT, "wpt_geometry_check.cjs")], {
      encoding: "utf8",
      timeout: 60_000,
    });
    expect(wptOut).toContain("OK: WPT layout geometry check passed");
  }, 90_000);

  it("every row of docs/chromium-layout/README.md points to real Lean theorems, Bend theorems, and JS functions", () => {
    const readme = readFileSync(join(ROOT, "README.md"), "utf8");
    const leanAll = [
      readFileSync(join(ROOT, "LayoutTypes.lean"), "utf8"),
      readFileSync(join(ROOT, "LayoutBlock.lean"), "utf8"),
      readFileSync(join(ROOT, "LayoutInline.lean"), "utf8"),
      readFileSync(join(ROOT, "Layout.lean"), "utf8"),
    ].join("\n");
    const proofBend = readFileSync(join(ROOT, "proof.bend"), "utf8");
    const lawsTable = readme.slice(
      readme.indexOf("## Mechanized Laws"),
      readme.indexOf("## Assumptions Register"),
    );
    const rows = lawsTable.split("\n").filter((l) => l.startsWith("| **Law"));
    expect(rows.length).toBe(5);
    const ids = (cell: string): string[] =>
      [...cell.matchAll(/`([A-Za-z0-9_]+)`/g)].map((m) => m[1]);
    for (const row of rows) {
      const [, leanCell, bendCell, jsCell] = row.split("|").slice(1, -1).map((c) => c.trim());
      for (const thm of ids(leanCell)) {
        expect(leanAll, `Lean theorem ${thm}`).toMatch(new RegExp(`theorem\\s+${thm}\\b`));
      }
      for (const bthm of ids(bendCell)) {
        expect(proofBend, `Bend theorem ${bthm}`).toMatch(new RegExp(`law\\s+${bthm}\\b`));
      }
      for (const fn of ids(jsCell)) {
        expect(typeof (layout as Record<string, unknown>)[fn], `layout.mjs export ${fn}`).toBe("function");
      }
    }
    expect(readme).toContain("kLayoutUnitMax");
    expect(readme).toContain("kBendNatImmediateMax");
    expect(readme).toContain("Subpixel rounding & physical pixel snapping");
    expect(readme).toContain("Caching & incremental layout");
  });
});
