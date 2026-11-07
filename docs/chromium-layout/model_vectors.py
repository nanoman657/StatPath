#!/usr/bin/env python3
"""Writes docs/chromium-layout/model_vectors.txt: the Lean model's layout results on a bounded domain
spanning M1 (signed MarginStrut), M2 (in-flow block layout), M3 (greedy line breaking), and
M4 (inline box state and line boxes).

tests/chromium_layout_bend.test.ts checks that the compiled Bend model (docs/chromium-layout/layout.mjs)
produces the exact same results on every vector.

Run from anywhere: python3 docs/chromium-layout/model_vectors.py [--out PATH]
Requires lean 4.34.0 (see LEAN_BIN below). The output is committed; the test regenerates it and compares.
"""
import argparse
import os
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
LAYOUT_TYPES_LEAN = os.path.join(HERE, "LayoutTypes.lean")
DEFAULT_OUT = os.path.join(HERE, "model_vectors.txt")
LEAN_BIN = os.environ.get("LEAN_BIN", "/root/.elan/toolchains/leanprover--lean4---v4.34.0/bin")
OLEAN_DIR = os.environ.get("OLEAN_DIR", "/root/agy-scratch/chromium-layout/olean")

GENERATOR = r'''
import LayoutTypes

section Vectors
open ChromiumLayout

def showOptNat : Option Nat → String
  | none => "-"
  | some n => toString n

def showMStrut (s : MarginStrut) : String :=
  s!"{s.pos},{s.neg}"

def strutVals : List MarginStrut :=
  [ { pos := 0, neg := 0 }
  , { pos := 10, neg := 0 }
  , { pos := 30, neg := 0 }
  , { pos := 70, neg := 0 }
  , { pos := 0, neg := 10 }
  , { pos := 0, neg := 40 }
  , { pos := 10, neg := 10 }
  , { pos := 30, neg := 10 }
  , { pos := 70, neg := 10 }
  , { pos := 10, neg := 40 }
  , { pos := 30, neg := 40 }
  , { pos := 70, neg := 40 }
  ]

-- Child catalog for M2 block layout vectors:
-- Format: kind,id,bs_pad,be_pad,bs_m,be_m,exp_h,is_bfc,csz,has_c,ist_p,ien_p
def mkChildFromCode (code : Nat) : LayoutInputNode :=
  match code with
  | 0 =>
    -- Self-collapsing empty child with margins 10..20
    .blockChild 10 {} {} { blockStart := 10, blockEnd := 20 } (some 100) none false 0 false
      MarginStrut.empty MarginStrut.empty
  | 1 =>
    -- Non-self-collapsing child with explicit height 30, margins 10..20
    .blockChild 11 {} {} { blockStart := 10, blockEnd := 20 } (some 100) (some 30) false 30 true
      MarginStrut.empty MarginStrut.empty
  | 2 =>
    -- Non-self-collapsing child with auto height (content 45), margins 25..15, inner struts 40..35 (no border/padding)
    .blockChild 12 {} {} { blockStart := 25, blockEnd := 15 } (some 100) none false 45 true
      { pos := 40, neg := 0 } { pos := 35, neg := 0 }
  | _ =>
    -- Non-self-collapsing child with border/padding (bs=3, be=5), content 40, margins 15..25, inner struts 50..50
    .blockChild 13 { blockStart := 1, blockEnd := 2 } { blockStart := 2, blockEnd := 3 }
      { blockStart := 15, blockEnd := 25 } (some 100) none false 40 true
      { pos := 50, neg := 0 } { pos := 50, neg := 0 }

def childSeqs : List (List Nat) :=
  [ []
  , [0], [1], [2], [3]
  , [0, 1], [1, 0], [1, 2], [2, 1], [2, 3], [3, 2], [0, 0], [1, 3]
  ]

def showChildCodes (cs : List Nat) : String :=
  String.intercalate "," (cs.map toString)

def showChildFragments (fs : List ChildBoxFragment) : String :=
  String.intercalate ";" (fs.map fun f => s!"{f.nodeId}:{f.offset.blockOffset}:{f.borderBoxSize.blockSize}")

-- Item catalog for M3/M4 inline layout vectors:
-- Code 0: TextSeg w=35, fh=(10,4), non-space
-- Code 1: TextSeg w=15, fh=(10,4), trailing space
-- Code 2: TextSeg w=60, fh=(14,6), non-space
-- Code 3: TextSeg w=110, fh=(12,5), non-space (overflows avail=80/100)
-- Code 4: ForcedBreak
-- Code 5: OpenTag bp=4, fh=(16,7)
-- Code 6: CloseTag bp=4
def mkItemFromCode (idx code : Nat) : InlineItem :=
  match code with
  | 0 => .TextSeg idx 35 { ascent := 10, descent := 4 } true false
  | 1 => .TextSeg idx 15 { ascent := 10, descent := 4 } true true
  | 2 => .TextSeg idx 60 { ascent := 14, descent := 6 } true false
  | 3 => .TextSeg idx 110 { ascent := 12, descent := 5 } true false
  | 4 => .ForcedBreak idx
  | 5 => .OpenTag idx 4 { ascent := 16, descent := 7 }
  | _ => .CloseTag idx 4

def buildItemsFromCodes (codes : List Nat) : List InlineItem :=
  (List.range codes.length).zipWith (fun i c => mkItemFromCode (i + 1) c) codes

def lineSeqs : List (List Nat) :=
  [ [0]
  , [1]
  , [3]
  , [4]
  , [0, 0]
  , [0, 1]
  , [0, 1, 0]
  , [0, 1, 2]
  , [0, 1, 0, 0]
  , [2, 1, 0]
  , [2, 2]
  , [3, 0]
  , [0, 3, 0]
  , [0, 4, 0]
  , [0, 1, 4, 2]
  , [5, 0, 6]
  , [0, 5, 2, 6, 0]
  , [5, 0, 1, 2, 6]
  ]

def showLines (ls : List LineInfo) : String :=
  String.intercalate ";" (ls.map fun l =>
    let ids := String.intercalate "," (l.items.map fun it => toString it.itemId)
    s!"{l.inlineSize}:{l.nonBreakItemCount}:[{ids}]")

def showPlaced (ps : List PlacedInlineItem) : String :=
  String.intercalate ";" (ps.map fun p =>
    s!"{p.itemId}:{p.inlineOffset}:{p.blockOffset}:{p.inlineSize}:{p.blockSize}")

def emit : IO Unit := do
  -- 1. M1 vectors (144 vectors)
  for a in strutVals do
    for b in strutVals do
      let ab := MarginStrut.append a b
      let applied := MarginStrut.applyOffset 100 ab
      IO.println s!"V|M|{showMStrut a}|{showMStrut b}|{ab.pos},{ab.neg},{ab.sum},{applied}"

  -- 2. M2 block layout vectors (2 * 2 * 2 * 2 * 2 * 13 = 416 vectors)
  for padStart in [0, 4] do
    for padEnd in [0, 6] do
      for isBfc in [false, true] do
        for expH in ([none, some 120] : List (Option Nat)) do
          for spacePos in [0, 15] do
            for seq in childSeqs do
              let cs := seq.map mkChildFromCode
              let space : ConstraintSpace :=
                { availableInlineSize := 200
                , bfcBlockOffset := 10
                , marginStrut := { pos := spacePos, neg := 0 }
                , isNewBfc := false }
              let node : BlockContainerNode :=
                { nodeId := 1
                , padding := { blockStart := padStart, blockEnd := padEnd }
                , explicitInlineSize := some 100
                , explicitBlockSize := expH
                , isNewBfc := isBfc
                , children := cs }
              let res := layoutBlock space node
              let flow := totalCollapsedFlowBlockSize cs
              let bfcStr := if isBfc then "1" else "0"
              let inSpec := s!"{padStart},{padEnd},{bfcStr},{showOptNat expH},{spacePos}:{showChildCodes seq}"
              let outSpec := s!"{showOptNat res.bfcBlockOffset},{res.intrinsicBlockSize},{res.fragment.borderBoxSize.blockSize},{res.endMarginStrut.pos},{res.endMarginStrut.neg},{flow}|{showChildFragments res.fragment.children}"
              IO.println s!"V|B|{inSpec}|{outSpec}"

  -- 3. M3 line breaking vectors (3 * 18 = 54 vectors)
  for avail in [50, 80, 100] do
    for seq in lineSeqs do
      let items := buildItemsFromCodes seq
      let lines := breakLines avail items
      IO.println s!"V|L|{avail}|{showChildCodes seq}|{showLines lines}"

  -- 4. M4 inline box state and line box vectors (2 * 18 = 36 vectors)
  for strut in ([{ ascent := 10, descent := 4 }, { ascent := 15, descent := 6 }] : List FontHeight) do
    for seq in lineSeqs do
      let items := buildItemsFromCodes seq
      let li : LineInfo := { items := items, inlineSize := 80, nonBreakItemCount := items.length }
      let lb := createLineBox strut li
      let stMetrics := applyBoxStateStack strut items
      let (stacked, totalBs) := stackLineBoxes strut 5 (breakLines 80 items)
      let stackedSpec := String.intercalate "," (stacked.map fun lf => s!"{lf.bfcOffset.blockOffset}:{lf.metrics.lineHeight}")
      IO.println s!"V|I|{strut.ascent},{strut.descent}|{showChildCodes seq}|{lb.metrics.ascent},{lb.metrics.descent},{stMetrics.ascent},{stMetrics.descent},{totalBs}|[{stackedSpec}]|{showPlaced lb.items}"

#eval emit
end Vectors
'''


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default=DEFAULT_OUT)
    args = ap.parse_args()
    os.makedirs(OLEAN_DIR, exist_ok=True)
    olean_path = os.path.join(OLEAN_DIR, "LayoutTypes.olean")
    env = dict(
        os.environ,
        PATH=LEAN_BIN + os.pathsep + os.environ.get("PATH", ""),
        LEAN_PATH=OLEAN_DIR,
    )
    if not os.path.exists(olean_path) or os.path.getmtime(olean_path) < os.path.getmtime(LAYOUT_TYPES_LEAN):
        comp = subprocess.run(
            ["lean", "-j", "1", "-o", olean_path, LAYOUT_TYPES_LEAN],
            capture_output=True,
            text=True,
            env=env,
            timeout=900,
        )
        if comp.returncode != 0:
            sys.stderr.write(comp.stdout + comp.stderr)
            return comp.returncode
    tmp = tempfile.mkdtemp(prefix="cl-mv-")
    try:
        src = os.path.join(tmp, "Vectors.lean")
        with open(src, "w") as f:
            f.write(GENERATOR)
        run = subprocess.run(["lean", "-j", "1", src], capture_output=True, text=True, env=env, timeout=900)
        if run.returncode != 0:
            sys.stderr.write(run.stdout + run.stderr)
            return run.returncode
        rows = [l for l in run.stdout.split("\n") if l.startswith("V|")]
        if not rows:
            sys.stderr.write("the model produced no vectors\n")
            return 1
        with open(args.out, "w") as f:
            f.write("# Generated by docs/chromium-layout/model_vectors.py from LayoutTypes.lean. Do not edit by hand.\n")
            f.write("# Kinds: M (MarginStrut), B (layoutBlock & flow), L (breakLines), I (createLineBox & applyBoxStateStack)\n")
            f.write("\n".join(rows) + "\n")
        print(f"{len(rows)} vectors written to {args.out}")
        return 0
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


if __name__ == "__main__":
    sys.exit(main())
