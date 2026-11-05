# bend-engine: the learning-data merge, in Bend and in Lean

`src/engine/merge.ts` merges two copies of a learner's progress. This folder checks its learning-data
part: lessons, SRS cards and XP per day. Cosmetic settings, the streak (which depends on local time),
the UI and effects are out of scope.

| File | What it is |
|------|------------|
| `merge.bend` | The merge in Bend: lessons, SRS cards and XP as sorted association lists |
| `merge.mjs` | Generated from `merge.bend` by `gen.sh`; committed |
| `merge.d.mts` | The types of `merge.mjs` (written by hand; the test checks behaviour) |
| `gen.sh` | Checks `merge.bend`, then regenerates `merge.mjs` |
| `Merge.lean` | The model in Lean 4.34.0 (core only) and the laws, proved or refuted |
| `../tests/merge_bend.test.ts` | Compiled Bend against `mergeProgress` on random pairs; the laws in code; staleness |

## Representation

- Each map is a list of entries, strictly increasing by key (Bend's `String.cmp`), so a key appears once.
- A key in both maps is combined: lessons take the larger of each field; XP takes the larger day total;
  cards take `mergeCard(a, b)` with the first map's card first.
- Numbers are `Nat`. An absent `lastReview` is `None`; the comparisons read it as 0, as merge.ts does with
  `?? 0`, and the output keeps it absent.
- The laws are stated for sorted inputs. The merge does not claim anything for unsorted input.

## Commands

    bend bend-engine/merge.bend --check-only     # the check (passes)
    bend-engine/gen.sh                            # regenerate merge.mjs
    npx vitest run tests/merge_bend.test.ts       # differential, laws in code, staleness
    export PATH=/root/.elan/toolchains/leanprover--lean4---v4.34.0/bin:$PATH
    lean bend-engine/Merge.lean                   # compiles; prints the axioms of the laws

`bend merge.bend --verdict` is not used: no Bend-level proofs were added.

## Lean theorems

Layers: **proved** means proved in `Merge.lean` for the model; **tested** means the compiled Bend code
is checked against the TypeScript or against the law in `merge_bend.test.ts`; **assumed** means relied
on without a check here.

| Lean theorem (`Merge.lean`) | Bend function | TypeScript | Test | Layer |
|---|---|---|---|---|
| `lessons_comm` | `merge_lessons` | `mergeProgress` (lessons, `mergeLesson`) | "compiled lesson and XP merges are commutative"; "agrees with mergeProgress" | proved; code tested |
| `lessons_idem` | `merge_lessons` | `mergeProgress(a, a)` lessons | "the compiled merges are idempotent" | proved; code tested |
| `xp_comm` | `merge_xp` | `mergeProgress` (`xpByDay`) | "compiled lesson and XP merges are commutative" | proved; code tested |
| `xp_idem` | `merge_xp` | `mergeProgress` (`xpByDay`) | "the compiled merges are idempotent" | proved; code tested |
| `xsum_comm` | `merge_state` (output `xp`, `xsum`) | `mergeProgress(...).xp` | "compiled lesson and XP merges are commutative" (the `xp` field) | proved; code tested |
| `srs_idem` | `merge_srs` | `mergeProgress` (`srs`, `mergeCard`) | "the compiled merges are idempotent" | proved; code tested |
| `srs_comm_false_ease` (counterexample) | `merge_srs` | `mergeProgress` (`srs`, `mergeCard`) | "records the finding: ... differ ... on a tie" (ease 200 vs 250) | proved (negation); code tested |
| `srs_comm_false_none` (counterexample) | `merge_srs` | `mergeProgress` (`srs`, `mergeCard`) | "records the finding: an absent lastReview against 0" | proved (negation); code tested |
| `state_comm_false` | `merge_state` (`srs` part) | `mergeProgress` | the two findings; "the SRS merge is not, and the trials show it" | proved (negation); code tested |
| `state_lessons_xp_comm` | `merge_state` (`lessons`, `xp`) | `mergeProgress` | "compiled lesson and XP merges are commutative on random pairs" | proved; code tested |

Supporting lemmas (`insC_spec`, `ins_lookup`, `fold_lookup`, `mergeMap_lookup`, `eq_of_sorted_lookup`,
`mergeMap_sorted`) are the model's proof of the algorithm: insertion keeps the map sorted, and two sorted
maps with the same lookups are equal. They have no separate test; the differential test covers them
through the laws above.

Proved axioms (printed by `lean`): `propext`, `Classical.choice`, `Quot.sound` only. No placeholder proofs.

## What the Lean model does not cover

- **The transcription.** `Merge.lean` follows `merge.bend` by hand, function for function: `insC` is
  `lins_c`, `ins` is `lins`, `fold` is `lfold`, and so on. No tool checks that correspondence. The
  differential test checks the compiled code against `mergeProgress`, which is the evidence that the
  transcription and the code agree on the tested inputs.
- **Numbers.** The Bend code and the model use `Nat`. merge.ts uses doubles, and `ease` and
  `bestAccuracy` are not integers in general. The merge only compares and selects numbers and never
  computes with them, so the laws do not depend on the representation; the tests use integer values.
  This is assumed, not proved.
- **Key order.** The model uses Lean's `<` on `String`; the code uses `String.cmp`. The test
  `orders keys as JavaScript orders them, on random strings` checks them against JavaScript's string order on random strings.
  That is a test of the order, not a proof that the two agree on every string.
- **The streak, the cosmetic settings, the other engine modules** are out of scope.

## The finding: the SRS tie-break is not commutative

`mergeCard` returns `a` on a full tie of `lastReview`, `reps` and `due`. So `merge(a, b)` and `merge(b, a)`
can differ for cards that tie and differ in another field. `Merge.lean` proves two counterexamples:

1. Two cards that tie on review time, reps and due date, and differ in ease (200 and 250). The merge keeps
   the first card, so the two orders give different cards.
2. A card with no review time against one with a review time of 0. The tie keeps the first card, and that
   card has no review time, so the two orders again give different cards.

The lessons and XP maps are commutative regardless of order. The SRS map and therefore the whole learning
state are not. merge.ts claims commutativity for all learning data, so the claim is false for these cards.

**Status: awaiting the owner.** The fix is a product decision and was not chosen here. Merge behaviour is
unchanged (`src/engine/merge.ts` is not modified). The owner's answer is recorded below when given.

## Translation validation: `CompilerCheck.lean`

Attempted on the lesson-level maximum. The checker's readers take the JavaScript of a transition as a
single function whose name starts with `$`, with arithmetic in its return expression. The result:

- **The compiled `Nat.max`** (`return (_a_0 > _b_0 ? _a_0 : _b_0);`) is **refused** by `parseJS`. The reader's
  conditional is `a < b ? t : f` and accepts only `<`; with `>` it returns no function.
- **A `<`-guarded maximum** `(a < b ? b : a)` is accepted by the reader, but the checker's Bend side has
  no maximum: its definitions are `var`, `add`, `sub` and `min`. So the Bend definition cannot be
  stated, and the check cannot run.
- **The lesson merge** (`lp_max`) returns a record, and the XP maximum sits inside list constructors.
  The checker covers only transitions that return a `Nat` from `Nat` arguments, so these functions are
  outside its fragment whatever their guard.

Reproduced with the checker's own reader in a scratch copy (`lean` on the file with
`#eval (parseJS [...]).map ...`); the repository's `CompilerCheck.lean` is unchanged. The `<` control
parses to `cond(a, b, a, b)`, the minimum shape, which is the only shape the checker accepts for a guard.

## Assumed, and not yet done

- The Lean toolchain `lean-4.34.0` was obtained from GitHub; its checksum was not verified against a
  published value (see `browser/README.md`, "The Lean recheck").
- The staleness test runs only when `bend` is installed; without it the test is skipped.
- `merge.d.mts` is written by hand. Generating declarations from the Bend types is not done.
