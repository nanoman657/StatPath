# bend-engine: the learning-data merge, in Bend and in Lean

`src/engine/merge.ts` merges two copies of a learner's progress. This folder checks its learning-data
part: lessons, SRS cards and XP per day. Cosmetic settings, the streak (which depends on local time),
the UI and effects are out of scope.

| File | What it is |
|------|------------|
| `merge.bend` | The merge in Bend: lessons, SRS cards and XP as sorted association lists |
| `merge.mjs` | Generated from `merge.bend` by `gen.sh`; committed |
| `merge.d.mts` | The types of `merge.mjs` (written by hand; the tests check behaviour) |
| `gen.sh` | Checks `merge.bend`, then regenerates `merge.mjs` |
| `Merge.lean` | The model in Lean 4.34.0 (core only) and its laws, all proved |
| `../tests/merge_bend.test.ts` | Compiled Bend against `mergeProgress`; the laws in code; staleness; this README's rows |

## Representation

- Each map is a list of entries, strictly increasing by key (Bend's `String.cmp`), so a key appears once.
- A key in both maps is combined: lessons take the larger of each field; XP takes the larger day total;
  cards take `mergeCard(a, b)`.
- Numbers are `Nat`. An absent `lastReview` is `None`; the comparisons read it as 0, as merge.ts does with
  `?? 0`, and the output keeps it absent.
- The laws are stated for sorted inputs. The merge does not claim anything for unsorted input.

### The SRS tie-break

`mergeCard` keeps the later review, then more reps, then the later due date. On a full tie of those, it
keeps the card with the larger content. The owner chose this rule, after a finding that the earlier
tie-break was not commutative.

The cards are compared field by field, in this order: `id`, `lessonId`, `interval`, `ease`, `due`,
`lapses`, `reps`, then `lastReview` with an absent one first. The owner asked for "serialized content". JSON
strings cannot be reproduced in Bend, which has no float-to-text, so the comparison is field by field. The
order is total. merge.ts (`compareCards`), `merge.bend` (`full_cmp`) and `Merge.lean` (`fullCmp`) implement
the same one.

## Commands

    bend bend-engine/merge.bend --check-only     # the check (passes)
    bend-engine/gen.sh                            # regenerate merge.mjs
    npx vitest run tests/merge_bend.test.ts       # differential, laws in code, staleness, these rows
    export PATH=/root/.elan/toolchains/leanprover--lean4---v4.34.0/bin:$PATH
    lean bend-engine/Merge.lean                   # compiles; prints the axioms of the laws

`bend merge.bend --verdict` is not used: no Bend-level proofs were added.

## Lean theorems

Layers: **proved** means proved in `Merge.lean` for the model. **code tested** means the compiled Bend code
is checked against `mergeProgress` or against the law, in `merge_bend.test.ts`. The model is linked to the
code by a hand transcription, which is not mechanized (see below).

The test `every row points to a real theorem, function and test` checks that each row's
Lean theorem, Bend function and TypeScript function exist, and that each quoted test name is a test in
`merge_bend.test.ts`.

| Lean theorem | Bend function | TypeScript | Test | Layer |
|---|---|---|---|---|
| `lessons_comm` | `merge_lessons` | `mergeProgress` (lessons, `mergeLesson`) | "the compiled merges are commutative on random pairs, the SRS merge included"; "agrees with mergeProgress on 10,000 random pairs, with ties and missing entries" | proved; code tested |
| `lessons_idem` | `merge_lessons` | `mergeProgress(a, a)` (lessons) | "the compiled merges are idempotent: merging a copy with itself gives the copy" | proved; code tested |
| `xp_comm` | `merge_xp` | `mergeProgress` (`xpByDay`) | "the compiled merges are commutative on random pairs, the SRS merge included" | proved; code tested |
| `xp_idem` | `merge_xp` | `mergeProgress` (`xpByDay`) | "the compiled merges are idempotent: merging a copy with itself gives the copy" | proved; code tested |
| `xsum_comm` | `merge_state` (output `xp`, `xsum`) | `mergeProgress(...).xp` | "the compiled merges are commutative on random pairs, the SRS merge included" | proved; code tested |
| `cardMerge_comm` | `merge_srs` (`card_pick`, `full_cmp`) | `mergeCard`, `compareCards` | "the compiled merges are commutative on random pairs, the SRS merge included" | proved; code tested |
| `srs_comm` | `merge_srs` | `mergeProgress` (`srs`, `mergeCard`) | "the compiled merges are commutative on random pairs, the SRS merge included" | proved; code tested |
| `srs_idem` | `merge_srs` | `mergeProgress` (`srs`, `mergeCard`) | "the compiled merges are idempotent: merging a copy with itself gives the copy" | proved; code tested |
| `cardMerge_cA_cB` | `merge_srs` (`card_pick`, `full_cmp`) | `mergeCard` (tie on ease) | "the tie-break keeps the card with the larger content, in either order (ease)" | proved; code tested |
| `cardMerge_cD_cC` | `merge_srs` (`card_pick`, `full_cmp`) | `mergeCard` (absent against 0) | "the tie-break counts an absent lastReview as before any time (absent against 0)" | proved; code tested |
| `state_comm` | `merge_state` | `mergeProgress` | "the compiled merges are commutative on random pairs, the SRS merge included" | proved; code tested |

Supporting lemmas (`insC_spec`, `ins_lookup`, `fold_lookup`, `mergeMap_lookup`, `eq_of_sorted_lookup`,
`mergeMap_sorted`, `cardMerge_eq`, `cardCmp_swap`, `fullCmp_eq`) are the model's proofs. Insertion keeps a
map sorted. Two sorted maps with the same lookups are equal. The card order flips with its arguments, and a
tie is the same card. The rows above use them.

Proved axioms (printed by `lean`): `propext`, `Classical.choice`, `Quot.sound` only. No placeholder proofs.

## What is not mechanized

- **The transcription.** `Merge.lean` follows `merge.bend` by hand, function for function: `insC` is
  `lins_c`, `ins` is `lins`, `fold` is `lfold`, `fullCmp` is `full_cmp`, and so on. No tool checks that
  correspondence. The differential test checks the compiled code against `mergeProgress`, which is the
  evidence that the transcription and the code agree on the tested inputs. The rows above are therefore
  proved for the model and tested for the code; they are not linked by a proof.
- **Numbers.** The Bend code and the model use `Nat`. merge.ts uses doubles, and `ease` and `bestAccuracy`
  are not integers in general. The merge only compares and selects numbers and never computes with them, so
  the laws do not depend on the representation; the tests use integer values. This is assumed, not proved.
- **Key order.** The model uses Lean's `<` on `String`; the code uses `String.cmp`. The test
  `orders keys as JavaScript orders them, on random strings` checks them against JavaScript's string order on
  random strings. That is a test of the order, not a proof that the two agree on every string.
- **Out of scope:** the streak, the cosmetic settings, the other engine modules.

## Translation validation: `CompilerCheck.lean`

Attempted on the lesson-level maximum. The checker's readers take the JavaScript of a transition as a single
function whose name starts with `$`, with arithmetic in its return expression. The result:

- **The compiled `Nat.max`** (`return (_a_0 > _b_0 ? _a_0 : _b_0);`) is **refused** by `parseJS`. The reader's
  conditional is `a < b ? t : f` and accepts only `<`; with `>` it returns no function. A `<` control,
  `return (_a_0 < _b_0 ? _a_0 : _b_0);`, is accepted and parses to the minimum shape `cond(a, b, a, b)`.
- **A `<`-guarded maximum** `(a < b ? b : a)` is accepted by the reader, but the checker's Bend side has no
  maximum: its definitions are `var`, `add`, `sub` and `min`. So the Bend definition cannot be stated, and
  the check cannot run.
- **The lesson merge** (`lp_max`) returns a record, and the XP maximum sits inside list constructors. The SRS
  order (`card_pick`, `full_cmp`) returns a record too. The checker covers only transitions that return a
  `Nat` from `Nat` arguments, so these functions are outside its fragment whatever their guard.

Reproduced with the checker's own reader in a scratch copy of `CompilerCheck.lean`, with `#eval`s appended;
the repository's file is unchanged. The name must start with `$`: a name without it parses to no functions.
An `isSome` test on the empty list is true, so the result must be printed to tell the cases apart.

## The SRS tie-break: the finding and its resolution

The first version of `mergeCard` returned `a` on a full tie of review time, reps and due date, so
`merge(a, b)` and `merge(b, a)` could differ. `Merge.lean` proved two counterexamples at the time: cards that
differ only in ease, and a card with no review time against one with 0. The owner chose to break ties on the
whole card (see "The SRS tie-break" above). That rule is now implemented in `src/engine/merge.ts`
(commits `9372632`), `bend-engine/merge.bend` and `merge.mjs`, and `Merge.lean` (commit `87df171`). The
counterexamples became the commutativity rows above; the two examples now show the order deciding the ties.

## Assumed, and not yet done

- The Lean toolchain `lean-4.34.0` was obtained from GitHub; its checksum was not verified against a published
  value (see `browser/README.md`, "The Lean recheck").
- The staleness test fails when `bend` is not on PATH; it does not skip. It needs `bend` installed.
- `merge.d.mts` is written by hand. Generating declarations from the Bend types is not done.
- The model-to-code correspondence is a hand transcription (see "What is not mechanized").
