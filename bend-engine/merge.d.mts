// The types of merge.mjs, which bend-engine/gen.sh generates from merge.bend. The module exports the
// Bend functions as they are; tests/merge_bend.test.ts checks them against mergeProgress.
export interface BendMerge {
  /** The learning data of two copies: lessons, SRS cards and XP per day, merged (see merge.bend). */
  merge_state(a: unknown, b: unknown): unknown;
  /** The order of two keys, as String.cmp gives it: { $: "LT" | "EQ" | "GT" }. */
  skey_cmp(a: string, b: string): unknown;
}
declare const bend: BendMerge;
export default bend;
