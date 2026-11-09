# Anchor lane: where Chromium and the spec disagree

No disagreement between Chromium's tests and CSS Anchor Positioning 1 has been found in the rows
formalized so far. Open points (the spec was read from its source, `anchor.bs`, on GitHub):

| row | spec section | spec says | Chromium does | deviation or open question |
|---|---|---|---|---|
| anchor_evaluator_impl_test.cc:330 Transform | "Finding an Anchor" | the anchor box's position includes transforms; the axis-aligned bounding rectangle in the containing block's space is used, and updates may lag by a few frames | the anchor map holds the transformed rectangle (`(100,100,800,0)` for a `translate`) | model applies translations only (no rotation, scale); the frame delay is not modelled |
| anchor_position_scroll_data_test.cc:142, :205, :266, :392 | "Taking Scroll Into Account" | the user agent remembers the sum of the scroll offsets of the anchor's scroll-container ancestors and re-applies it when the box is laid out | the tests read the offset applied at the last scroll end, after clamping to the scroll range | `Anchor.clampScroll` models the clamp; the applied offset is an input, not derived. Open question whether Chromium's relayout-on-scroll-end matches the spec's remembered scroll offset in every case |
