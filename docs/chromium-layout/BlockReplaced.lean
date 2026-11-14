/-
  BlockReplaced.lean: Replaced elements intrinsic sizing and zoom (CSS 2.1 §10.3.2,
  HTML Living Standard §4.8.9, CSSOM View / CSS Zoom). Owned by the block lane.
-/
namespace ChromiumLayout
namespace BlockReplaced

/-- Video poster source state. HTML Living Standard §4.8.9 The video element. -/
inductive PosterState where
  | none
  | authorPoster (w h : Nat)
  | defaultPoster (w h : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Intrinsic dimensions of a replaced video element.
    HTML Living Standard §4.8.9, CSS 2.1 §10.3.2.
    Default video dimensions are 300x150 px. Author poster provides intrinsic dimensions
    before video data loads; default poster (e.g. embedder setting) does not affect layout. -/
def videoIntrinsicSize (poster : PosterState) (hasVideoFrame : Bool) (videoW videoH : Nat) : Nat × Nat :=
  if hasVideoFrame then
    (videoW, videoH)
  else match poster with
    | .authorPoster w h => (w, h)
    | .defaultPoster _ _ | .none => (300, 150)

/-- Used size of a replaced element with zoom factor applied (as percentage: 100 for 1.0, 150 for 1.5).
    CSS 2.1 §10.3.2, CSSOM View. -/
def applyZoom (size : Nat) (zoomPct : Nat) : Nat :=
  (size * zoomPct) / 100

/-- Law: Zoom 100% is the identity on intrinsic size.
    CSSOM View. -/
theorem applyZoom_hundred (s : Nat) : applyZoom s 100 = s := by
  dsimp [applyZoom]
  omega

/-- Law: Zoom scaling is monotonic with respect to zoom factor.
    CSSOM View. -/
theorem applyZoom_monotone (s : Nat) (z1 z2 : Nat) (hz : z1 ≤ z2) :
    applyZoom s z1 ≤ applyZoom s z2 := by
  dsimp [applyZoom]
  apply Nat.div_le_div_right
  exact Nat.mul_le_mul_left s hz

/-- Law: Intrinsic dimensions with an author poster before playback equal the poster dimensions.
    HTML Living Standard §4.8.9. -/
theorem video_author_poster_dimensions (w h : Nat) :
    videoIntrinsicSize (.authorPoster w h) false 0 0 = (w, h) := by
  rfl

/-- Law: Default poster URL does not alter fallback default video dimensions (300x150).
    HTML Living Standard §4.8.9. -/
theorem video_default_poster_fallback (dw dh : Nat) :
    videoIntrinsicSize (.defaultPoster dw dh) false 0 0 = (300, 150) := by
  rfl

end BlockReplaced
end ChromiumLayout
