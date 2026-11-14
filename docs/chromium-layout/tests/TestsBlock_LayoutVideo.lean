import BlockReplaced

namespace ChromiumLayout
namespace TestsBlock

open BlockReplaced

-- layout_video_test.cc:38: PosterSizeWithNormal
-- CSS 2.1 §10.3.2, HTML Living Standard §4.8.9.
-- Video with author poster 10x10 and zoom: 1 has width 10px.
theorem PosterSizeWithNormal_vectors :
    let (w, _) := videoIntrinsicSize (.authorPoster 10 10) false 0 0
    applyZoom w 100 = 10 := by
  decide

-- layout_video_test.cc:55: PosterSizeWithZoom
-- CSS 2.1 §10.3.2, HTML Living Standard §4.8.9, CSSOM View.
-- Video with author poster 10x10 and zoom: 1.5 has width 15px.
theorem PosterSizeWithZoom_vectors :
    let (w, _) := videoIntrinsicSize (.authorPoster 10 10) false 0 0
    applyZoom w 150 = 15 := by
  decide

-- layout_video_test.cc:72: PosterSizeAfterPlay
-- CSS 2.1 §10.3.2, HTML Living Standard §4.8.9.
-- Stalled playback without video frame maintains author poster intrinsic width (10px).
theorem PosterSizeAfterPlay_vectors :
    let (w, _) := videoIntrinsicSize (.authorPoster 10 10) false 0 0
    applyZoom w 100 = 10 := by
  decide

-- layout_video_test.cc:98: DefaultPosterImageSize
-- HTML Living Standard §4.8.9.
-- Default poster image URL set via embedder settings does not affect layout; falls back to default 300px width.
theorem DefaultPosterImageSize_vectors :
    let (w, _) := videoIntrinsicSize (.defaultPoster 10 10) false 0 0
    applyZoom w 100 = 300 := by
  decide

end TestsBlock
end ChromiumLayout
