import BlockRelative

namespace TestsBlock

open ChromiumLayout.BlockRelative

def kLeft : Int := 3
def kRight : Int := 5
def kTop : Int := 7
def kBottom : Int := 9

-- relative_utils_test.cc:49: HorizontalTB
theorem HorizontalTB_vectors :
    computeRelativeInsets none none none none = ⟨0, 0, 0, 0⟩ ∧
    computeRelativeInsets (some kTop) (some kRight) (some kBottom) (some kLeft) =
      ⟨kTop, kRight, kBottom, kLeft⟩ ∧
    computeRelativeInsets none (some kRight) (some kBottom) none =
      ⟨-kBottom, kRight, kBottom, -kRight⟩ ∧
    computeRelativeInsets (some kTop) none none (some kLeft) =
      ⟨kTop, -kLeft, -kTop, kLeft⟩ := by
  decide

end TestsBlock
