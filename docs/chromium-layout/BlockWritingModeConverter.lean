/-
  BlockWritingModeConverter.lean: logical <-> physical offset conversion inside a box,
  written from geometry/writing_mode_converter_test.cc. Owned by the block lane.
-/
namespace ChromiumLayout
namespace BlockWritingModeConverter

/-- `writing-mode`. CSS Writing Modes Level 4 §3.1. -/
inductive WM where
  | horizontalTb | verticalRl | verticalLr | sidewaysRl | sidewaysLr
  deriving DecidableEq, Repr

/-- `direction`. CSS Writing Modes Level 4 §2.1. -/
inductive Dir where
  | ltr | rtl
  deriving DecidableEq, Repr

/-- Vertical modes put the inline axis along y. CSS Writing Modes 4 §3.1. -/
def vertical (wm : WM) : Bool := wm != .horizontalTb

/-- Axis flip: reflect a start offset `x` of a box of size `n` inside a container of size `o`.
    CSS Writing Modes 4 §6.2 (abstract-to-physical mappings). -/
def fl (c : Bool) (o x n : Int) : Int := if c then o - x - n else x

/-- (inline flipped, block flipped), see `conv`. -/
def flips (wm : WM) (d : Dir) : Bool × Bool :=
  ((d == .rtl) != (wm == .sidewaysLr), wm == .verticalRl || wm == .sidewaysRl)

/-- Offset (inline, block) <-> (inline, block) in the other frame, before the axis swap:
    block flows right-to-left in vertical-rl/sideways-rl (§3.1); inline is reversed by rtl (§2.1)
    and by sideways-lr (text rotated counter-clockwise, §3.1). Sizes are (width, height). -/
def conv (wm : WM) (d : Dir) (outer inner o : Int × Int) : Int × Int :=
  let s := fun (p : Int × Int) => if vertical wm then (p.2, p.1) else p
  (fl (flips wm d).1 (s outer).1 o.1 (s inner).1, fl (flips wm d).2 (s outer).2 o.2 (s inner).2)

/-- Logical (inline, block) offset to physical (x, y). -/
def toPhysical (wm : WM) (d : Dir) (outer inner o : Int × Int) : Int × Int :=
  let r := conv wm d outer inner o
  if vertical wm then (r.2, r.1) else r

/-- Physical (x, y) offset to logical (inline, block). -/
def toLogical (wm : WM) (d : Dir) (outer inner p : Int × Int) : Int × Int :=
  conv wm d outer inner (if vertical wm then (p.2, p.1) else p)

/-- The flip is an involution. -/
theorem fl_fl (c : Bool) (o x n : Int) : fl c o (fl c o x n) n = x := by
  cases c <;> simp [fl] <;> omega

/-- Law: converting to physical and back is the identity for every writing mode, direction,
    size and offset (`ConvertLogicalOffsetToPhysicalOffset`,
    `ConvertPhysicalOffsetToLogicalOffset`). -/
theorem toLogical_toPhysical (wm : WM) (d : Dir) (outer inner o : Int × Int) :
    toLogical wm d outer inner (toPhysical wm d outer inner o) = o := by
  obtain ⟨i, b⟩ := o
  cases h : vertical wm <;> simp [toLogical, toPhysical, conv, h, fl_fl]

end BlockWritingModeConverter
end ChromiumLayout
