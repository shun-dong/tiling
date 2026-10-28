import Tiling.Combinatorics.Quadrangulation
import Mathlib.Tactic.LinearCombination

/-!
# Edge-path parity and orientation transport

A flag path traverses a side, changes sides at a corner, or crosses a gluing at the
same endpoint. Only traversing a side counts toward edge-path length; only crossing
a gluing changes the local square orientation. Distinct occurrences remain distinct,
even for loops and repeated vertices. This is a combinatorial path model, without
asserting a bridge to a topological realization or a characteristic class.
-/

namespace Tiling

variable {Vertex Face : Type*}

/-- Traverse the side from one endpoint occurrence to the other. -/
def sideFlip (x : Flag Face) : Flag Face := (x.1, !x.2)

theorem localColor_sideFlip (x : Flag Face) :
    localColor (sideFlip x) = localColor x + 1 := by
  rcases x with ⟨d, b⟩
  cases b <;> simp [sideFlip, localColor, add_assoc,
    show (1 + 1 : ZMod 2) = 0 by decide]

namespace QuadGluing

variable (Q : QuadGluing Vertex Face)

/-- An edge path with its intervening choices of corner and gluing occurrences. -/
inductive FlagPath : Flag Face → Flag Face → Type _
  | nil (x : Flag Face) : FlagPath x x
  | corner {x y : Flag Face} : FlagPath (cornerSwap x) y → FlagPath x y
  | across {x y : Flag Face} : FlagPath (Q.edgeSwap x) y → FlagPath x y
  | along {x y : Flag Face} : FlagPath (sideFlip x) y → FlagPath x y

namespace FlagPath

variable {Q}

/-- The number of traversed edges modulo two, including repeated occurrences. -/
def parity {x y : Flag Face} : Q.FlagPath x y → ZMod 2
  | .nil _ => 0
  | .corner p => parity p
  | .across p => parity p
  | .along p => 1 + parity p

/-- Orientation change obtained from the actual edge gluing directions. -/
def orientation {x y : Flag Face} : Q.FlagPath x y → ZMod 2
  | .nil _ => 0
  | .corner p => orientation p
  | .across (x := x) p => Q.orientationTransition x.1 + orientation p
  | .along p => orientation p

/-- The local color after changing the frame of each square by the given phase. -/
def potential (s : Face → ZMod 2) (x : Flag Face) : ZMod 2 :=
  s x.1.1 + localColor x

private theorem double_eq_zero (x : ZMod 2) : x + x = 0 := by
  revert x
  decide

private theorem potential_corner (s : Face → ZMod 2) (x : Flag Face) :
    potential s (cornerSwap x) = potential s x := by
  unfold potential
  rw [localColor_cornerSwap]
  cases h : x.2 <;> simp [cornerSwap, h]

private theorem potential_sideFlip (s : Face → ZMod 2) (x : Flag Face) :
    potential s (sideFlip x) = potential s x + 1 := by
  change s x.1.1 + localColor (sideFlip x) = _
  rw [localColor_sideFlip]
  simp [potential, add_assoc]

private theorem potential_across (s : Face → ZMod 2)
    (hs : ∀ d, Q.colorTransition d =
      Q.orientationTransition d + s d.1 + s (Q.across d).1)
    (x : Flag Face) :
    potential s (Q.edgeSwap x) = potential s x + Q.orientationTransition x.1 := by
  have h := (Q.colorTransition_eq_localColor x).symm.trans (hs x.1)
  have hz₁ := double_eq_zero (s (Q.across x.1).1)
  have hz₂ := double_eq_zero (localColor x)
  unfold potential
  change s (Q.across x.1).1 + localColor (Q.edgeSwap x) = _
  linear_combination h + hz₁ - hz₂

/-- The difference of orientation transport and path parity telescopes to the endpoints. -/
theorem orientation_eq_parity_add_endpoints (s : Face → ZMod 2)
    (hs : ∀ d, Q.colorTransition d =
      Q.orientationTransition d + s d.1 + s (Q.across d).1)
    {x y : Flag Face} (p : Q.FlagPath x y) :
    p.orientation = p.parity + potential s x + potential s y := by
  induction p with
  | nil x => simp [orientation, parity, double_eq_zero]
  | corner p ih => simpa [orientation, parity, potential_corner] using ih
  | @across x y p ih =>
      simp only [orientation, parity, ih, potential_across s hs]
      have hz := double_eq_zero (Q.orientationTransition x.1)
      linear_combination hz
  | @along x y p ih =>
      simp only [orientation, parity, ih, potential_sideFlip]
      ring

/-- Every closed edge path is odd exactly when its local orientation is reversed. -/
theorem parity_eq_orientation (hQ : Q.OrientationTwisted)
    {x : Flag Face} (p : Q.FlagPath x x) : p.parity = p.orientation := by
  obtain ⟨s, hs⟩ := hQ
  rw [p.orientation_eq_parity_add_endpoints s hs]
  simp [add_assoc, double_eq_zero]

end FlagPath
end QuadGluing
end Tiling
