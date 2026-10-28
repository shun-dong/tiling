import Tiling.Combinatorics.Quadrangulation
import Mathlib.Tactic.LinearCombination

/-!
# Orientability and vertex colorings

Local square orientations can be flipped to agree across every glued side precisely when
their transition system is a coboundary. A global alternating vertex coloring trivializes
the local color transitions in the same way. Together these give orientation twisting.
-/

namespace Tiling.QuadGluing

variable {Vertex Face : Type*} (Q : QuadGluing Vertex Face)

/-- Choices of local orientation flips making all square orientations compatible. -/
def Orientable : Prop :=
  ∃ o : Face → ZMod 2, ∀ d,
    Q.orientationTransition d = o d.1 + o (Q.across d).1

/-- A two-coloring of the global vertices, alternating across every side. -/
structure Coloring where
  color : Vertex → ZMod 2
  edge : ∀ d, color (Q.head d) = color (Q.tail d) + 1

private theorem double_eq_zero (x : ZMod 2) : x + x = 0 := by
  revert x
  decide

namespace Coloring

variable {Q} (c : Q.Coloring)

/-- A vertex coloring restricts to the usual alternating colors on each square. -/
theorem vertex (f : Face) (i : Fin 4) :
    c.color (Q.vertex f i) = c.color (Q.vertex f 0) + (i.val : ZMod 2) := by
  have h₁ : c.color (Q.vertex f 1) = c.color (Q.vertex f 0) + 1 := by
    simpa [tail, head] using c.edge (f, 0)
  have h₂ : c.color (Q.vertex f 2) = c.color (Q.vertex f 1) + 1 := by
    simpa [tail, head] using c.edge (f, 1)
  have h₃ : c.color (Q.vertex f 3) = c.color (Q.vertex f 2) + 1 := by
    simpa [tail, head] using c.edge (f, 2)
  fin_cases i <;>
    simp [h₁, h₂, h₃, add_assoc, show (1 + 1 : ZMod 2) = 0 by decide,
      show (2 : ZMod 2) = 0 by decide, show (3 : ZMod 2) = 1 by decide]

/-- Local and global endpoint colors differ by the color at the square's initial vertex. -/
theorem flag (x : Flag Face) :
    c.color (flagVertex Q.vertex x) = c.color (Q.vertex x.1.1 0) + localColor x := by
  rcases x with ⟨d, b⟩
  cases b
  · simpa [flagVertex, localColor] using c.vertex d.1 d.2
  · change c.color (Q.head d) = c.color (Q.vertex d.1 0) + ((d.2.val : ZMod 2) + 1)
    rw [c.edge]
    change c.color (Q.vertex d.1 d.2) + 1 = _
    rw [c.vertex]
    exact add_assoc _ _ _

/-- A global coloring expresses the color transition as a difference of local frames. -/
theorem colorTransition (d : Side Face) :
    Q.colorTransition d = c.color (Q.vertex d.1 0) + c.color (Q.vertex (Q.across d).1 0) := by
  let x : Flag Face := (d, false)
  have hv := congrArg c.color (Q.flagVertex_edgeSwap x)
  rw [c.flag, c.flag] at hv
  rw [Q.colorTransition_eq_localColor x]
  change localColor (Q.edgeSwap x) + localColor x = _
  change c.color (Q.vertex (Q.across d).1 0) + localColor (Q.edgeSwap x) =
    c.color (Q.vertex d.1 0) + localColor x at hv
  linear_combination hv + double_eq_zero (localColor x) -
    double_eq_zero (c.color (Q.vertex (Q.across d).1 0))

end Coloring

/-- An orientable gluing with a vertex two-coloring is orientation-twisted. -/
theorem orientationTwisted_of_orientable (hQ : Q.Orientable) (c : Q.Coloring) :
    Q.OrientationTwisted := by
  obtain ⟨o, ho⟩ := hQ
  refine ⟨fun f => c.color (Q.vertex f 0) + o f, ?_⟩
  intro d
  rw [c.colorTransition, ho]
  linear_combination -double_eq_zero (o d.1) - double_eq_zero (o (Q.across d).1)

end Tiling.QuadGluing
