import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Relation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Closed quadrilateral gluings and orientation twisting

Sides and their two endpoint flags remain distinct incidences, even when the resulting
vertices or edges coincide. The reversal bit records the actual gluing map: true exchanges
the endpoints, hence the induced boundary directions are opposite.

Quadrangulation additionally requires connected incidence links. This is a finite
combinatorial surface model; no bridge to a topological realization or a Mathlib
characteristic class is asserted here.
-/

namespace Tiling

abbrev Side (Face : Type*) := Face × Fin 4
abbrev Flag (Face : Type*) := Side Face × Bool

variable {Vertex Face : Type*}

/-- The vertex at a specified occurrence of a side endpoint. -/
def flagVertex (vertex : Face → Fin 4 → Vertex) (x : Flag Face) : Vertex :=
  vertex x.1.1 (x.1.2 + if x.2 then 1 else 0)

/-- The alternating color of an endpoint in its square, before any gluing. -/
def localColor (x : Flag Face) : ZMod 2 :=
  (x.1.2.val : ZMod 2) + if x.2 then 1 else 0

/-- The two side endpoints bounding the same corner of a square. -/
def cornerSwap (x : Flag Face) : Flag Face :=
  if x.2 then ((x.1.1, x.1.2 + 1), false)
  else ((x.1.1, x.1.2 + 3), true)

/-- A closed gluing of quadrilateral disks. Repeated vertices and loop edges are allowed. -/
structure QuadGluing (Vertex Face : Type*) where
  vertex : Face → Fin 4 → Vertex
  across : Side Face → Side Face
  across_involutive : Function.Involutive across
  across_ne : ∀ d, across d ≠ d
  reverse : Side Face → Bool
  reverse_across : ∀ d, reverse (across d) = reverse d
  glued : ∀ d b,
    flagVertex vertex (across d, b.xor (reverse d)) = flagVertex vertex (d, b)

namespace QuadGluing

variable (Q : QuadGluing Vertex Face)

def tail (d : Side Face) : Vertex := Q.vertex d.1 d.2
def head (d : Side Face) : Vertex := Q.vertex d.1 (d.2 + 1)

/-- Cross a glued side while retaining the same endpoint occurrence. -/
def edgeSwap (x : Flag Face) : Flag Face :=
  (Q.across x.1, x.2.xor (Q.reverse x.1))

theorem edgeSwap_involutive : Function.Involutive Q.edgeSwap := by
  rintro ⟨d, b⟩
  cases h : Q.reverse d <;> cases b <;>
    simp [edgeSwap, Q.across_involutive d, Q.reverse_across d, h]

theorem edgeSwap_ne (x : Flag Face) : Q.edgeSwap x ≠ x := by
  intro h
  exact Q.across_ne x.1 (congrArg Prod.fst h)

theorem flagVertex_edgeSwap (x : Flag Face) :
    flagVertex Q.vertex (Q.edgeSwap x) = flagVertex Q.vertex x :=
  Q.glued x.1 x.2

/-- The two types of interval adjacency in a vertex link. -/
def LinkAdjacent (x y : Flag Face) : Prop :=
  y = Q.edgeSwap x ∨ y = cornerSwap x

/-- Every vertex occurs, and its incidence link is connected.

Each flag has a corner neighbor and a gluing neighbor; multiplicities are retained.
For finite face sets this describes a single link circle, including nonregular cellulations.
-/
def IsSurface : Prop :=
  (∀ v, ∃ x, flagVertex Q.vertex x = v) ∧
    ∀ x y, flagVertex Q.vertex x = flagVertex Q.vertex y →
      Relation.ReflTransGen Q.LinkAdjacent x y

/-- Change of orientation between the square charts along a glued side. -/
def orientationTransition (d : Side Face) : ZMod 2 :=
  if Q.reverse d then 0 else 1

/-- Change between the local alternating colorings of the two squares. -/
def colorTransition (d : Side Face) : ZMod 2 :=
  (d.2.val : ZMod 2) + ((Q.across d).2.val : ZMod 2) + 1 +
    Q.orientationTransition d

/-- Orientation change is the same in either direction across a glued edge. -/
theorem orientationTransition_across (d : Side Face) :
    Q.orientationTransition (Q.across d) = Q.orientationTransition d := by
  simp [orientationTransition, Q.reverse_across]

/-- Color change is the same in either direction across a glued edge. -/
theorem colorTransition_across (d : Side Face) :
    Q.colorTransition (Q.across d) = Q.colorTransition d := by
  simp only [colorTransition, Q.across_involutive d, Q.orientationTransition_across d]
  ring

/-- The transition is exactly the difference of the two colors at a glued endpoint. -/
theorem colorTransition_eq_localColor (x : Flag Face) :
    Q.colorTransition x.1 = localColor (Q.edgeSwap x) + localColor x := by
  rcases x with ⟨d, b⟩
  cases h : Q.reverse d <;> cases b <;>
    simp [colorTransition, orientationTransition, edgeSwap, localColor, h] <;>
      (ring_nf; try simp [show (2 : ZMod 2) = 0 by decide])

/-- The color and orientation transition systems differ by a change of local frames. -/
def OrientationTwisted : Prop :=
  ∃ s : Face → ZMod 2, ∀ d,
    Q.colorTransition d =
      Q.orientationTransition d + s d.1 + s (Q.across d).1

private theorem transition_eq_iff (i j x y e : ZMod 2) :
    i + j + 1 + e = e + x + y ↔ y + j = x + i + 1 := by
  revert i j x y e
  decide

/-- Twisting gives opposite exponents on each pair of glued side occurrences. -/
theorem orientationTwisted_iff_phase :
    Q.OrientationTwisted ↔
      ∃ s : Face → ZMod 2, ∀ d,
        s (Q.across d).1 + ((Q.across d).2.val : ZMod 2) =
          s d.1 + (d.2.val : ZMod 2) + 1 := by
  simp only [OrientationTwisted, colorTransition, transition_eq_iff]
end QuadGluing

theorem cornerSwap_involutive : Function.Involutive (cornerSwap (Face := Face)) := by
  rintro ⟨⟨f, i⟩, b⟩
  fin_cases i <;> cases b <;> simp [cornerSwap]

theorem cornerSwap_ne (x : Flag Face) : cornerSwap x ≠ x := by
  rcases x with ⟨⟨f, i⟩, b⟩
  cases b <;> simp [cornerSwap]

theorem flagVertex_cornerSwap (vertex : Face → Fin 4 → Vertex) (x : Flag Face) :
    flagVertex vertex (cornerSwap x) = flagVertex vertex x := by
  rcases x with ⟨⟨f, i⟩, b⟩
  fin_cases i <;> cases b <;> simp [cornerSwap, flagVertex]

/-- The two flags of a corner give the same local color. -/
theorem localColor_cornerSwap (x : Flag Face) : localColor (cornerSwap x) = localColor x := by
  rcases x with ⟨⟨f, i⟩, b⟩
  fin_cases i <;> cases b <;> simp [localColor, cornerSwap] <;> decide

/-- A finite combinatorial closed surface with a quadrilateral cellulation. -/
structure Quadrangulation (Vertex Face : Type*) [Fintype Face]
    extends QuadGluing Vertex Face where
  isSurface : toQuadGluing.IsSurface

end Tiling
