import Tiling.FP.Geometry
import Tiling.Combinatorics.Coloring
import Tiling.Algebra.EdgeWeights

/-!
# Point--hyperplane tilings

A label is a point vector or a hyperplane covector. Nonzero adjacent evaluations enforce
both alternating types and nonincidence. Geometric coherence allows repeated opposite
projective points or hyperplanes. All edge cancellation is delegated to EdgeWeights.
-/

namespace Tiling.FP

/-- A homogeneous representative of either a point or a hyperplane. -/
inductive Label (K V : Type*) [Field K] [AddCommGroup V] [Module K V] where
  | point : V → Label K V
  | hyperplane : Module.Dual K V → Label K V

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

namespace Label

/-- A representative must be nonzero to define a projective object. -/
def Nonzero : Label K V → Prop
  | .point a => a ≠ 0
  | .hyperplane l => l ≠ 0

/-- Point and hyperplane types supply the global two-coloring. -/
def color : Label K V → ZMod 2
  | .point _ => 0
  | .hyperplane _ => 1

/-- Evaluation on opposite types, and zero on equal types. -/
def pairing : Label K V → Label K V → K
  | .point a, .hyperplane l => l a
  | .hyperplane l, .point a => l a
  | _, _ => 0

theorem pairing_symm (p q : Label K V) : pairing p q = pairing q p := by
  cases p <;> cases q <;> rfl

/-- Nonzero evaluation forces opposite types. -/
theorem color_of_pairing_ne_zero (p q : Label K V) (h : pairing p q ≠ 0) :
    color q = color p + 1 := by
  cases p <;> cases q <;>
    simp_all [pairing, color, show (1 + 1 : ZMod 2) = 0 by decide]

/-- The point line meets the intersection of the two hyperplanes, including degeneracies. -/
def Coherent : Label K V → Label K V → Label K V → Label K V → Prop
  | .point a, .hyperplane l, .point b, .hyperplane m => GeometricCoherent a b l m
  | .hyperplane l, .point a, .hyperplane m, .point b => GeometricCoherent a b l m
  | _, _, _, _ => False

/-- The geometric criterion is the alternating product of the four edge evaluations. -/
theorem coherent_iff_weight_eq_one {p₀ p₁ p₂ p₃ : Label K V}
    (h₀₁ : pairing p₀ p₁ ≠ 0) (h₁₂ : pairing p₁ p₂ ≠ 0)
    (h₂₃ : pairing p₂ p₃ ≠ 0) (h₃₀ : pairing p₃ p₀ ≠ 0) :
    Coherent p₀ p₁ p₂ p₃ ↔
      (pairing p₀ p₁ * pairing p₂ p₃) / (pairing p₁ p₂ * pairing p₃ p₀) = 1 := by
  cases p₀ <;> cases p₁ <;> cases p₂ <;> cases p₃ <;>
    simp only [pairing, Coherent] at * <;> try contradiction
  · simpa [weight, Pairing.weight, mul_comm] using
      geometricCoherent_iff_weight_eq_one h₀₁ h₃₀ h₁₂
  · simpa [weight, Pairing.weight] using
      geometricCoherent_iff_weight_eq_one h₀₁ h₁₂ h₃₀

end Label

variable {Vertex Face : Type*}

/-- A realized FP tiling with nonincident adjacent point--hyperplane labels. -/
structure Tiling (Q : QuadGluing Vertex Face) where
  label : Vertex → Label K V
  label_ne_zero : ∀ v, (label v).Nonzero
  edge_ne_zero : ∀ d, Label.pairing (label (Q.tail d)) (label (Q.head d)) ≠ 0

namespace Tiling

variable {Q : QuadGluing Vertex Face} (T : Tiling (K := K) (V := V) Q)

/-- The point/hyperplane distinction gives the required coloring of vertices. -/
def coloring : Q.Coloring where
  color v := (T.label v).color
  edge d := Label.color_of_pairing_ne_zero _ _ (T.edge_ne_zero d)

/-- The same scalar evaluation is used from both sides of each glued edge. -/
def edgeWeights : EdgeWeights Q K :=
  EdgeWeights.ofPairing Q T.label Label.pairing Label.pairing_symm T.edge_ne_zero

/-- Geometric coherence in the cyclic order of the four positions of a face. -/
def FaceCoherent (f : Face) : Prop :=
  Label.Coherent (T.label (Q.vertex f 0)) (T.label (Q.vertex f 1))
    (T.label (Q.vertex f 2)) (T.label (Q.vertex f 3))

/-- The face incidence statement is equivalent to its common edge weight being one. -/
theorem faceCoherent_iff_weight_eq_one (f : Face) :
    T.FaceCoherent f ↔ T.edgeWeights.faceWeight f = 1 := by
  have h₀₁ : Label.pairing (T.label (Q.vertex f 0)) (T.label (Q.vertex f 1)) ≠ 0 := by
    simpa [QuadGluing.tail, QuadGluing.head] using T.edge_ne_zero (f, 0)
  have h₁₂ : Label.pairing (T.label (Q.vertex f 1)) (T.label (Q.vertex f 2)) ≠ 0 := by
    simpa [QuadGluing.tail, QuadGluing.head] using T.edge_ne_zero (f, 1)
  have h₂₃ : Label.pairing (T.label (Q.vertex f 2)) (T.label (Q.vertex f 3)) ≠ 0 := by
    simpa [QuadGluing.tail, QuadGluing.head] using T.edge_ne_zero (f, 2)
  have h₃₀ : Label.pairing (T.label (Q.vertex f 3)) (T.label (Q.vertex f 0)) ≠ 0 := by
    simpa [QuadGluing.tail, QuadGluing.head] using T.edge_ne_zero (f, 3)
  simpa [FaceCoherent, edgeWeights, EdgeWeights.ofPairing, EdgeWeights.faceWeight,
    QuadGluing.tail, QuadGluing.head] using
    Label.coherent_iff_weight_eq_one h₀₁ h₁₂ h₂₃ h₃₀

end Tiling
end Tiling.FP
