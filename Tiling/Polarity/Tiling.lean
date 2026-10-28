import Tiling.Polarity.Geometry
import Tiling.Algebra.EdgeWeights
import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# Realized polarity tilings

Nonzero vectors represent the vertex points. A symmetric form turns their pairings into the
shared edge-weight system. Coherence retains the geometric line--polar-subspace definition.
-/

namespace Tiling.Polarity

variable {K V Vertex Face : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- A polarity realization with nonconjugate adjacent projective points. -/
structure Tiling (Q : QuadGluing Vertex Face) (B : LinearMap.BilinForm K V) where
  point : Vertex → V
  point_ne_zero : ∀ v, point v ≠ 0
  edge_ne_zero : ∀ d, B (point (Q.tail d)) (point (Q.head d)) ≠ 0

namespace Tiling

variable {Q : QuadGluing Vertex Face} {B : LinearMap.BilinForm K V} (T : Tiling Q B)

/-- Pairing values on the unoriented edges, shared with the FP construction. -/
def edgeWeights (hB : B.IsSymm) : EdgeWeights Q K :=
  EdgeWeights.ofPairing Q T.point (fun a b => B a b) (fun a b => hB.eq a b) T.edge_ne_zero

/-- The two pairs of opposite vertices are fed to the geometric coherence predicate. -/
def FaceCoherent (f : Face) : Prop :=
  GeometricCoherent B (T.point (Q.vertex f 0)) (T.point (Q.vertex f 2))
    (T.point (Q.vertex f 1)) (T.point (Q.vertex f 3))

/-- The common face weight is the mixed cross-ratio of the four point representatives. -/
theorem edgeWeights_faceWeight (hB : B.IsSymm) (f : Face) :
    (T.edgeWeights hB).faceWeight f =
      weight B (T.point (Q.vertex f 0)) (T.point (Q.vertex f 2))
        (T.point (Q.vertex f 1)) (T.point (Q.vertex f 3)) := by
  simp [edgeWeights, EdgeWeights.ofPairing, EdgeWeights.faceWeight, weight, Pairing.weight,
    QuadGluing.tail, QuadGluing.head, hB.eq, mul_comm]

/-- The geometric criterion identifies coherence with shared face weight one. -/
theorem faceCoherent_iff_weight_eq_one (hB : B.IsSymm) (f : Face) :
    T.FaceCoherent f ↔ (T.edgeWeights hB).faceWeight f = 1 := by
  rw [T.edgeWeights_faceWeight hB]
  apply geometricCoherent_iff_weight_eq_one
  · simpa [QuadGluing.tail, QuadGluing.head] using T.edge_ne_zero (f, 0)
  · rw [hB.eq]
    simpa [QuadGluing.tail, QuadGluing.head] using T.edge_ne_zero (f, 3)
  · rw [hB.eq]
    simpa [QuadGluing.tail, QuadGluing.head] using T.edge_ne_zero (f, 1)

end Tiling
end Tiling.Polarity
