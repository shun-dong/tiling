import Tiling.FP.Tiling

/-!
# The Fomin--Pylyavskyy master theorem

Orientation and the point/hyperplane coloring supply orientation twisting. The shared
edge-weight master theorem then transfers through the geometric face criterion.
-/

namespace Tiling

variable {K V Vertex Face : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- FP master theorem over any field and in arbitrary dimension. -/
theorem FP.master [Fintype Face] {Q : QuadGluing Vertex Face}
    (T : FP.Tiling (K := K) (V := V) Q) (hQ : Q.Orientable)
    (f₀ : Face) (hfaces : ∀ f, f ≠ f₀ → T.FaceCoherent f) :
    T.FaceCoherent f₀ := by
  apply (T.faceCoherent_iff_weight_eq_one f₀).mpr
  exact T.edgeWeights.master (Q.orientationTwisted_of_orientable hQ T.coloring) f₀
    (fun f hf => (T.faceCoherent_iff_weight_eq_one f).mp (hfaces f hf))

/-- The FP master theorem for a finite combinatorial closed orientable surface. -/
theorem Quadrangulation.fp_master [Fintype Face] (Q : Quadrangulation Vertex Face)
    (T : FP.Tiling (K := K) (V := V) Q.toQuadGluing) (hQ : Q.toQuadGluing.Orientable)
    (f₀ : Face) (hfaces : ∀ f, f ≠ f₀ → T.FaceCoherent f) :
    T.FaceCoherent f₀ :=
  FP.master T hQ f₀ hfaces

end Tiling
