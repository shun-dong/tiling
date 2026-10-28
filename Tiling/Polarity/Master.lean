import Tiling.Polarity.Tiling

/-! # The polarity master theorem, as a specialization of edge-weight cancellation -/

namespace Tiling

variable {K V Vertex Face : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype Face]

/-- The polarity master theorem in arbitrary dimension, for closed quadrilateral gluings. -/
theorem Polarity.master {Q : QuadGluing Vertex Face} {B : LinearMap.BilinForm K V}
    (T : Polarity.Tiling Q B) (hB : B.IsSymm) (hQ : Q.OrientationTwisted)
    (f₀ : Face) (hfaces : ∀ f, f ≠ f₀ → T.FaceCoherent f) :
    T.FaceCoherent f₀ := by
  apply (T.faceCoherent_iff_weight_eq_one hB f₀).mpr
  exact (T.edgeWeights hB).master hQ f₀
    (fun f hf => (T.faceCoherent_iff_weight_eq_one hB f).mp (hfaces f hf))

/-- The geometric master theorem on a finite combinatorial closed surface. -/
theorem Quadrangulation.polarity_master (Q : Quadrangulation Vertex Face)
    {B : LinearMap.BilinForm K V} (T : Polarity.Tiling Q.toQuadGluing B)
    (hB : B.IsSymm) (hQ : Q.OrientationTwisted)
    (f₀ : Face) (hfaces : ∀ f, f ≠ f₀ → T.FaceCoherent f) : T.FaceCoherent f₀ :=
  Polarity.master T hB hQ f₀ hfaces

end Tiling
