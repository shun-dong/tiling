import Tiling.Geometry.Pairing
import Mathlib.LinearAlgebra.BilinearForm.Basic

/-!
# Polarity coherence

The common pairing geometry specializes to a bilinear form on a single vector space.
The arguments are opposite pairs: the cyclic boundary order is a,c,b,d.
-/

namespace Tiling.Polarity

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

abbrev SamePoint (a b : V) : Prop := Pairing.SamePoint (K := K) a b

/-- The line AB meets the polar subspace of CD, with repeated opposite points allowed. -/
abbrev GeometricCoherent (B : LinearMap.BilinForm K V) (a b c d : V) : Prop :=
  Pairing.GeometricCoherent B a b c d

abbrev AlgebraicCoherent (B : LinearMap.BilinForm K V) (a b c d : V) : Prop :=
  Pairing.AlgebraicCoherent B a b c d

abbrev weight (B : LinearMap.BilinForm K V) (a b c d : V) : K :=
  Pairing.weight B a b c d

variable {B : LinearMap.BilinForm K V} {a b c d : V}

theorem geometricCoherent_iff_algebraic (hac : B a c ≠ 0) (hbc : B b c ≠ 0) :
    GeometricCoherent B a b c d ↔ AlgebraicCoherent B a b c d :=
  Pairing.geometricCoherent_iff_algebraic hac hbc

theorem geometricCoherent_iff_weight_eq_one
    (hac : B a c ≠ 0) (had : B a d ≠ 0) (hbc : B b c ≠ 0) :
    GeometricCoherent B a b c d ↔ weight B a b c d = 1 :=
  Pairing.geometricCoherent_iff_weight_eq_one hac had hbc

theorem geometricCoherent_smul (r s t u : K)
    (hr : r ≠ 0) (hs : s ≠ 0) (ht : t ≠ 0) (hu : u ≠ 0) :
    GeometricCoherent B (r • a) (s • b) (t • c) (u • d) ↔
      GeometricCoherent B a b c d :=
  Pairing.geometricCoherent_smul r s t u hr hs ht hu

theorem weight_smul (r s t u : K)
    (hr : r ≠ 0) (hs : s ≠ 0) (ht : t ≠ 0) (hu : u ≠ 0) :
    weight B (r • a) (s • b) (t • c) (u • d) = weight B a b c d :=
  Pairing.weight_smul r s t u hr hs ht hu

end Tiling.Polarity
