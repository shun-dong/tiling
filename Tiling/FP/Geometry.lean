import Tiling.Geometry.Pairing
import Mathlib.LinearAlgebra.Dual.Defs

/-!
# Point--hyperplane coherence

Points are represented by nonzero vectors, hyperplanes by nonzero linear functionals.
Evaluation is a pairing between the vector space and its dual; all determinant and scaling
proofs are inherited from the common pairing geometry. No chosen polarity is required.
-/

namespace Tiling.FP

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Equality of the projective covectors representing two hyperplanes. -/
abbrev SameHyperplane (l m : Module.Dual K V) : Prop := Pairing.SamePoint (K := K) l m

/-- Equal covector spans are exactly equal kernels, including the zero case. -/
theorem sameHyperplane_iff_ker_eq (l m : Module.Dual K V) :
    SameHyperplane l m ↔ LinearMap.ker l = LinearMap.ker m := by
  constructor
  · intro h
    obtain ⟨u, hu⟩ := Submodule.span_singleton_eq_span_singleton.mp h
    rw [← hu]
    ext x
    simp [LinearMap.mem_ker, Units.smul_def]
  · intro h
    by_cases hl : l = 0
    · have hm : m = 0 := LinearMap.ker_eq_top.mp (by simpa [hl] using h.symm)
      simp [SameHyperplane, Pairing.SamePoint, hl, hm]
    · obtain ⟨u, hu⟩ : ∃ u, l u ≠ 0 := by
        contrapose! hl
        ext u
        exact hl u
      have hmu : m u ≠ 0 := by
        intro hmu
        have : u ∈ LinearMap.ker l := h.symm ▸ hmu
        exact hu this
      have heq : (m u) • l = (l u) • m := by
        ext v
        have hz : l (l u • v - l v • u) = 0 := by
          simp only [map_sub, map_smul, smul_eq_mul]
          ring
        have hmz : m (l u • v - l v • u) = 0 := by
          change (l u • v - l v • u) ∈ LinearMap.ker m
          rw [← h]
          exact hz
        simp only [map_sub, map_smul, smul_eq_mul] at hmz
        simp only [LinearMap.smul_apply, smul_eq_mul]
        linear_combination -hmz
      have hspan := congrArg (fun f : Module.Dual K V => Submodule.span K {f}) heq
      simpa only [Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hu),
        Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hmu)] using hspan

/-- The line AB meets the intersection of the two hyperplanes, with repeated labels allowed. -/
abbrev GeometricCoherent (a b : V) (l m : Module.Dual K V) : Prop :=
  Pairing.GeometricCoherent (Module.Dual.eval K V) a b l m

abbrev AlgebraicCoherent (a b : V) (l m : Module.Dual K V) : Prop :=
  Pairing.AlgebraicCoherent (Module.Dual.eval K V) a b l m

abbrev weight (a b : V) (l m : Module.Dual K V) : K :=
  Pairing.weight (Module.Dual.eval K V) a b l m

/-- The specialized definition is the geometric incidence condition using actual hyperplanes. -/
theorem geometricCoherent_iff (a b : V) (l m : Module.Dual K V) :
    GeometricCoherent a b l m ↔
      Pairing.SamePoint (K := K) a b ∨ LinearMap.ker l = LinearMap.ker m ∨
        ∃ x : V, x ≠ 0 ∧ x ∈ Submodule.span K {a, b} ∧ l x = 0 ∧ m x = 0 := by
  change _ ∨ SameHyperplane l m ∨ _ ↔ _
  simp only [sameHyperplane_iff_ker_eq, Module.Dual.eval_apply]

variable {a b : V} {l m : Module.Dual K V}

theorem geometricCoherent_iff_algebraic (hal : l a ≠ 0) (hbl : l b ≠ 0) :
    GeometricCoherent a b l m ↔ AlgebraicCoherent a b l m :=
  Pairing.geometricCoherent_iff_algebraic hal hbl

theorem geometricCoherent_iff_weight_eq_one
    (hal : l a ≠ 0) (ham : m a ≠ 0) (hbl : l b ≠ 0) :
    GeometricCoherent a b l m ↔ weight a b l m = 1 :=
  Pairing.geometricCoherent_iff_weight_eq_one hal ham hbl

theorem geometricCoherent_smul (r s t u : K)
    (hr : r ≠ 0) (hs : s ≠ 0) (ht : t ≠ 0) (hu : u ≠ 0) :
    GeometricCoherent (r • a) (s • b) (t • l) (u • m) ↔
      GeometricCoherent a b l m :=
  Pairing.geometricCoherent_smul r s t u hr hs ht hu

theorem weight_smul (r s t u : K)
    (hr : r ≠ 0) (hs : s ≠ 0) (ht : t ≠ 0) (hu : u ≠ 0) :
    weight (r • a) (s • b) (t • l) (u • m) = weight a b l m :=
  Pairing.weight_smul r s t u hr hs ht hu

end Tiling.FP
