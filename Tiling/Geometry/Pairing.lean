import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Geometric coherence for a pairing of two vector spaces

Nonzero vectors represent projective points. `SamePoint` identifies representatives of the same
point. A bilinear pairing permits one common determinant criterion for point--hyperplane
incidence and polarity coherence, including repeated opposite labels. No dimension assumption
is needed.
-/

namespace Tiling.Pairing

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Equality of the one-dimensional spans representing projective points. -/
def SamePoint (a b : V) : Prop :=
  Submodule.span K {a} = Submodule.span K {b}

variable {W : Type*} [AddCommGroup W] [Module K W]

/-- The line through the left pair meets the common annihilator of the right pair. -/
def GeometricCoherent (B : V →ₗ[K] W →ₗ[K] K) (a b : V) (c d : W) : Prop :=
  SamePoint (K := K) a b ∨ SamePoint (K := K) c d ∨
    ∃ x : V, x ≠ 0 ∧ x ∈ Submodule.span K {a, b} ∧ B x c = 0 ∧ B x d = 0

/-- The determinant criterion for paired coherence. -/
def AlgebraicCoherent (B : V →ₗ[K] W →ₗ[K] K) (a b : V) (c d : W) : Prop :=
  B a c * B b d = B a d * B b c

/-- The mixed cross-ratio of a tile, in cyclic order `a,c,b,d`. -/
def weight (B : V →ₗ[K] W →ₗ[K] K) (a b : V) (c d : W) : K :=
  (B a c * B b d) / (B a d * B b c)

variable {B : V →ₗ[K] W →ₗ[K] K} {a b : V} {c d : W}

/-- Geometric coherence is exactly the vanishing of the two-by-two pairing determinant. -/
theorem geometricCoherent_iff_algebraic (hac : B a c ≠ 0) (hbc : B b c ≠ 0) :
    GeometricCoherent B a b c d ↔ AlgebraicCoherent B a b c d := by
  constructor
  · rintro (hab | hcd | ⟨x, hx, hspan, hxc, hxd⟩)
    · obtain ⟨u, hu⟩ := Submodule.span_singleton_eq_span_singleton.mp hab
      rw [← hu]
      simp only [AlgebraicCoherent, Units.smul_def, LinearMap.map_smul₂, smul_eq_mul]
      ring
    · obtain ⟨u, hu⟩ := Submodule.span_singleton_eq_span_singleton.mp hcd
      rw [← hu]
      simp only [AlgebraicCoherent, Units.smul_def, map_smul, smul_eq_mul]
      ring
    · obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hspan
      simp only [LinearMap.map_add₂, LinearMap.map_smul₂, smul_eq_mul] at hxc hxd
      have hs : s ≠ 0 := by
        intro hs
        have ht : t = 0 := (mul_eq_zero.mp (by simpa [hs] using hxc)).resolve_right hbc
        exact hx (by simp [hs, ht])
      have hdet : s * (B a c * B b d - B a d * B b c) = 0 := by
        linear_combination B b d * hxc - B b c * hxd
      exact sub_eq_zero.mp ((mul_eq_zero.mp hdet).resolve_left hs)
  · intro hdet
    by_cases hab : SamePoint (K := K) a b
    · exact Or.inl hab
    · right; right
      refine ⟨B b c • a - B a c • b, ?_, ?_, ?_, ?_⟩
      · intro hx
        apply hab
        have heq := congrArg (fun x : V => Submodule.span K {x}) (sub_eq_zero.mp hx)
        simpa only [Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hbc),
          Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hac)] using heq
      · exact Submodule.mem_span_pair.mpr ⟨B b c, -(B a c), by simp [sub_eq_add_neg]⟩
      · simp only [LinearMap.map_sub₂, LinearMap.map_smul₂, smul_eq_mul]
        ring
      · simp only [LinearMap.map_sub₂, LinearMap.map_smul₂, smul_eq_mul]
        unfold AlgebraicCoherent at hdet
        linear_combination -hdet

/-- Under the nonconjugacy assumptions, geometric coherence is equivalent to weight one. -/
theorem geometricCoherent_iff_weight_eq_one
    (hac : B a c ≠ 0) (had : B a d ≠ 0) (hbc : B b c ≠ 0) :
    GeometricCoherent B a b c d ↔ weight B a b c d = 1 := by
  rw [geometricCoherent_iff_algebraic hac hbc]
  exact (div_eq_one_iff_eq (mul_ne_zero had hbc)).symm

/-- For nonzero representatives, `SamePoint` is literal equality in projective space. -/
theorem samePoint_iff_projectivization_mk_eq (ha : a ≠ 0) (hb : b ≠ 0) :
    SamePoint (K := K) a b ↔ Projectivization.mk K a ha = Projectivization.mk K b hb := by
  change (Projectivization.mk K a ha).submodule = (Projectivization.mk K b hb).submodule ↔ _
  exact ⟨fun h => Projectivization.submodule_injective h, congrArg Projectivization.submodule⟩

/-- Replacing either representative by a nonzero multiple does not change its projective point. -/
theorem samePoint_smul (r s : K) (hr : r ≠ 0) (hs : s ≠ 0) :
    SamePoint (K := K) (r • a) (s • b) ↔ SamePoint (K := K) a b := by
  simp only [SamePoint,
    Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hr),
    Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hs)]

/-- The geometric definition is independent of all four choices of representative. -/
theorem geometricCoherent_smul (r s t u : K)
    (hr : r ≠ 0) (hs : s ≠ 0) (ht : t ≠ 0) (hu : u ≠ 0) :
    GeometricCoherent B (r • a) (s • b) (t • c) (u • d) ↔
      GeometricCoherent B a b c d := by
  have hspan : Submodule.span K {r • a, s • b} = Submodule.span K {a, b} := by
    simp only [Submodule.span_insert,
      Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hr),
      Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hs)]
  simp only [GeometricCoherent, samePoint_smul r s hr hs, samePoint_smul t u ht hu,
    hspan, map_smul, smul_eq_mul, mul_eq_zero, ht, hu, false_or]

/-- The mixed cross-ratio is likewise independent of representatives. -/
theorem weight_smul (r s t u : K)
    (hr : r ≠ 0) (hs : s ≠ 0) (ht : t ≠ 0) (hu : u ≠ 0) :
    weight B (r • a) (s • b) (t • c) (u • d) = weight B a b c d := by
  simp only [weight, map_smul, LinearMap.smul_apply, smul_eq_mul]
  calc
    _ = ((r * s * t * u) * (B a c * B b d)) /
        ((r * s * t * u) * (B a d * B b c)) := by congr 1 <;> ring
    _ = _ := mul_div_mul_left _ _ (mul_ne_zero (mul_ne_zero (mul_ne_zero hr hs) ht) hu)

end Tiling.Pairing
