import Tiling.FP.Geometry
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic.FinCases

/-!
# Nondegenerate point--hyperplane examples

In the rational projective plane, the line through (1,0,0) and (0,1,0) meets
x+y=0 and x+y+z=0 at (1,-1,0). Replacing the second hyperplane by x+2y=0
breaks coherence while retaining nonincidence at all four adjacent pairs.
-/

namespace Tiling.Examples.FPGeometry

abbrev Space := Fin 3 → ℚ

private def coordinate (i : Fin 3) : Module.Dual ℚ Space := LinearMap.proj i

def a : Space := ![1, 0, 0]
def b : Space := ![0, 1, 0]
def l : Module.Dual ℚ Space := coordinate 0 + coordinate 1
def m : Module.Dual ℚ Space := l + coordinate 2
def bad : Module.Dual ℚ Space := coordinate 0 + 2 • coordinate 1
def intersection : Space := ![1, -1, 0]

theorem adjacent_nonincident :
    l a ≠ 0 ∧ l b ≠ 0 ∧ m a ≠ 0 ∧ m b ≠ 0 ∧ bad a ≠ 0 ∧ bad b ≠ 0 := by
  norm_num [Matrix.cons_val_two, coordinate, l, m, bad, a, b]

theorem distinct_points : ¬ Pairing.SamePoint (K := ℚ) a b := by
  intro h
  have ha : a ∈ Submodule.span ℚ {b} := h ▸ Submodule.subset_span (by simp)
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp ha
  have := congrFun hr 0
  norm_num [Matrix.cons_val_two, coordinate, a, b] at this

theorem distinct_hyperplanes : ¬ FP.SameHyperplane l m := by
  intro h
  have hk := (FP.sameHyperplane_iff_ker_eq l m).mp h
  have hm : m (![0, 0, 1] : Space) = 0 := by
    change (![0, 0, 1] : Space) ∈ LinearMap.ker m
    rw [← hk]
    norm_num [Matrix.cons_val_two, coordinate, LinearMap.mem_ker, l]
  norm_num [Matrix.cons_val_two, coordinate, m, l] at hm

/-- A concrete nonzero intersection witness proves the genuine incidence branch. -/
theorem coherent : FP.GeometricCoherent a b l m := by
  right; right
  refine ⟨intersection, ?_, ?_, ?_, ?_⟩
  · intro h
    have := congrFun h 0
    norm_num [Matrix.cons_val_two, coordinate, intersection] at this
  · apply Submodule.mem_span_pair.mpr
    refine ⟨1, -1, ?_⟩
    ext i
    fin_cases i <;> norm_num [Matrix.cons_val_two, coordinate, a, b, intersection]
  · norm_num [Matrix.cons_val_two, coordinate, l, intersection]
  · norm_num [Matrix.cons_val_two, coordinate, m, l, intersection]

/-- The second example satisfies nonincidence but its pairing determinant is nonzero. -/
theorem not_coherent : ¬ FP.GeometricCoherent a b l bad := by
  intro h
  have hd := (FP.geometricCoherent_iff_algebraic
    adjacent_nonincident.1 adjacent_nonincident.2.1).mp h
  norm_num [Matrix.cons_val_two, coordinate, FP.AlgebraicCoherent,
    Pairing.AlgebraicCoherent, Module.Dual.eval_apply, l, bad, a, b] at hd

end Tiling.Examples.FPGeometry
