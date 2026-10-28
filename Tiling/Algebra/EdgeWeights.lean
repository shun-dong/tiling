import Tiling.Combinatorics.Quadrangulation
import Tiling.Algebra.Cancellation
import Mathlib.Algebra.BigOperators.Fin

/-!
# Nonzero edge weights and the common master theorem

An edge weight is independent of which paired side occurrence is chosen. Orientation twisting
supplies alternating exponents, so paired contributions cancel. Geometry enters only through
an identification of face coherence with face weight one.
-/

namespace Tiling

open scoped BigOperators

variable {Vertex Face K : Type*} [Field K]

/-- Nonzero weights on the edges of a quadrilateral gluing, expressed on side occurrences. -/
structure EdgeWeights (Q : QuadGluing Vertex Face) (K : Type*) [Field K] where
  value : Side Face → K
  ne_zero : ∀ d, value d ≠ 0
  across_eq : ∀ d, value (Q.across d) = value d

namespace EdgeWeights

variable {Q : QuadGluing Vertex Face}

/-- A symmetric pairing on vertex labels defines well-defined edge weights. -/
def ofPairing {Label : Type*} (Q : QuadGluing Vertex Face) (label : Vertex → Label)
    (pair : Label → Label → K) (hsymm : ∀ a b, pair a b = pair b a)
    (hnz : ∀ d, pair (label (Q.tail d)) (label (Q.head d)) ≠ 0) : EdgeWeights Q K where
  value d := pair (label (Q.tail d)) (label (Q.head d))
  ne_zero := hnz
  across_eq d := by
    cases hrev : Q.reverse d
    · have ht : Q.tail (Q.across d) = Q.tail d := by
        simpa [QuadGluing.tail, flagVertex, hrev] using Q.glued d false
      have hh : Q.head (Q.across d) = Q.head d := by
        simpa [QuadGluing.head, flagVertex, hrev] using Q.glued d true
      rw [ht, hh]
    · have ht : Q.tail (Q.across d) = Q.head d := by
        simpa [QuadGluing.tail, QuadGluing.head, flagVertex, hrev] using Q.glued d true
      have hh : Q.head (Q.across d) = Q.tail d := by
        simpa [QuadGluing.tail, QuadGluing.head, flagVertex, hrev] using Q.glued d false
      rw [ht, hh, hsymm]

variable (W : EdgeWeights Q K)

/-- The alternating product of the four edge weights of a face. -/
def faceWeight (f : Face) : K :=
  (W.value (f, 0) * W.value (f, 2)) / (W.value (f, 1) * W.value (f, 3))

private def signed (phase : ZMod 2) (a : K) : K :=
  if phase = 0 then a else a⁻¹

private theorem signed_mul_signed_add_one (phase : ZMod 2) (a : K) (ha : a ≠ 0) :
    signed phase a * signed (phase + 1) a = 1 := by
  fin_cases phase <;> simp [signed, ha, show (1 + 1 : ZMod 2) = 0 by decide]

private theorem prod_signed (phase : ZMod 2) (w : Fin 4 → K) :
    (∏ i, signed (phase + (i.val : ZMod 2)) (w i)) =
      if phase = 0 then (w 0 * w 2) / (w 1 * w 3)
      else ((w 0 * w 2) / (w 1 * w 3))⁻¹ := by
  have h2 : (2 : ZMod 2) = 0 := by decide
  have h3 : (3 : ZMod 2) = 1 := by decide
  have h11 : (1 + 1 : ZMod 2) = 0 := by decide
  fin_cases phase <;>
    simp [signed, Fin.prod_univ_four, h2, h3, h11, div_eq_mul_inv,
      mul_comm, mul_left_comm, mul_assoc]

/-- A side contribution, with a choice of alternating phase on each face. -/
def contribution (s : Face → ZMod 2) (d : Side Face) : K :=
  signed (s d.1 + (d.2.val : ZMod 2)) (W.value d)

theorem contribution_mul_across (s : Face → ZMod 2)
    (hs : ∀ d, s (Q.across d).1 + ((Q.across d).2.val : ZMod 2) =
      s d.1 + (d.2.val : ZMod 2) + 1) (d : Side Face) :
    W.contribution s d * W.contribution s (Q.across d) = 1 := by
  unfold contribution
  rw [hs d, W.across_eq d]
  exact signed_mul_signed_add_one _ _ (W.ne_zero d)

/-- Each phased face contribution is its face weight or its inverse. -/
theorem faceProduct_contribution (s : Face → ZMod 2) (f : Face) :
    faceProduct (W.contribution s) f =
      if s f = 0 then W.faceWeight f else (W.faceWeight f)⁻¹ := by
  simp only [faceProduct, contribution]
  exact prod_signed (s f) (fun i => W.value (f, i))

theorem faceProduct_contribution_eq_one_iff (s : Face → ZMod 2) (f : Face) :
    faceProduct (W.contribution s) f = 1 ↔ W.faceWeight f = 1 := by
  rw [W.faceProduct_contribution]
  split_ifs <;> simp

/-- Common master theorem: all but one face weight equal to one forces the remaining one. -/
theorem master [Fintype Face] (hQ : Q.OrientationTwisted)
    (f₀ : Face) (hfaces : ∀ f, f ≠ f₀ → W.faceWeight f = 1) :
    W.faceWeight f₀ = 1 := by
  obtain ⟨s, hs⟩ := Q.orientationTwisted_iff_phase.mp hQ
  apply (W.faceProduct_contribution_eq_one_iff s f₀).mp
  exact faceProduct_eq_one_of_all_but_one Q.across Q.across_involutive Q.across_ne
    (W.contribution s) (W.contribution_mul_across s hs) f₀
    (fun f hf => (W.faceProduct_contribution_eq_one_iff s f).mpr (hfaces f hf))

end EdgeWeights
end Tiling
