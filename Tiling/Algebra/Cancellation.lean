import Mathlib.Data.Fintype.BigOperators

/-!
# Cancellation on quadrilateral gluings

The algebraic part of the master theorem: paired side contributions cancel,
so the product of all face contributions is one. No surface topology is used here.
-/

namespace Tiling

open scoped BigOperators

variable {F G : Type*} [Fintype F] [CommMonoid G]

/-- The product of the four side contributions to a face. -/
def faceProduct (w : F × Fin 4 → G) (f : F) : G :=
  ∏ i, w (f, i)

/-- A fixed-point-free pairing of mutually cancelling sides gives global cancellation. -/
theorem prod_faceProduct_eq_one (across : F × Fin 4 → F × Fin 4)
    (hinv : Function.Involutive across) (hne : ∀ d, across d ≠ d)
    (w : F × Fin 4 → G) (hcancel : ∀ d, w d * w (across d) = 1) :
    ∏ f, faceProduct w f = 1 := by
  classical
  change (∏ f, ∏ i, w (f, i)) = 1
  rw [← Fintype.prod_prod_type]
  exact Finset.prod_ninvolution across hcancel (fun d _ => hne d)
    (fun _ => Finset.mem_univ _) hinv

/-- If all but one face have product one, cancellation forces the remaining face. -/
theorem faceProduct_eq_one_of_all_but_one (across : F × Fin 4 → F × Fin 4)
    (hinv : Function.Involutive across) (hne : ∀ d, across d ≠ d)
    (w : F × Fin 4 → G) (hcancel : ∀ d, w d * w (across d) = 1)
    (f₀ : F) (hfaces : ∀ f, f ≠ f₀ → faceProduct w f = 1) :
    faceProduct w f₀ = 1 := by
  classical
  have hsingle : (∏ f, faceProduct w f) = faceProduct w f₀ :=
    Finset.prod_eq_single f₀ (fun f _ hf => hfaces f hf) (by simp)
  exact hsingle.symm.trans (prod_faceProduct_eq_one across hinv hne w hcancel)

end Tiling
