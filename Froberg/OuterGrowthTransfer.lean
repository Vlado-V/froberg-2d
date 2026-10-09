module

public import Froberg.OuterLoss
public import Froberg.OuterInitialFibers

@[expose] public section

/-! Transfer from the finite ideal-shadow estimate to actual outer-module growth. -/
noncomputable section
namespace Froberg.AttachedMultiplication
open Module Finset Quartic.HomogeneousCoefficientCoordinates
variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I] {n s h : ℕ}
variable (e : I → Fin n →₀ ℕ) (v : I → Fin h → K) (he : ∀ i, (e i).degree = s)

theorem sum_source_fiber_finrank :
    (∑ a : Exponent n s, finrank K ((Fin h → K) ⧸ relationFiber e v a.val)) =
      finrank K ((Fin h → Forms K n s) ⧸ relationSpace (d := 0) e v he) := by
  simpa only [Nat.add_zero, Module.finrank_pi_fintype] using (quotientFiberEquiv (d := 0) e v he).finrank_eq.symm

/-- All geometric steps of the outer-module growth proof. The sole remaining
input is an explicitly finite numerical ideal-shadow lower bound. -/
theorem uniform_outer_growth_of_ideal_bound (hn : 0 < n)
    (hv : ∀ S : Finset I, S.card ≤ h → LinearIndependent K (fun i : S => v i.val))
    (hm : MixedExterior.UniversalMixedPosition v)
    (hsize : ∀ b : Exponent n (s+(s+1)), (labelsBelow e b.val).card ≤ h)
    (R D : ℝ)
    (hbound : ∀ C : (a : Exponent n s) → Submodule K ((Fin h → K) ⧸ relationFiber e v a.val),
      R * (∑ a, finrank K (C a) : ℕ) +
        (D + h*((h*2^h)*(n+s-1).choose s)) *
          (min (∑ a, finrank K (C a))
            (finrank K ((Fin h → Forms K n s) ⧸ relationSpace (d := 0) e v he) -
              ∑ a, finrank K (C a)) : ℕ) ≤
        (∑ b, idealShadow e v C b : ℕ)) :
    ∀ L : Submodule K ((Fin h → Forms K n s) ⧸ relationSpace (d := 0) e v he),
      R * finrank K L + D *
        (min (finrank K L)
          (finrank K ((Fin h → Forms K n s) ⧸ relationSpace (d := 0) e v he) -
            finrank K L) : ℕ) ≤
        finrank K (outerImage (d := s+1) e v he L) := by
  intro L
  obtain ⟨C,hCdim,hCimage⟩ := exists_initial_monomial_fibers (d := s+1) e v he L
  have hb := hbound C
  have hl := idealShadow_sum_le_actual_image_add_loss e v hn he hv hm hsize C
  rw [sum_source_fiber_finrank e v he] at hl
  have hlR : (∑ b, idealShadow e v C b : ℕ) ≤
      (finrank K (Quartic.BilinearImage.image (fiberMultiply (d := s+1) e v he)
        (Submodule.pi Set.univ C)) : ℝ) +
      (h*((h*2^h)*(n+s-1).choose s) : ℕ) *
        (min (∑ a, finrank K (C a))
          (finrank K ((Fin h → Forms K n s) ⧸ relationSpace (d := 0) e v he) -
            ∑ a, finrank K (C a)) : ℕ) := by exact_mod_cast hl
  have hiR : (finrank K (Quartic.BilinearImage.image (fiberMultiply (d := s+1) e v he)
      (Submodule.pi Set.univ C)) : ℝ) ≤ finrank K (outerImage (d := s+1) e v he L) := by
    exact_mod_cast hCimage
  rw [hCdim] at hb hlR
  push_cast at hb hlR ⊢
  nlinarith

end Froberg.AttachedMultiplication
