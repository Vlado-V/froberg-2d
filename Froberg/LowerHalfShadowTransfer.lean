module

public import Froberg.OuterGrowthTransfer

@[expose] public section

/-! A lower-half ideal bound transfers to every actual subspace of that size. -/
noncomputable section
namespace Froberg.AttachedMultiplication
open Module Finset Quartic.HomogeneousCoefficientCoordinates
variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I] {n s h : ℕ}

lemma lower_half_growth_of_ideal_bound
    (e : I → Fin n →₀ ℕ) (v : I → Fin h → K) (he : ∀ i,(e i).degree=s)
    (hn : 0<n)
    (hv : ∀ U : Finset I,U.card≤h → LinearIndependent K (fun i : U => v i.val))
    (hm : MixedExterior.UniversalMixedPosition v)
    (hsize : ∀ β : Exponent n (s+(s+1)),(labelsBelow e β.val).card≤h)
    (R G : ℝ)
    (hbound : ∀ C : (α : Exponent n s) → Submodule K ((Fin h → K) ⧸ relationFiber e v α.val),
      2*(∑ α,finrank K (C α))≤finrank K ((Fin h → Forms K n s) ⧸ relationSpace (d := 0) e v he) →
      R*(∑ α,finrank K (C α) : ℕ)+G*(∑ α,finrank K (C α) : ℕ)≤
        (∑ β,idealShadow e v C β : ℕ))
    (L : Submodule K ((Fin h → Forms K n s) ⧸ relationSpace (d := 0) e v he))
    (hL : 2*finrank K L≤finrank K ((Fin h → Forms K n s) ⧸ relationSpace (d := 0) e v he)) :
    R*(finrank K L : ℝ)+(G-(h*((h*2^h)*(n+s-1).choose s) : ℕ))*(finrank K L : ℝ)≤
      (finrank K (outerImage (d := s+1) e v he L) : ℝ) := by
  obtain ⟨C,hCdim,hCimage⟩ := exists_initial_monomial_fibers (d := s+1) e v he L
  have hb := hbound C (by rwa [hCdim])
  have hl := idealShadow_sum_le_actual_image_add_loss e v hn he hv hm hsize C
  have hmin := Nat.mul_le_mul_left (h*((h*2^h)*(n+s-1).choose s))
    (min_le_left (∑ α,finrank K (C α))
      ((∑ α : Exponent n s,finrank K ((Fin h → K) ⧸ relationFiber e v α.val))-∑ α,finrank K (C α)))
  have hsum : (∑ β,idealShadow e v C β)≤
      finrank K (outerImage (d := s+1) e v he L)+
        h*((h*2^h)*(n+s-1).choose s)*(∑ α,finrank K (C α)) := by omega
  rw [hCdim] at hb hsum
  have hsR := (Nat.cast_le (α := ℝ)).mpr hsum
  push_cast at hsR hb
  push_cast
  nlinarith

end Froberg.AttachedMultiplication
