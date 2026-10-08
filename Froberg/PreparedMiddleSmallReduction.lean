import Froberg.SmallRenamedProducts
import Froberg.PreparedFourthRow
import Froberg.PreparedSmallEvenReduction

/-! All rows in degrees five through eight are witnessed in one actual
prepared parameter space; finite rank openness makes them simultaneous. -/
noncomputable section
set_option maxHeartbeats 1800000
namespace Froberg.ProductRows
open Froberg Module MvPolynomial
variable {K : Type} [Field K] {σ : Type*}

theorem multiplication_empty_off_two_four (e : ℕ → ℕ) (J : Finset ℕ)
    (hz : ∀ k∈J,k≠2 → k≠4 → e k=0)
    (q : (k : ℕ) → Fin (e k) → MvPolynomial σ K)
    {R : ℕ} (h4 : R≠4) (h6 : R≠6) (h8 : R≠8) :
    Function.Injective (multiplication e q J R) := by
  classical
  have hempty : IsEmpty (Σ r : Row J R,Columns e r) := by
    refine ⟨?_⟩
    rintro ⟨r,c⟩
    have hp := counts_positive_of_column e r c
    have hleft : r.val.val=2 ∨ r.val.val=4 := by
      by_contra hn
      have hzero := hz _ r.property.1 (by tauto) (by tauto)
      omega
    have hright : R-r.val.val=2 ∨ R-r.val.val=4 := by
      by_contra hn
      have hzero := hz _ r.property.2.1 (by tauto) (by tauto)
      omega
    have hbound := r.val.isLt
    omega
  letI := hempty
  exact linearIndependent_empty_type

end Froberg.ProductRows

namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial MonomialExpansion
variable {K : Type} [Field K] [Infinite K]
variable {X : Type*} [AddCommGroup X] [Module K X] [Module.Finite K X]

theorem finite_middle_small_witnesses
    {w v d q a b : ℕ} {counts : ℕ → ℕ}
    [LinearOrder (Label q (allEvenIndices d) counts)]
    (hd : 5≤d) (hd8 : d≤8) (hh : 144≤w+w) (hfour : 4∣w+w)
    (ha : 0<a) (hb : 0<b) (hv : 0<v) (hab : a+b=w+w)
    (T : ℕ → MvPolynomial (Fin w × Bool) K →ₗ[K] X) (hT : T 4=0)
    (hz : ∀ k∈allEvenIndices d,k≠2 → k≠4 → counts k=0)
    (hquad : ∃ c,QuadraticRowCapacity (v+v) d q c (allEvenIndices d) counts (constrainedOutputs T))
    (hrowfour : ∃ c,FourthRowCapacity w v d q c (allEvenIndices d) counts T)
    (hcross₂ : counts 2≤((a+2-1).choose 2-finrank K X)*(v+(d-2)-1).choose (d-2))
    (hcross₄ : counts 4≤(b+4-1).choose 4*(v+(d-4)-1).choose (d-4))
    (hdiagonal₄ : if d=5 then counts 4≤((w+w)^4/256)*((v+v)/2)
      else counts 4≤((w+w)^4/256)*(v.choose (d-4)/2))
    (hscalar₆ : 6≤d → ∃ Q : Fin (Fintype.card (Label q (allEvenIndices d) counts)) → Forms K (v+v) d,
      Function.Injective (ProjectedPrefix.multiplication
        (fun α => partialDegree (balancedScalarHalf v) α≠d-2) Q (d-6)))
    (hscalar₈ : 8≤d → ∃ Q : Fin (Fintype.card (Label q (allEvenIndices d) counts)) → Forms K (v+v) d,
      Function.Injective (ProjectedPrefix.multiplication
        (fun α => partialDegree (balancedScalarHalf v) α≠2*((d-4)/2)) Q (d-8))) :
    (∀ R : allEvenIndices d,∃ p : Space (v+v) d q (allEvenIndices d) counts (constrainedOutputs T),
      LinearIndependent K (fun i => intrinsicLayerMap (fun _ _ => inf_le_left) R i p) ∧
      (row (fun _ _ => inf_le_left) R p).ker=(rowConstants (fun _ _ => inf_le_left) R p).range) ∧
    (∀ R,d<R → R≤2*d → R%2=0 →
      ∃ p : Space (v+v) d q (allEvenIndices d) counts (constrainedOutputs T),
        Function.Injective (ProductRows.multiplication counts (layers p) (allEvenIndices d) R)) := by
  classical
  let ecross : Fin (a+b) ≃ (Fin w × Bool) := (finCongr hab).trans (pairedScalarEquiv w).symm
  let ediag := (pairedScalarEquiv w).symm
  have hS : (balancedScalarHalf v).card≤(balancedScalarHalf v)ᶜ.card := by
    simp only [balancedScalarHalf_card,balancedScalarHalf_compl_card,le_refl]
  have h6 := exists_small_cross_profile_parameter_equiv (q := q) ecross ha hb hv T hT hz hcross₂ hcross₄
  have h8p : d≠5 → ∃ p : Space (v+v) d q (allEvenIndices d) counts (constrainedOutputs T),
      Function.Injective (ProductRows.multiplication counts (layers p) (allEvenIndices d) 8) ∧
      ∀ z,(ProductRows.multiplication counts (layers p) (allEvenIndices d) 8 z).IsWeightedHomogeneous
        (Sum.elim (fun _ : Fin w × Bool => 0) (ProductRows.halfWeight (balancedScalarHalf v)))
        (2*((d-4)/2)) := by
    intro hd5
    exact exists_strong_fourth_profile_parameter_equiv (q := q) ediag hh hfour T hT hz
      (balancedScalarHalf v) hS (by simpa only [if_neg hd5,balancedScalarHalf_card] using hdiagonal₄)
  have h8 : ∃ p : Space (v+v) d q (allEvenIndices d) counts (constrainedOutputs T),
      Function.Injective (ProductRows.multiplication counts (layers p) (allEvenIndices d) 8) := by
    by_cases hd5 : d=5
    · subst d
      exact exists_quintic_fourth_product_parameter_equiv ediag hh hfour T hT hz
        (by simpa using hdiagonal₄)
    · obtain ⟨p,hp,_⟩ := h8p hd5
      exact ⟨p,hp⟩
  constructor
  · intro R
    have hr := mem_allEvenIndices.mp R.property
    have hcases : R.val=2 ∨ R.val=4 ∨ R.val=6 ∨ R.val=8 := by omega
    rcases hcases with hR|hR|hR|hR
    · have h2 : 2∈allEvenIndices d := hR ▸ R.property
      have heq : R=(⟨2,h2⟩ : allEvenIndices d) := Subtype.ext hR
      subst R
      obtain ⟨c,hc⟩ := hquad
      exact exists_quadratic_row_parameter (fun _ _ => inf_le_left)
        (fun _ hj => (mem_allEvenIndices.mp hj).1) h2 hc
    · have h4 : 4∈allEvenIndices d := hR ▸ R.property
      have heq : R=(⟨4,h4⟩ : allEvenIndices d) := Subtype.ext hR
      subst R
      obtain ⟨c,hc⟩ := hrowfour
      exact exists_fourth_row_parameter h4 hc
    · obtain ⟨p,hp,hw⟩ := h6
      obtain ⟨Q,hQ⟩ := hscalar₆ (by omega)
      exact exists_empty_profile_row_parameter (fun _ _ => inf_le_left) R
        (hz _ R.property (by omega) (by omega)) (balancedScalarHalf v) (d-2) p
        (by rw [hR]; exact hp) (by rw [hR]; exact hw) Q (by rw [hR]; exact hQ)
    · obtain ⟨p,hp,hw⟩ := h8p (by omega)
      obtain ⟨Q,hQ⟩ := hscalar₈ (by omega)
      exact exists_empty_profile_row_parameter (fun _ _ => inf_le_left) R
        (hz _ R.property (by omega) (by omega)) (balancedScalarHalf v) (2*((d-4)/2)) p
        (by rw [hR]; exact hp) (by rw [hR]; exact hw) Q (by rw [hR]; exact hQ)
  · intro R hRd hR2d hRe
    by_cases hR6 : R=6
    · obtain ⟨p,hp,_⟩ := h6
      exact ⟨p,by rw [hR6]; exact hp⟩
    by_cases hR8 : R=8
    · rw [hR8]
      exact h8
    exact ⟨0,ProductRows.multiplication_empty_off_two_four counts (allEvenIndices d) hz
      (layers (0 : Space (v+v) d q (allEvenIndices d) counts (constrainedOutputs T)))
      (by omega) hR6 hR8⟩

theorem finite_middle_small_reduction_open
    {w v d q a b : ℕ} {counts : ℕ → ℕ}
    [LinearOrder (Label q (allEvenIndices d) counts)]
    (hd : 5≤d) (hd8 : d≤8) (hh : 144≤w+w) (hfour : 4∣w+w)
    (ha : 0<a) (hb : 0<b) (hv : 0<v) (hab : a+b=w+w)
    (T : ℕ → MvPolynomial (Fin w × Bool) K →ₗ[K] X) (hT : T 4=0)
    (hz : ∀ k∈allEvenIndices d,k≠2 → k≠4 → counts k=0)
    (hquad : ∃ c,QuadraticRowCapacity (v+v) d q c (allEvenIndices d) counts (constrainedOutputs T))
    (hrowfour : ∃ c,FourthRowCapacity w v d q c (allEvenIndices d) counts T)
    (hcross₂ : counts 2≤((a+2-1).choose 2-finrank K X)*(v+(d-2)-1).choose (d-2))
    (hcross₄ : counts 4≤(b+4-1).choose 4*(v+(d-4)-1).choose (d-4))
    (hdiagonal₄ : if d=5 then counts 4≤((w+w)^4/256)*((v+v)/2)
      else counts 4≤((w+w)^4/256)*(v.choose (d-4)/2))
    (hscalar₆ : 6≤d → ∃ Q : Fin (Fintype.card (Label q (allEvenIndices d) counts)) → Forms K (v+v) d,
      Function.Injective (ProjectedPrefix.multiplication
        (fun α => partialDegree (balancedScalarHalf v) α≠d-2) Q (d-6)))
    (hscalar₈ : 8≤d → ∃ Q : Fin (Fintype.card (Label q (allEvenIndices d) counts)) → Forms K (v+v) d,
      Function.Injective (ProjectedPrefix.multiplication
        (fun α => partialDegree (balancedScalarHalf v) α≠2*((d-4)/2)) Q (d-8))) :
    let A := Space (v+v) d q (allEvenIndices d) counts (constrainedOutputs T)
    ∃ D : MvPolynomial (Fin (finrank K A)) K,
      (∃ p : A,eval ((Module.finBasis K A).equivFun p) D≠0) ∧
      ∀ p : A,eval ((Module.finBasis K A).equivFun p) D≠0 → EvenPositiveReduction p := by
  classical
  obtain ⟨hrows,hproducts⟩ := finite_middle_small_witnesses hd hd8 hh hfour ha hb hv hab
    T hT hz hquad hrowfour hcross₂ hcross₄ hdiagonal₄ hscalar₆ hscalar₈
  exact even_reduction_open_of_witnesses (fun _ _ => inf_le_left)
    (fun _ hj => (mem_allEvenIndices.mp hj).1)
    (fun _ hj => (mem_allEvenIndices.mp hj).2.1)
    (fun _ hj => (mem_allEvenIndices.mp hj).2.2)
    (fun r hr hrd hre => mem_allEvenIndices.mpr ⟨by omega,hrd,hre⟩)
    hrows hproducts

end Froberg.PreparedParameters
