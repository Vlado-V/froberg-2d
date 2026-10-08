import Froberg.AttachedMultiplication

/-! Polynomial injectivity for the monomial-attached outer module of Appendix B.2. -/
noncomputable section
namespace Froberg.OuterInjection
open MvPolynomial

abbrev Labels (k a s : ℕ) := Fin k × Sym (Fin a) s

/-- Include a core monomial into the full core-plus-free variable set. -/
def coreExponent {k a s : ℕ} (z : ℕ) (i : Labels k a s) : Fin (a+z) →₀ ℕ :=
  ((exponentEquiv a s i.2).val).mapDomain (Fin.castAdd z)

@[simp] theorem coreExponent_degree {k a s : ℕ} (z : ℕ) (i : Labels k a s) :
    (coreExponent z i).degree = s := by
  rw [coreExponent,Finsupp.degree_mapDomain]
  exact (exponentEquiv a s i.2).property

/-- Each target has at most k times choose(degβ,s) attached source labels. -/
theorem card_target_labels_le {k a s : ℕ} (z : ℕ) (β : Fin (a+z) →₀ ℕ) :
    Fintype.card {i : Labels k a s // coreExponent z i ≤ β} ≤
      k * β.degree.choose s := by
  classical
  let f : {i : Labels k a s // coreExponent z i ≤ β} →
      Fin k × MonomialExpansion.Divisor β s := fun i =>
    (i.val.1,⟨coreExponent z i.val,
      Finset.mem_filter.mpr ⟨MonomialExpansion.mem_exponents.mpr (coreExponent_degree z i.val),i.property⟩⟩)
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun p : Fin k × MonomialExpansion.Divisor β s => p.1) hij
    · have he := congrArg (fun p : Fin k × MonomialExpansion.Divisor β s => p.2.val) hij
      have he' : (exponentEquiv a s i.val.2).val = (exponentEquiv a s j.val.2).val :=
        Finsupp.mapDomain_injective (Fin.castAdd_injective a z) he
      exact (exponentEquiv a s).injective (Subtype.ext he')
  calc
    Fintype.card {i : Labels k a s // coreExponent z i ≤ β} ≤
        Fintype.card (Fin k × MonomialExpansion.Divisor β s) :=
      Fintype.card_le_of_injective f hf
    _ = k * Fintype.card (MonomialExpansion.Divisor β s) := by simp
    _ ≤ k * β.degree.choose s := Nat.mul_le_mul_left k
      (MonomialExpansion.card_divisor_le β s)

/-- The actual monomial-attached polynomial map is injective whenever the
output dimension meets the target divisor bound. This is the first assertion
of Theorem B.2, without any asymptotic hypotheses. -/
theorem exists_injective_attached_multiplication_through {K : Type*} [Field K] [Infinite K]
    (k a z s d h : ℕ) (hh : k * (s+d).choose s ≤ h) :
    ∃ v : Labels k a s → Fin h → K, ∀ c ≤ d,
      Function.Injective (AttachedMultiplication.multiplication (d := c) (coreExponent z) v) := by
  classical
  obtain ⟨v,hv⟩ := GeneralPositionVectors.exists_small_subfamilies_independent
    (K := K) (α := Labels k a s) h
  refine ⟨v,?_⟩
  intro c hc
  apply AttachedMultiplication.injective_of_independent_fibers (coreExponent z) v
    (coreExponent_degree z)
  intro β hβ
  let U : Finset (Labels k a s) := Finset.univ.filter (fun i => coreExponent z i ≤ β)
  have hU : U.card ≤ h := by
    have hcard : Fintype.card {i : Labels k a s // coreExponent z i ≤ β} ≤ h :=
      (card_target_labels_le (k := k) (s := s) z β).trans
      (by
        rw [hβ]
        exact (Nat.mul_le_mul_left k (Nat.choose_le_choose s (Nat.add_le_add_left hc s))).trans hh)
    simpa only [Fintype.card_subtype] using hcard
  let f : {i : Labels k a s // coreExponent z i ≤ β} → U := fun i =>
    ⟨i.val,by simp only [U,Finset.mem_filter,Finset.mem_univ,true_and]; exact i.property⟩
  have hf : Function.Injective f := by
    intro i j hij
    exact Subtype.ext (congrArg (fun x : U => x.val) hij)
  exact (hv U hU).comp f hf

/-- Polynomial injectivity at one prescribed coefficient degree. -/
theorem exists_injective_attached_multiplication {K : Type*} [Field K] [Infinite K]
    (k a z s d h : ℕ) (hh : k * (s+d).choose s ≤ h) :
    ∃ v : Labels k a s → Fin h → K,
      Function.Injective (AttachedMultiplication.multiplication (d := d) (coreExponent z) v) := by
  obtain ⟨v,hv⟩ := exists_injective_attached_multiplication_through (K := K) k a z s d h hh
  exact ⟨v,hv d le_rfl⟩

end Froberg.OuterInjection
