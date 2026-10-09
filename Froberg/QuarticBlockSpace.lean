module

public import Froberg.QuarticBlockAssembly
public import Froberg.PairedSpace

@[expose] public section

/-! A strengthened quartic independent-product construction, and the
quartic dimension required in Proposition 4.2. -/
noncomputable section
namespace Froberg.QuarticBlocks
open Module PairedMonomials ProductFibers
variable {K : Type} [Field K] [Infinite K]

@[simp] theorem card_label (X : Type*) [Fintype X] [DecidableEq X] :
    Fintype.card (Label X) = 2 * (Fintype.card X).choose 4 := by
  simp only [Label, Fintype.card_prod, PairedMonomials.card_sizedSubset, Fintype.card_bool]
  omega

/-- Two forms per four-element block support, with no loss to the symmetric-product property. -/
theorem block_space_exists (w : ℕ) :
    ∃ W : Submodule K (MvPolynomial (Fin w × Bool) K),
      W ≤ MvPolynomial.homogeneousSubmodule (Fin w × Bool) K 4 ∧
      finrank K W = 2 * w.choose 4 ∧
      Function.Injective (subspaceSymmetricMultiplication W) := by
  obtain ⟨values, hp⟩ := exists_independent_pairProducts (X := Fin w) (K := K)
  let q := specializedForm values
  refine ⟨Submodule.span K (Set.range q), ?_, ?_, ?_⟩
  · exact Submodule.span_le.mpr (by rintro _ ⟨l,rfl⟩; exact specializedForm_homogeneous values l)
  · rw [finrank_span_eq_card (linearIndependent_of_pairProducts q hp), card_label, Fintype.card_fin]
  · exact symmetricMultiplication_injective_of_pairProducts q hp

/-- Restrict the family to any smaller number of generators and rename the
paired variables injectively into an arbitrary larger variable set. -/
theorem exists_independent_quartics {h w m : ℕ}
    (hvars : 2*w ≤ h) (hcount : m ≤ 2*w.choose 4) :
    ∃ q : Fin m → Poly K h,
      (∀ i, q i ∈ Forms K h 4) ∧ LinearIndependent K (pairProducts q) := by
  classical
  obtain ⟨values, hp⟩ := exists_independent_pairProducts (X := Fin w) (K := K)
  obtain ⟨generators⟩ : Nonempty (Fin m ↪ Label (Fin w)) :=
    Function.Embedding.nonempty_of_card_le (by simpa [mul_comm] using hcount)
  obtain ⟨varEmbed⟩ : Nonempty ((Fin w × Bool) ↪ Fin h) :=
    Function.Embedding.nonempty_of_card_le (by simpa [mul_comm] using hvars)
  let q : Fin m → Poly K h := fun i =>
    MvPolynomial.rename varEmbed (specializedForm values (generators i))
  refine ⟨q, ?_, ?_⟩
  · intro i
    exact (specializedForm_homogeneous values (generators i)).rename_isHomogeneous
  · have hrestricted := hp.comp (Sym2.map generators) (Sym2.map.injective generators.injective)
    have hrenamed := hrestricted.map' (MvPolynomial.rename varEmbed).toLinearMap
      (LinearMap.ker_eq_bot.mpr (MvPolynomial.rename_injective varEmbed varEmbed.injective))
    convert hrenamed using 1
    funext p
    induction p using Sym2.inductionOn with
    | _ i j => simp only [pairProducts_mk, Function.comp_apply, Sym2.map_mk,
        AlgHom.toLinearMap_apply, map_mul, q]

/-- A convenient exact lower bound for four-element subsets. -/
theorem fourth_power_le_thirtytwo_choose_four {w : ℕ} (hw : 24 ≤ w) :
    w^4 ≤ 32*w.choose 4 := by
  have hc := Nat.descFactorial_eq_factorial_mul_choose w 4
  norm_num [Nat.descFactorial_succ, Nat.descFactorial_zero] at hc
  have hcZ : 24*(w.choose 4 : ℤ) =
      (w : ℤ)*((w : ℤ)-1)*((w : ℤ)-2)*((w : ℤ)-3) := by
    have h := congrArg (fun n : ℕ => (n : ℤ)) hc
    push_cast [Nat.cast_sub (by omega : 1 ≤ w), Nat.cast_sub (by omega : 2 ≤ w),
      Nat.cast_sub (by omega : 3 ≤ w)] at h
    nlinarith
  have hwZ : (24 : ℤ) ≤ w := by exact_mod_cast hw
  have hlarge : 0 ≤ (w : ℤ)^3*((w : ℤ)-24) := mul_nonneg (by positivity) (by omega)
  have hsmall : 0 ≤ (w : ℤ)*(44*(w : ℤ)-24) := mul_nonneg (by positivity) (by omega)
  have h : (w : ℤ)^4 ≤ 32*(w.choose 4 : ℤ) := by nlinarith
  exact_mod_cast h

/-- The stronger two-form construction has enough quartics for Appendix A.3. -/
theorem required_quartic_count {h : ℕ} (hh : 144 ≤ h) (hfour : 4 ∣ h) :
    h^4/256 ≤ 2*(h/2).choose 4 := by
  obtain ⟨t,rfl⟩ := hfour
  have ht : 36 ≤ t := by omega
  have hw := fourth_power_le_thirtytwo_choose_four (w := 2*t) (by omega)
  have hpower : t^4 ≤ 2*(2*t).choose 4 := by nlinarith [hw]
  have hdiv : (4*t)/2 = 2*t := by omega
  rw [hdiv, Nat.mul_pow]
  norm_num
  exact hpower

/-- Proposition 4.2(H4), via five checked unrestricted block fibers. -/
theorem quartic_space_exists {h : ℕ} (hh : 144 ≤ h) (hfour : 4 ∣ h) :
    ∃ W : Submodule K (Poly K h),
      W ≤ Forms K h 4 ∧ finrank K W = h^4/256 ∧
      Function.Injective (subspaceSymmetricMultiplication W) := by
  obtain ⟨q, hq, hp⟩ := exists_independent_quartics (K := K)
    (h := h) (w := h/2) (m := h^4/256) (by omega) (required_quartic_count hh hfour)
  refine ⟨Submodule.span K (Set.range q), ?_, ?_, ?_⟩
  · exact Submodule.span_le.mpr (by rintro _ ⟨i,rfl⟩; exact hq i)
  · rw [finrank_span_eq_card (linearIndependent_of_pairProducts q hp), Fintype.card_fin]
  · exact symmetricMultiplication_injective_of_pairProducts q hp

end Froberg.QuarticBlocks
