module

public import Froberg.QuadraticBlockAssembly
public import Froberg.PairedSpace

@[expose] public section

/-! A strengthened quadratic independent-product construction, and the
quadratic dimension required in Proposition 4.2. -/
noncomputable section
namespace Froberg.QuadraticBlocks
open Module PairedMonomials ProductFibers
variable {K : Type} [Field K] [Infinite K]

@[simp] theorem card_label (X : Type*) [Fintype X] [DecidableEq X] :
    Fintype.card (Label X) = 2 * (Fintype.card X).choose 2 := by
  simp only [Label, Fintype.card_prod, PairedMonomials.card_sizedSubset, Fintype.card_bool]
  omega

/-- Two forms per block pair, with no loss to the symmetric-product property. -/
theorem block_space_exists (w : ℕ) :
    ∃ W : Submodule K (MvPolynomial (Fin w × Bool) K),
      W ≤ MvPolynomial.homogeneousSubmodule (Fin w × Bool) K 2 ∧
      finrank K W = 2 * w.choose 2 ∧
      Function.Injective (subspaceSymmetricMultiplication W) := by
  obtain ⟨values, hp⟩ := exists_independent_pairProducts (X := Fin w) (K := K)
  let q := specializedForm values
  refine ⟨Submodule.span K (Set.range q), ?_, ?_, ?_⟩
  · exact Submodule.span_le.mpr (by rintro _ ⟨l,rfl⟩; exact specializedForm_homogeneous values l)
  · rw [finrank_span_eq_card (linearIndependent_of_pairProducts q hp), card_label, Fintype.card_fin]
  · exact symmetricMultiplication_injective_of_pairProducts q hp

/-- Restrict the family to any smaller number of generators and rename the
paired variables injectively into an arbitrary larger variable set. -/
theorem exists_independent_quadrics {h w m : ℕ}
    (hvars : 2*w ≤ h) (hcount : m ≤ 2*w.choose 2) :
    ∃ q : Fin m → Poly K h,
      (∀ i, q i ∈ Forms K h 2) ∧ LinearIndependent K (pairProducts q) := by
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

/-- The elementary count is substantially stronger than the required 5/32. -/
theorem required_quadratic_count {h : ℕ} (hh : 65 ≤ h) :
    5*h^2/32 ≤ 2*(h/2).choose 2 := by
  have hc : 2*(h/2).choose 2 = (h/2)*(h/2-1) := by
    simpa only [Nat.choose_one_right, Nat.mul_comm] using Nat.choose_succ_right_eq (h/2) 1
  rw [hc]
  have hw : 32 ≤ h/2 := by omega
  have hh' : h ≤ 2*(h/2)+1 := by omega
  have hs : h*h ≤ (2*(h/2)+1)*(2*(h/2)+1) := Nat.mul_self_le_mul_self hh'
  have hp : h/2-1+1 = h/2 := by omega
  have hq : 32*(h/2) ≤ (h/2)*(h/2) := Nat.mul_le_mul_right (h/2) hw
  have hb : 5*h^2 ≤ 32*((h/2)*(h/2-1)) := by nlinarith
  calc
    5*h^2/32 ≤ (32*((h/2)*(h/2-1)))/32 := Nat.div_le_div_right hb
    _ = (h/2)*(h/2-1) := by omega

/-- Proposition 4.2(H2), proved by explicit generic block minors. -/
theorem quadratic_space_exists {h : ℕ} (hh : 65 ≤ h) :
    ∃ W : Submodule K (Poly K h),
      W ≤ Forms K h 2 ∧ finrank K W = 5*h^2/32 ∧
      Function.Injective (subspaceSymmetricMultiplication W) := by
  obtain ⟨q, hq, hp⟩ := exists_independent_quadrics (K := K)
    (h := h) (w := h/2) (m := 5*h^2/32) (by omega) (required_quadratic_count hh)
  refine ⟨Submodule.span K (Set.range q), ?_, ?_, ?_⟩
  · exact Submodule.span_le.mpr (by rintro _ ⟨i,rfl⟩; exact hq i)
  · rw [finrank_span_eq_card (linearIndependent_of_pairProducts q hp), Fintype.card_fin]
  · exact symmetricMultiplication_injective_of_pairProducts q hp

end Froberg.QuadraticBlocks
