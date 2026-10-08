import Froberg.ProductRows
import Froberg.ProductRowAssignments

/-! When only one layer has nonzero size, its symmetric products are the
entire product source, including after zero-size layers are added. -/
noncomputable section
namespace Froberg
open Module MvPolynomial
variable {K : Type} [Field K]

theorem linearIndependent_sigma_one_fiber {I : Type*} [Fintype I]
    {J : I → Type*} [∀ i,Fintype (J i)] {V : Type*} [AddCommGroup V] [Module K V]
    (f : (i : I) → J i → V) (i₀ : I)
    (honly : ∀ i,J i → i=i₀) (hi : LinearIndependent K (f i₀)) :
    LinearIndependent K (fun p : Sigma J => f p.1 p.2) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc p
  obtain ⟨i,x⟩ := p
  have hh := honly i x
  subst i
  apply Fintype.linearIndependent_iff.mp hi (fun y => c ⟨i₀,y⟩) _ x
  rw [Fintype.sum_sigma] at hc
  rw [Finset.sum_eq_single i₀] at hc
  · exact hc
  · intro i _ hne
    apply Finset.sum_eq_zero
    intro y _
    exact (hne (honly i y)).elim
  · simp

namespace ProductRows
variable {σ : Type*}

theorem counts_positive_of_column (e : ℕ → ℕ) {J R} (r : Row J R) (c : Columns e r) :
    0<e r.val.val ∧ 0<e (R-r.val.val) := by
  classical
  unfold Columns at c
  split_ifs at c with h
  · have hp : 0<e r.val.val := by
      induction c using Sym2.inductionOn with
      | _ a b => exact lt_of_le_of_lt (Nat.zero_le _) a.isLt
    exact ⟨hp,by rwa [←h]⟩
  · exact ⟨lt_of_le_of_lt (Nat.zero_le _) c.1.isLt,
      lt_of_le_of_lt (Nat.zero_le _) c.2.isLt⟩

theorem multiplication_single_layer (e : ℕ → ℕ) (J : Finset ℕ) (j : ℕ)
    (hz : ∀ k∈J,k≠j → e k=0)
    (q : (k : ℕ) → Fin (e k) → MvPolynomial σ K)
    (hi : LinearIndependent K (pairProducts (q j))) (R : ℕ) :
    Function.Injective (multiplication e q J R) := by
  classical
  have hindex (r : Row J R) (c : Columns e r) : r.val.val=j ∧ R=2*j := by
    have hp := counts_positive_of_column e r c
    have h1 : r.val.val=j := by
      by_contra hn
      have hh := hz _ r.property.1 hn
      omega
    have h2 : R-r.val.val=j := by
      by_contra hn
      have hh := hz _ r.property.2.1 hn
      omega
    have hle := r.val.isLt
    constructor
    · exact h1
    · omega
  by_cases hnon : Nonempty (Σ r : Row J R,Columns e r)
  · obtain ⟨r,c⟩ := hnon
    have hr := hindex r c
    have hdiag : r.val.val=R-r.val.val := by omega
    have hlocal : LinearIndependent K (products e q r) := by
      unfold products
      rw [dif_pos hdiag]
      have hq : LinearIndependent K (pairProducts (q r.val.val)) := by rwa [hr.1]
      exact hq.comp (cast (if_pos hdiag)) (Equiv.cast _).injective
    apply linearIndependent_sigma_one_fiber (products e q) r _ hlocal
    intro s b
    apply Subtype.ext
    apply Fin.ext
    exact (hindex s b).1.trans hr.1.symm
  · letI : IsEmpty (Σ r : Row J R,Columns e r) := not_nonempty_iff.mp hnon
    exact linearIndependent_empty_type

theorem single_layer_product_mem (e : ℕ → ℕ) (J : Finset ℕ) (j : ℕ)
    (hz : ∀ k∈J,k≠j → e k=0)
    (q : (k : ℕ) → Fin (e k) → MvPolynomial σ K)
    (P : Submodule K (MvPolynomial σ K))
    (hp : ∀ a,pairProducts (q j) a∈P)
    {R : ℕ} (r : Row J R) (c : Columns e r) : products e q r c∈P := by
  classical
  have hpos := counts_positive_of_column e r c
  have hleft : r.val.val=j := by
    by_contra hn
    have hh := hz _ r.property.1 hn
    omega
  have hright : R-r.val.val=j := by
    by_contra hn
    have hh := hz _ r.property.2.1 hn
    omega
  have hdiag : r.val.val=R-r.val.val := hleft.trans hright.symm
  have hh : ∀ a,pairProducts (q r.val.val) a∈P := by rwa [hleft]
  unfold products
  rw [dif_pos hdiag]
  exact hh _

theorem multiplication_single_layer_range (e : ℕ → ℕ) (J : Finset ℕ) (j : ℕ)
    (hz : ∀ k∈J,k≠j → e k=0)
    (q : (k : ℕ) → Fin (e k) → MvPolynomial σ K)
    (P : Submodule K (MvPolynomial σ K))
    (hp : ∀ a,pairProducts (q j) a∈P) (R : ℕ) :
    (multiplication e q J R).range≤P := by
  rw [multiplication,Finsupp.range_linearCombination]
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨r,c⟩,rfl⟩
  exact single_layer_product_mem e J j hz q P hp r c

end ProductRows
end Froberg
