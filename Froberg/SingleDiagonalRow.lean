import Froberg.SingleLayerProducts

/-! A fixed product row can be diagonal even when other generator layers
are nonempty. This is the quartic-square row in the small-degree construction. -/
noncomputable section
namespace Froberg.ProductRows
open Froberg Module MvPolynomial
variable {K : Type} [Field K] {σ : Type*}

theorem multiplication_single_diagonal_row
    (e : ℕ → ℕ) (J : Finset ℕ) (j : ℕ)
    (q : (k : ℕ) → Fin (e k) → MvPolynomial σ K)
    (honly : ∀ r : Row J (2*j),Columns e r → r.val.val=j)
    (hi : LinearIndependent K (pairProducts (q j))) :
    Function.Injective (multiplication e q J (2*j)) := by
  classical
  by_cases hnon : Nonempty (Σ r : Row J (2*j),Columns e r)
  · obtain ⟨r,c⟩ := hnon
    have hr := honly r c
    have hdiag : r.val.val=2*j-r.val.val := by omega
    have hlocal : LinearIndependent K (products e q r) := by
      unfold products
      rw [dif_pos hdiag]
      have hq : LinearIndependent K (pairProducts (q r.val.val)) := by rwa [hr]
      exact hq.comp (cast (if_pos hdiag)) (Equiv.cast _).injective
    apply linearIndependent_sigma_one_fiber (products e q) r _ hlocal
    intro s b
    apply Subtype.ext
    apply Fin.ext
    exact (honly s b).trans hr.symm
  · letI : IsEmpty (Σ r : Row J (2*j),Columns e r) := not_nonempty_iff.mp hnon
    exact linearIndependent_empty_type

theorem multiplication_single_diagonal_row_range
    (e : ℕ → ℕ) (J : Finset ℕ) (j : ℕ)
    (q : (k : ℕ) → Fin (e k) → MvPolynomial σ K)
    (honly : ∀ r : Row J (2*j),Columns e r → r.val.val=j)
    (P : Submodule K (MvPolynomial σ K)) (hp : ∀ a,pairProducts (q j) a∈P) :
    (multiplication e q J (2*j)).range≤P := by
  rw [multiplication,Finsupp.range_linearCombination]
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨r,c⟩,rfl⟩
  have hr := honly r c
  have hdiag : r.val.val=2*j-r.val.val := by omega
  have hq : ∀ a,pairProducts (q r.val.val) a∈P := by rwa [hr]
  unfold products
  dsimp only
  rw [dif_pos hdiag]
  exact hq _

theorem eighth_row_only_fourth
    (e : ℕ → ℕ) (J : Finset ℕ)
    (hz : ∀ k∈J,k≠2 → k≠4 → e k=0)
    (r : Row J 8) (c : Columns e r) : r.val.val=4 := by
  have hp := counts_positive_of_column e r c
  have hleft : r.val.val=2 ∨ r.val.val=4 := by
    by_contra h
    have hh := hz _ r.property.1 (by tauto) (by tauto)
    omega
  have hright : 8-r.val.val=2 ∨ 8-r.val.val=4 := by
    by_contra h
    have hh := hz _ r.property.2.1 (by tauto) (by tauto)
    omega
  omega

end Froberg.ProductRows
