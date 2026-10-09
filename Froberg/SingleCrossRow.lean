module

public import Froberg.SingleDiagonalRow

@[expose] public section

/-! The only nonempty cross block in the small-degree row six is 2+4. -/
noncomputable section
namespace Froberg.ProductRows
open Froberg Module MvPolynomial
variable {K : Type} [Field K] {σ : Type*}

theorem multiplication_single_cross_row
    (e : ℕ → ℕ) (J : Finset ℕ) (R j : ℕ) (hj : j≠R-j)
    (q : (k : ℕ) → Fin (e k) → MvPolynomial σ K)
    (honly : ∀ r : Row J R,Columns e r → r.val.val=j)
    (hi : LinearIndependent K (fun p : Fin (e j) × Fin (e (R-j)) => q j p.1*q (R-j) p.2)) :
    Function.Injective (multiplication e q J R) := by
  classical
  by_cases hnon : Nonempty (Σ r : Row J R,Columns e r)
  · obtain ⟨r,c⟩ := hnon
    have hr := honly r c
    have hcross : r.val.val≠R-r.val.val := by simpa only [hr] using hj
    have hlocal : LinearIndependent K (products e q r) := by
      let c : Columns e r ≃ Fin (e r.val.val) × Fin (e (R-r.val.val)) := Equiv.cast (if_neg hcross)
      have hq : LinearIndependent K (fun p : Fin (e r.val.val) × Fin (e (R-r.val.val)) =>
          q r.val.val p.1*q (R-r.val.val) p.2) := by rwa [hr]
      convert hq.comp c c.injective using 1
      funext a
      simp only [products,dif_neg hcross,Function.comp_apply]
      rfl
    apply linearIndependent_sigma_one_fiber (products e q) r _ hlocal
    intro s a
    apply Subtype.ext
    apply Fin.ext
    exact (honly s a).trans hr.symm
  · letI : IsEmpty (Σ r : Row J R,Columns e r) := not_nonempty_iff.mp hnon
    exact linearIndependent_empty_type

theorem multiplication_single_cross_row_range
    (e : ℕ → ℕ) (J : Finset ℕ) (R j : ℕ) (hj : j≠R-j)
    (q : (k : ℕ) → Fin (e k) → MvPolynomial σ K)
    (honly : ∀ r : Row J R,Columns e r → r.val.val=j)
    (P : Submodule K (MvPolynomial σ K))
    (hp : ∀ p : Fin (e j) × Fin (e (R-j)),q j p.1*q (R-j) p.2∈P) :
    (multiplication e q J R).range≤P := by
  rw [multiplication,Finsupp.range_linearCombination]
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨r,c⟩,rfl⟩
  have hr := honly r c
  have hcross : r.val.val≠R-r.val.val := by simpa only [hr] using hj
  have hq : ∀ p : Fin (e r.val.val) × Fin (e (R-r.val.val)),q r.val.val p.1*q (R-r.val.val) p.2∈P := by
    rwa [hr]
  unfold products
  dsimp only
  rw [dif_neg hcross]
  exact hq _

theorem sixth_row_only_second
    (e : ℕ → ℕ) (J : Finset ℕ)
    (hz : ∀ k∈J,k≠2 → k≠4 → e k=0)
    (r : Row J 6) (c : Columns e r) : r.val.val=2 := by
  have hp := counts_positive_of_column e r c
  have hleft : r.val.val=2 ∨ r.val.val=4 := by
    by_contra h
    have hh := hz _ r.property.1 (by tauto) (by tauto)
    omega
  have hle := r.property.2.2
  omega

end Froberg.ProductRows
