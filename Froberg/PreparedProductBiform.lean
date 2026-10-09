module

public import Froberg.PreparedCoreExtension
public import Froberg.ProductRowRename

@[expose] public section

/-! Product columns lie in their literal homogeneous bidegree and commute
with adjoining private variables. -/
noncomputable section
namespace Froberg.ProductRows
open Froberg MvPolynomial
variable {K : Type} [Field K] [Infinite K] {σ : Type*} [Fintype σ]
variable {n d R : ℕ} {J : Finset ℕ} {counts : ℕ → ℕ}

theorem products_full_biform
    (E : (j : ℕ) → Fin (counts j) → MvPolynomial (σ ⊕ Fin n) K)
    (hR : R≤2*d)
    (hE : ∀ j∈J,∀ i,(E j i).IsHomogeneous d)
    (hEX : ∀ j∈J,∀ i,(E j i).IsWeightedHomogeneous
      (Sum.elim (fun _ : σ => 1) (fun _ : Fin n => 0)) j)
    (p : Row J R) (c : Columns counts p) :
    products counts E p c∈FullBiform K σ n R (2*d-R) := by
  classical
  have hmem {j k : ℕ} (hj : j∈J) (hk : k∈J) (hjk : j+k=R)
      (i : Fin (counts j)) (l : Fin (counts k)) :
      E j i*E k l∈FullBiform K σ n R (2*d-R) := by
    apply mem_biformImage_of_homogeneous
    · rw [Nat.add_sub_of_le hR]
      simpa only [two_mul] using (hE j hj i).mul (hE k hk l)
    · simpa only [hjk] using (hEX j hj i).mul (hEX k hk l)
  unfold products
  split_ifs with hp
  · dsimp only
    generalize hc : cast (if_pos hp) c = t
    induction t using Sym2.inductionOn with
    | _ i l =>
      apply hmem p.property.1 p.property.1 (by have := p.property.2.2;omega) i l
  · exact hmem p.property.1 p.property.2.1
      (by have := p.val.isLt;omega) _ _

theorem multiplication_range_full_biform
    (E : (j : ℕ) → Fin (counts j) → MvPolynomial (σ ⊕ Fin n) K)
    (hR : R≤2*d)
    (hE : ∀ j∈J,∀ i,(E j i).IsHomogeneous d)
    (hEX : ∀ j∈J,∀ i,(E j i).IsWeightedHomogeneous
      (Sum.elim (fun _ : σ => 1) (fun _ : Fin n => 0)) j) :
    (multiplication counts E J R).range≤FullBiform K σ n R (2*d-R) := by
  rw [multiplication,Finsupp.range_linearCombination]
  apply Submodule.span_le.mpr
  rintro _ ⟨p,rfl⟩
  exact products_full_biform E hR hE hEX p.1 p.2

end Froberg.ProductRows

namespace Froberg.PreparedParameters
open Froberg MvPolynomial
variable {K : Type} [Field K] [Infinite K] {σ : Type*} [Fintype σ]
variable {a z d q : ℕ} {J : Finset ℕ} {counts : ℕ → ℕ}
variable {O : ℕ → Submodule K (MvPolynomial σ K)}

theorem coreExtension_layers (p : Space a d q J counts O) :
    layers (coreExtension z p)=fun j i => rename (Sum.map id (Fin.castAdd z)) (layers p j i) := by
  classical
  funext j i
  by_cases hj : j∈J
  · simp only [layers,dif_pos hj]
    rfl
  · simp only [layers,dif_neg hj,map_zero]

theorem coreExtension_products (p : Space a d q J counts O) (R : ℕ) :
    ProductRows.multiplication counts (layers (coreExtension z p)) J R=
      (rename (Sum.map id (Fin.castAdd z))).toLinearMap.comp
        (ProductRows.multiplication counts (layers p) J R) := by
  rw [coreExtension_layers,ProductRows.multiplication_rename]

end Froberg.PreparedParameters
