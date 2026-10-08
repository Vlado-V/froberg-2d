import Froberg.ProductRowRename

/-! A product row of positive layers never uses the layer with its total degree.
The new-layer columns can therefore be chosen independently of that row. -/
noncomputable section
namespace Froberg.ProductRows
open Froberg MvPolynomial
variable {K : Type} [Field K] {σ : Type*}

/-- Both factors in a row of positive layers are strictly below its total degree. -/
theorem row_factors_lt {J : Finset ℕ} {R : ℕ}
    (hJ : ∀ j∈J,0<j) (p : Row J R) : p.val.val<R ∧ R-p.val.val<R := by
  have hleft := hJ _ p.property.1
  have hright := hJ _ p.property.2.1
  have hp := p.property.2.2
  omega

/-- Agreement on the two factor layers implies agreement of the actual product. -/
theorem products_congr_factors (e : ℕ → ℕ)
    (q q' : (j : ℕ) → Fin (e j) → MvPolynomial σ K)
    {J R} (p : Row J R)
    (hleft : q p.val.val=q' p.val.val)
    (hright : q (R-p.val.val)=q' (R-p.val.val)) (c : Columns e p) :
    products e q p c=products e q' p c := by
  classical
  unfold products
  split_ifs <;> simp only [hleft,hright]

/-- Product rows depend only on lower layers. -/
theorem multiplication_congr_below (e : ℕ → ℕ)
    (q q' : (j : ℕ) → Fin (e j) → MvPolynomial σ K)
    (J : Finset ℕ) (R : ℕ) (hJ : ∀ j∈J,0<j)
    (hqq : ∀ j<R,q j=q' j) :
    multiplication e q J R=multiplication e q' J R := by
  unfold multiplication
  congr 1
  funext p
  exact products_congr_factors e q q' p.1 (hqq _ (row_factors_lt hJ p.1).1)
    (hqq _ (row_factors_lt hJ p.1).2) p.2

/-- Replacing the new layer does not change any product in the current row. -/
theorem multiplication_update_self (e : ℕ → ℕ)
    (q : (j : ℕ) → Fin (e j) → MvPolynomial σ K)
    (J : Finset ℕ) (R : ℕ) (hJ : ∀ j∈J,0<j)
    (E : Fin (e R) → MvPolynomial σ K) :
    multiplication e (Function.update q R E) J R=multiplication e q J R := by
  classical
  apply multiplication_congr_below e _ _ J R hJ
  intro j hj
  exact Function.update_of_ne (Nat.ne_of_lt hj) E q

end Froberg.ProductRows
