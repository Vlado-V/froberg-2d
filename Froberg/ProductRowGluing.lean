import Froberg.ProductRows

/-! Witnesses for distinct pairs in one fixed product row can be chosen
independently and assembled into one common family of layer generators. -/
noncomputable section
namespace Froberg.ProductRows
open Froberg MvPolynomial
variable {K : Type} [Field K] {σ : Type*} {J : Finset ℕ} {R : ℕ}

/-- A layer belongs to at most one unordered pair with a prescribed sum. -/
theorem row_eq_of_common_layer (a b : Row J R) {j : ℕ}
    (ha : j=a.val.val ∨ j=R-a.val.val)
    (hb : j=b.val.val ∨ j=R-b.val.val) : a=b := by
  apply Subtype.ext
  apply Fin.ext
  have ha' := a.property.2.2
  have hb' := b.property.2.2
  have hale : a.val.val ≤ R := by omega
  have hble : b.val.val ≤ R := by omega
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> omega

def assembledFamily (e : ℕ → ℕ)
    (q : (r : Row J R) → (j : ℕ) → Fin (e j) → MvPolynomial σ K)
    (j : ℕ) : Fin (e j) → MvPolynomial σ K :=
  if h : ∃ r : Row J R, j=r.val.val ∨ j=R-r.val.val then q h.choose j else 0

theorem assembledFamily_eq (e : ℕ → ℕ)
    (q : (r : Row J R) → (j : ℕ) → Fin (e j) → MvPolynomial σ K)
    (r : Row J R) {j : ℕ} (hj : j=r.val.val ∨ j=R-r.val.val) :
    assembledFamily e q j = q r j := by
  have h : ∃ r : Row J R, j=r.val.val ∨ j=R-r.val.val := ⟨r,hj⟩
  rw [assembledFamily,dif_pos h]
  rw [row_eq_of_common_layer h.choose r h.choose_spec hj]

theorem products_congr (e : ℕ → ℕ)
    (q q' : (j : ℕ) → Fin (e j) → MvPolynomial σ K) (r : Row J R)
    (hl : q r.val.val = q' r.val.val) (hr : q (R-r.val.val) = q' (R-r.val.val)) :
    products e q r = products e q' r := by
  funext c
  unfold products
  split_ifs <;> simp only [hl,hr]

/-- A common family realizes every prescribed local pair witness exactly. -/
theorem assembled_products (e : ℕ → ℕ)
    (q : (r : Row J R) → (j : ℕ) → Fin (e j) → MvPolynomial σ K)
    (r : Row J R) : products e (assembledFamily e q) r = products e (q r) r := by
  apply products_congr
  · exact assembledFamily_eq e q r (Or.inl rfl)
  · exact assembledFamily_eq e q r (Or.inr rfl)

/-- Local pair witnesses give one global polynomial family whose full
formal product row is injective. This uses the actual pair multiplication
maps, rather than merely adding separately asserted dimensions. -/
theorem exists_injective_product_row (e : ℕ → ℕ) (w : σ → ℕ)
    (heven : ∀ j ∈ J, Even j)
    (hwitness : ∀ r : Row J R,
      ∃ q : (j : ℕ) → Fin (e j) → MvPolynomial σ K,
        (∀ j ∈ J, ∀ i, (q j i).IsWeightedHomogeneous w (assignedDegree R j)) ∧
        LinearIndependent K (products e q r)) :
    ∃ q : (j : ℕ) → Fin (e j) → MvPolynomial σ K,
      (∀ j ∈ J, ∀ i, (q j i).IsWeightedHomogeneous w (assignedDegree R j)) ∧
      Function.Injective (multiplication e q J R) := by
  classical
  choose q hq hi using hwitness
  refine ⟨assembledFamily e q,?_,?_⟩
  · intro j hj i
    unfold assembledFamily
    split_ifs with h
    · exact hq h.choose j hj i
    · exact isWeightedHomogeneous_zero K w (assignedDegree R j)
  · apply multiplication_injective e _ w J R heven
    · intro j hj i
      unfold assembledFamily
      split_ifs with h
      · exact hq h.choose j hj i
      · exact isWeightedHomogeneous_zero K w (assignedDegree R j)
    · intro r
      rw [assembled_products]
      exact hi r

end Froberg.ProductRows
