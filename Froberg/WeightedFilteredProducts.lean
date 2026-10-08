import Froberg.WeightedParitySpace

/-! A positive-weight factor cannot create a new first nonzero component
before that component appears in the other factor. -/
noncomputable section
namespace Froberg
open MvPolynomial
variable {K σ : Type*} [Field K]

theorem weighted_component_positive_left_zero (w : σ → ℕ)
    (p q : MvPolynomial σ K) (r : ℕ)
    (hp : weightedHomogeneousComponent w 0 p=0)
    (hq : ∀ t,t<r → weightedHomogeneousComponent w t q=0) :
    weightedHomogeneousComponent w r (p*q)=0 := by
  rw [weightedHomogeneousComponent_product]
  apply Finset.sum_eq_zero
  rintro ⟨a,b⟩ hab
  have hs : a+b=r := Finset.mem_antidiagonal.mp hab
  dsimp only
  by_cases ha : a=0
  · subst a
    rw [hp,zero_mul]
  · rw [hq b (by omega),mul_zero]

end Froberg
