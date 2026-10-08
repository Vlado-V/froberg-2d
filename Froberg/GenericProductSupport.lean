import Froberg.ProductMinors

/-! Coefficient support and assembly of independent polynomial product fibers. -/
noncomputable section
namespace Froberg.ProductMinors
open MvPolynomial
variable {K α τ ι : Type*} [CommRing K]

/-- Only sums of permitted factor exponents can occur in a generic product. -/
theorem generic_product_coeff_zero (terms : α → Finset (τ →₀ ℕ)) (a b : α)
    (row : τ →₀ ℕ)
    (h : ∀ e ∈ terms a, ∀ f ∈ terms b, row ≠ e + f) :
    ((genericForm (K := K) terms a) * genericForm terms b).coeff row = 0 := by
  classical
  simp only [genericForm, C_mul_monomial, mul_one, Finset.sum_mul, Finset.mul_sum,
    MvPolynomial.coeff_sum]
  apply Finset.sum_eq_zero
  intro e he
  apply Finset.sum_eq_zero
  intro f hf
  rw [monomial_mul_monomial, coeff_monomial, ite_eq_right (Ne.symm (h f hf e he))]

/-- Coefficient minors combine across arbitrary finite dependent fiber types. -/
theorem linearIndependent_sigma_of_fiber_minors {δ : Type*} [Fintype δ] [DecidableEq δ]
    {I : δ → Type*} [∀ d, Fintype (I d)] [∀ d, DecidableEq (I d)] [IsDomain K]
    (p : (d : δ) → I d → MvPolynomial τ K) (rows : (d : δ) → I d → τ →₀ ℕ)
    (hdet : ∀ d, Matrix.det (fun i j : I d => (p d j).coeff (rows d i)) ≠ 0)
    (hcross : ∀ d e, d ≠ e → ∀ i j, (p e j).coeff (rows d i) = 0) :
    LinearIndependent K (fun z : Sigma I => p z.1 z.2) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc z
  rcases z with ⟨d,j⟩
  have hlocal := Matrix.linearIndependent_cols_of_det_ne_zero (hdet d)
  apply Fintype.linearIndependent_iff.mp hlocal (fun i => c ⟨d,i⟩) _ j
  ext i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  change (∑ j : I d, c ⟨d,j⟩ * (p d j).coeff (rows d i)) = 0
  rw [Fintype.sum_sigma] at hc
  have hv := congrArg (fun q : MvPolynomial τ K => q.coeff (rows d i)) hc
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, smul_eq_mul,
    AddMonoidAlgebra.coeff_zero, Pi.zero_apply] at hv
  have he : (∑ e, ∑ j : I e, c ⟨e,j⟩ * (p e j).coeff (rows d i)) =
      ∑ j : I d, c ⟨d,j⟩ * (p d j).coeff (rows d i) := by
    apply Finset.sum_eq_single d
    · intro e _ hed
      apply Finset.sum_eq_zero
      intro j _
      rw [hcross d e (Ne.symm hed) i j, mul_zero]
    · simp
  exact he.symm.trans hv

end Froberg.ProductMinors
