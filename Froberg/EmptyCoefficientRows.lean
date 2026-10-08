import Froberg.CoefficientRowFromPairs
import Froberg.EvenCoefficientElimination

/-! Above the coefficient degree, only the independent formal products remain. -/
noncomputable section
namespace Froberg
open MvPolynomial
variable {K : Type} {σ I : Type*} [Field K] [Fintype I]

/-- Weights at most one leave no degree-d coefficient in output degree above d. -/
theorem coefficientComponentSpace_above (w : σ → ℕ) (hw : ∀ x,w x≤1)
    {d r : ℕ} (hr : d<r) : coefficientComponentSpace (K := K) w d r=⊥ := by
  apply le_antisymm
  · intro f hf
    change f=0
    ext α
    by_contra hα
    have hα' : f.coeff α≠0 := by simpa using hα
    have ht := hf.1 hα'
    have hx := hf.2 hα'
    have hdegree : α.degree=d := by
      simpa only [Finsupp.degree_eq_weight_one,Pi.one_def] using ht
    have hle := weight_le_degree w hw α
    omega
  · exact bot_le

/-- No scalar or new-layer coefficients occur above degree d, so product
independence is the entire row condition. -/
theorem coefficient_row_above_degree (w : σ → ℕ) (hw : ∀ x,w x≤1)
    {d r : ℕ} (hr : d<r) (a E : I → MvPolynomial σ K) (j : I → ℕ)
    (hj : ∀ i,j i≤d)
    (hpairs : LinearIndependent K
      (fun p : {p : Sym2 I // positiveDegreePair j r p} => pairProducts E p.val)) :
    CoefficientRowExact (coefficientComponentSpace w d) a E j r := by
  classical
  apply coefficientRowExact_of_independent_products _ _ _ _ _ hpairs
  intro u b p hu hb hp hrel
  have hu0 (i : I) : u i=0 := by
    have h := hu i
    rw [coefficientComponentSpace_above w hw hr] at h
    exact h
  have hne (i : I) : j i≠r := by have := hj i; omega
  have hp0 : p=0 := by simpa only [hu0,mul_zero,Finset.sum_const_zero,hne,ite_false,zero_add] using hrel
  refine ⟨0,?_,?_,?_,hp0⟩
  · intros; rfl
  · intro i
    simp [matrixCombination,hu0 i]
  · intro i hi
    exact False.elim (hne i hi)

end Froberg
