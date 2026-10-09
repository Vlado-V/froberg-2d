module

public import Froberg.MixedRowComponents

@[expose] public section

/-! Finite weighted-component decompositions of ordinary homogeneous forms.
The variable weights may be zero; weights at most one suffice. -/
noncomputable section
namespace Froberg
open MvPolynomial Finset
variable {K σ : Type*} [Field K]

/-- Zero-one weights never exceed the ordinary monomial degree. -/
theorem weight_le_degree (w : σ → ℕ) (hw : ∀ x,w x≤1) (a : σ →₀ ℕ) :
    Finsupp.weight w a≤a.degree := by
  simp only [Finsupp.weight_apply,Finsupp.degree_apply,Finsupp.sum,smul_eq_mul]
  apply sum_le_sum
  intro x hx
  simpa only [mul_one] using Nat.mul_le_mul_left (a x) (hw x)

/-- Weighted extraction preserves the ordinary homogeneous degree. -/
theorem weightedComponent_preserves_homogeneous (w : σ → ℕ)
    {f : MvPolynomial σ K} {d : ℕ} (hf : f.IsHomogeneous d) (t : ℕ) :
    (weightedHomogeneousComponent w t f).IsHomogeneous d := by
  intro a ha
  rw [coeff_weightedHomogeneousComponent] at ha
  split_ifs at ha with h
  · exact hf ha
  · exact False.elim (ha rfl)

/-- A homogeneous form has no components above its degree when every
variable weight is at most one. -/
theorem weightedComponent_above_homogeneous (w : σ → ℕ) (hw : ∀ x,w x≤1)
    {f : MvPolynomial σ K} {d : ℕ} (hf : f.IsHomogeneous d) {t : ℕ} (ht : d<t) :
    weightedHomogeneousComponent w t f=0 := by
  apply weightedHomogeneousComponent_eq_zero'
  intro a ha
  have hdegree := hf (mem_support_iff.mp ha)
  have hle := weight_le_degree w hw a
  have hdeg : a.degree=d := by
    simpa only [Finsupp.degree_eq_weight_one,Pi.one_def] using hdegree
  omega

/-- A homogeneous form is its scalar component plus finitely many positive
weighted components, without requiring positive variable weights. -/
theorem homogeneous_eq_weightedComponents (w : σ → ℕ) (hw : ∀ x,w x≤1)
    {f : MvPolynomial σ K} {d : ℕ} (hf : f.IsHomogeneous d) :
    f=weightedHomogeneousComponent w 0 f +
      ∑ t∈range d,weightedHomogeneousComponent w (t+1) f := by
  classical
  have hs : (∑ t∈range (d+1),weightedHomogeneousComponent w t f)=f := by
    ext a
    simp only [coeff_sum,coeff_weightedHomogeneousComponent]
    by_cases ha : f.coeff a=0
    · simp [ha]
    · have hdegree := hf ha
      have hdeg : a.degree=d := by
        simpa only [Finsupp.degree_eq_weight_one,Pi.one_def] using hdegree
      have hle := weight_le_degree w hw a
      have hmem : Finsupp.weight w a∈range (d+1) := mem_range.mpr (by omega)
      rw [sum_eq_single (Finsupp.weight w a)]
      · simp
      · intro t ht hne
        exact if_neg (Ne.symm hne)
      · exact fun h => False.elim (h hmem)
  rw [sum_range_succ'] at hs
  simpa only [add_comm] using hs.symm

end Froberg
