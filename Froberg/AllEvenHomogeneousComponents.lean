import Froberg.EvenHomogeneousComponents

/-! Exact even-weight decomposition in every ordinary homogeneous degree. -/
noncomputable section
namespace Froberg
open MvPolynomial Finset
variable {K σ : Type*} [Field K] {d : ℕ}

theorem all_even_homogeneous_components (w : σ → ℕ) (hw : ∀ x,w x≤1)
    (f : MvPolynomial σ K) (hf : f.IsHomogeneous d)
    (heven : ∀ a,f.coeff a≠0 → Finsupp.weight w a%2=0) :
    f=∑ r : Fin (d/2+1),weightedHomogeneousComponent w (2*r.val) f := by
  classical
  ext a
  simp only [coeff_sum,coeff_weightedHomogeneousComponent]
  by_cases ha : f.coeff a=0
  · simp [ha]
  have hdeg : a.degree=d := by
    simpa only [Finsupp.degree_eq_weight_one,Pi.one_def] using hf ha
  have hbound : Finsupp.weight w a≤d := by
    simpa only [hdeg] using weight_le_degree w hw a
  have hpar := heven a ha
  let r : Fin (d/2+1) := ⟨Finsupp.weight w a/2,by omega⟩
  have hr : Finsupp.weight w a=2*r.val := by dsimp [r]; omega
  rw [sum_eq_single r]
  · rw [if_pos hr]
  · intro s _ hsr
    rw [if_neg]
    intro hs
    apply hsr
    apply Fin.ext
    omega
  · simp

end Froberg
