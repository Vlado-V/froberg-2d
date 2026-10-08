import Froberg.OddSplitElimination

/-! Exact finite even-weight decomposition in odd ordinary degree. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg
open MvPolynomial Finset
variable {K σ : Type*} [Field K] {d : ℕ}

theorem even_homogeneous_components (w : σ → ℕ) (hw : ∀ x,w x≤1)
    (hd : Odd d) (f : MvPolynomial σ K) (hf : f.IsHomogeneous d)
    (heven : ∀ a,f.coeff a≠0 → Finsupp.weight w a%2=0) :
    f=weightedHomogeneousComponent w 0 f+
      ∑ r : Fin ((d-1)/2),weightedHomogeneousComponent w (2*(r.val+1)) f := by
  classical
  ext a
  simp only [AddMonoidAlgebra.coeff_add,Finsupp.add_apply,coeff_sum,coeff_weightedHomogeneousComponent]
  by_cases ha : f.coeff a=0
  · simp [ha]
  have hdeg : a.degree=d := by
    simpa only [Finsupp.degree_eq_weight_one,Pi.one_def] using hf ha
  have hbound : Finsupp.weight w a≤d := by
    simpa only [hdeg] using weight_le_degree w hw a
  have hpar := heven a ha
  have hodd : d%2=1 := Nat.odd_iff.mp hd
  by_cases hz : Finsupp.weight w a=0
  · rw [if_pos hz]
    have hs : (∑ r : Fin ((d-1)/2),if Finsupp.weight w a=2*(r.val+1) then f.coeff a else 0)=0 := by
      apply sum_eq_zero
      intro r _
      rw [if_neg (by omega)]
    rw [hs,add_zero]
  · rw [if_neg hz,zero_add]
    let r : Fin ((d-1)/2) := ⟨Finsupp.weight w a/2-1,by omega⟩
    have hr : Finsupp.weight w a=2*(r.val+1) := by dsimp [r]; omega
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
