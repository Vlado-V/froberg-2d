module

public import Froberg.OddSplitElimination

@[expose] public section

/-! Natural-weight parity is a linear condition, including in characteristic two. -/
noncomputable section
namespace Froberg
open MvPolynomial
variable {K σ : Type*} [Field K]

def weightedParitySpace (w : σ → ℕ) (p : ℕ) : Submodule K (MvPolynomial σ K) where
  carrier := {f | ∀ a,Finsupp.weight w a%2≠p → f.coeff a=0}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg a ha
    change f.coeff a + g.coeff a=0
    rw [hf a ha,hg a ha,add_zero]
  smul_mem' := by
    intro c f hf a ha
    simp only [coeff_smul,hf a ha,smul_zero]

theorem mem_weightedParitySpace_iff (w : σ → ℕ) (p : ℕ) (f : MvPolynomial σ K) :
    f∈weightedParitySpace w p ↔ ∀ a,f.coeff a≠0 → Finsupp.weight w a%2=p := by
  constructor
  · intro hf a ha
    by_contra h
    exact ha (hf a h)
  · intro hf a ha
    by_contra h
    exact ha (hf a h)

theorem IsWeightedHomogeneous.mem_parity {w : σ → ℕ} {f : MvPolynomial σ K}
    {j p : ℕ} (hf : f.IsWeightedHomogeneous w j) (hj : j%2=p) :
    f∈weightedParitySpace w p := by
  rw [mem_weightedParitySpace_iff]
  intro a ha
  rw [hf ha,hj]

end Froberg
