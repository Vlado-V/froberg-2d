import Froberg.ParityComplex
import Froberg.PreparedBackground

/-! The ZMod 2 monomial projection agrees exactly with natural-weight
parity conditions used in the prepared-row elimination. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open MvPolynomial
variable {K σ : Type*} [Field K]

lemma weight_natCast_mod_two (w : σ → ℕ) (a : σ →₀ ℕ) :
    Finsupp.weight (fun i => (w i : ZMod 2)) a=(Finsupp.weight w a : ZMod 2) := by
  classical
  simp [Finsupp.weight_apply,Finsupp.sum,nsmul_eq_mul]

/-- Equivalence with the literal support parity used by the background proof. -/
theorem parity_homogeneous_iff (w : σ → ℕ) (f : MvPolynomial σ K)
    (p : ℕ) (hp : p<2) :
    f.IsWeightedHomogeneous (fun i => (w i : ZMod 2)) (p : ZMod 2) ↔
      ∀ a, f.coeff a ≠ 0 → Finsupp.weight w a%2=p := by
  constructor
  · intro hf a ha
    have h := hf ha
    rw [weight_natCast_mod_two,ZMod.natCast_eq_natCast_iff'] at h
    simpa only [Nat.mod_eq_of_lt hp] using h
  · intro hf a ha
    rw [weight_natCast_mod_two,ZMod.natCast_eq_natCast_iff']
    simpa only [Nat.mod_eq_of_lt hp] using hf a ha

/-- An exact natural weight has its corresponding monomial parity. -/
theorem weighted_homogeneous_has_parity (w : σ → ℕ) (f : MvPolynomial σ K)
    {d : ℕ} (hf : f.IsWeightedHomogeneous w d) :
    f.IsWeightedHomogeneous (fun i => (w i : ZMod 2)) (d : ZMod 2) := by
  intro a ha
  rw [weight_natCast_mod_two,hf ha]

end Froberg
