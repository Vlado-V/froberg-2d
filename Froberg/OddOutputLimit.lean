module

public import Froberg.OddOutputSpace
public import Froberg.ScalarSeparationAsymptotic

@[expose] public section

/-! The actual odd-half output space occupies asymptotically one half of
the homogeneous output space. -/
noncomputable section
namespace Froberg
open Filter Finset
open scoped Topology

theorem oddOutputProfile_choose_sum {R : ℕ} (hR : 0<R) :
    ∑ a : OddOutputProfile R, R.choose a.val.val = 2^(R-1) := by
  rw [← parity_binomial_mass hR 0 0 (by omega)]
  apply sum_bij (fun a _ => a.val.val)
  · intro a ha
    have har := a.val.isLt
    have hap := a.property
    simp only [parityBinomialIndices,mem_filter,mem_range,zero_add]
    exact ⟨har,by omega⟩
  · intro a ha b hb hab
    exact Subtype.ext (Fin.ext hab)
  · intro a ha
    obtain ⟨har,hap⟩ := mem_filter.mp ha
    simp only [mem_range] at har
    refine ⟨⟨⟨a,har⟩,?_⟩,mem_univ _,rfl⟩
    simp only [zero_add] at hap
    change a%2=1
    omega
  · intro a ha
    rfl

private theorem oddOutput_factorial_identity {R a : ℕ} (ha : a≤R) :
    (a.factorial : ℝ)⁻¹*((R-a).factorial : ℝ)⁻¹ = (R.choose a : ℝ)/(R.factorial : ℝ) := by
  have hR : (R.factorial : ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero R
  have ha' : (a.factorial : ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero a
  have hb : ((R-a).factorial : ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero (R-a)
  have hfac : (R.choose a : ℝ)*a.factorial*(R-a).factorial=R.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial ha
  field_simp [hR,ha',hb]
  nlinarith [hfac]

theorem oddOutputDimension_normalized_limit {R : ℕ} (hR : 0<R) :
    Tendsto (fun w : ℕ => (oddOutputDimension w R : ℝ)/(w : ℝ)^R)
      atTop (𝓝 ((2 : ℝ)^(R-1)/(R.factorial : ℝ))) := by
  have hprofile (a : OddOutputProfile R) :
      Tendsto (fun w : ℕ => ((w+a.val.val-1).choose a.val.val : ℝ)*
        ((w+(R-a.val.val)-1).choose (R-a.val.val) : ℝ)/(w : ℝ)^R)
        atTop (𝓝 ((R.choose a.val.val : ℝ)/(R.factorial : ℝ))) := by
    have ha : a.val.val≤R := by have := a.val.isLt; omega
    have ht := (monomial_count_normalized_tendsto a.val.val).mul
      (monomial_count_normalized_tendsto (R-a.val.val))
    rw [oddOutput_factorial_identity ha] at ht
    simpa only [div_mul_div_comm,← pow_add,Nat.add_sub_of_le ha] using ht
  have ht := tendsto_finsetSum univ (fun a _ => hprofile a)
  have hsum : ∑ a : OddOutputProfile R, (R.choose a.val.val : ℝ)/(R.factorial : ℝ) =
      (2 : ℝ)^(R-1)/(R.factorial : ℝ) := by
    rw [← sum_div]
    congr 1
    exact_mod_cast oddOutputProfile_choose_sum hR
  rw [hsum] at ht
  apply ht.congr'
  exact Eventually.of_forall fun w => by simp [oddOutputDimension,← sum_div]

/-- In terms of the full output-variable count 2w, the leading coefficient
is exactly 1/(2 R!). -/
theorem oddOutputDimension_full_normalized_limit {R : ℕ} (hR : 0<R) :
    Tendsto (fun w : ℕ => (oddOutputDimension w R : ℝ)/(2*(w : ℝ))^R)
      atTop (𝓝 (1/(2*(R.factorial : ℝ)))) := by
  have ht := (oddOutputDimension_normalized_limit hR).div_const ((2 : ℝ)^R)
  have hp : (2 : ℝ)^R=2^(R-1)*2 := by rw [← pow_succ,Nat.sub_add_cancel hR]
  have hc : ((2 : ℝ)^(R-1)/(R.factorial : ℝ))/2^R=1/(2*(R.factorial : ℝ)) := by
    rw [hp]
    field_simp
  rw [hc] at ht
  apply ht.congr'
  exact Eventually.of_forall fun w => by dsimp only; rw [mul_pow]; ring

end Froberg
