module

public import Froberg.StrictModelCounts
public import Froberg.ExactOuterLimit
public import Froberg.ProfileCriticalRatio
public import Froberg.UpperEndpointConvolution
public import Froberg.ScalarSeparationAsymptotic

@[expose] public section

/-! Leading dimensions and the lower-order deficit in the outer scalar quotient. -/
noncomputable section
namespace Froberg
open Filter
open scoped Topology

def outerSourceCount (d h b : ℕ) (f : ℕ → ℕ) (n : ℕ) : ℝ :=
  (h : ℝ)*((n+(d-1)-1).choose (d-1) : ℝ)-f n-b

def outerTargetCount (d h b : ℕ) (f : ℕ → ℕ) (n : ℕ) : ℝ :=
  (h : ℝ)*((n+(2*d-1)-1).choose (2*d-1) : ℝ)-((f n : ℝ)+b)*((n+d-1).choose d : ℝ)

lemma critical_outer_balance {d : ℕ} (hd : 2 ≤ d) (h : ℝ) :
    h/((2*d-1).factorial : ℝ)-(h*criticalRatio d/((d-1).factorial : ℝ))/(d.factorial : ℝ)=
      (criticalRatio d/(d.factorial : ℝ))*(h/((d-1).factorial : ℝ)-h*criticalRatio d/((d-1).factorial : ℝ)) := by
  have hH : (centralHalfBinomial d : ℝ) ≠ 0 := by
    have := centralHalfBinomial_ge_two hd
    exact_mod_cast (show centralHalfBinomial d ≠ 0 by omega)
  have hf : (centralHalfBinomial d : ℝ)*((d-1).factorial : ℝ)*(d.factorial : ℝ)=
      ((2*d-1).factorial : ℝ) := by
    have hh := profile_capacity_factorials (d-1)
    rw [profileAmbientCapacity_eq_central] at hh
    simpa only [show d-1+1=d by omega,show 2*(d-1)+1=2*d-1 by omega] using hh
  have hc := criticalRatio_identity hd
  have he : h/((2*d-1).factorial : ℝ)-(h*criticalRatio d/((d-1).factorial : ℝ))/(d.factorial : ℝ)-
      (criticalRatio d/(d.factorial : ℝ))*(h/((d-1).factorial : ℝ)-h*criticalRatio d/((d-1).factorial : ℝ)) =
      h*(1-(centralHalfBinomial d : ℝ)*criticalRatio d*(2-criticalRatio d))/
        ((centralHalfBinomial d : ℝ)*((d-1).factorial : ℝ)*(d.factorial : ℝ)) := by
    rw [← hf]
    field_simp
    <;> ring
  rw [hc,sub_self,mul_zero,zero_div] at he
  linarith

theorem outer_count_limits {d h b : ℕ} (hd : 3 ≤ d) (f : ℕ → ℕ)
    (hf : Tendsto (fun n : ℕ => (f n : ℝ)/(n : ℝ)^(d-1)) atTop
      (𝓝 ((h : ℝ)*criticalRatio d/((d-1).factorial : ℝ)))) :
    Tendsto (fun n : ℕ => outerSourceCount d h b f n/(n : ℝ)^(d-1)) atTop
      (𝓝 ((h : ℝ)/((d-1).factorial : ℝ)-(h : ℝ)*criticalRatio d/((d-1).factorial : ℝ))) ∧
    Tendsto (fun n : ℕ =>
      (outerTargetCount d h b f n-(upperCount n d : ℝ)*outerSourceCount d h b f n)/(n : ℝ)^(2*d-1))
      atTop (𝓝 0) := by
  have hb : Tendsto (fun n : ℕ => (b : ℝ)/(n : ℝ)^(d-1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (nat_power_tendsto_atTop _ (by omega))
  have hbase := (monomial_count_normalized_tendsto (d-1)).const_mul (h : ℝ)
  have hA : Tendsto (fun n : ℕ => outerSourceCount d h b f n/(n : ℝ)^(d-1)) atTop
      (𝓝 ((h : ℝ)/((d-1).factorial : ℝ)-(h : ℝ)*criticalRatio d/((d-1).factorial : ℝ))) := by
    convert (hbase.sub hf).sub hb using 1
    · funext n
      dsimp [outerSourceCount]
      ring
    · simp only [sub_zero,div_eq_mul_inv]
  have hprod := (hf.add hb).mul (monomial_count_normalized_tendsto d)
  simp only [add_zero] at hprod
  have hprod' : Tendsto (fun n : ℕ =>
      (((f n : ℝ)+b)*((n+d-1).choose d : ℝ))/(n : ℝ)^(2*d-1)) atTop
      (𝓝 (((h : ℝ)*criticalRatio d/((d-1).factorial : ℝ))/(d.factorial : ℝ))) := by
    convert hprod using 1
    · funext n
      rw [show 2*d-1=(d-1)+d by omega,pow_add]
      ring
    · rfl
  have hT : Tendsto (fun n : ℕ => outerTargetCount d h b f n/(n : ℝ)^(2*d-1)) atTop
      (𝓝 ((h : ℝ)/((2*d-1).factorial : ℝ)-
        ((h : ℝ)*criticalRatio d/((d-1).factorial : ℝ))/(d.factorial : ℝ))) := by
    convert ((monomial_count_normalized_tendsto (2*d-1)).const_mul (h : ℝ)).sub hprod' using 1
    · funext n
      dsimp [outerTargetCount]
      ring
    · simp only [div_eq_mul_inv]
  have hQA := (upperCount_normalized_limit (by omega : 2 ≤ d)).mul hA
  have hQA' : Tendsto (fun n : ℕ =>
      ((upperCount n d : ℝ)*outerSourceCount d h b f n)/(n : ℝ)^(2*d-1)) atTop
      (𝓝 ((criticalRatio d/(d.factorial : ℝ))*
        ((h : ℝ)/((d-1).factorial : ℝ)-(h : ℝ)*criticalRatio d/((d-1).factorial : ℝ)))) := by
    convert hQA using 1
    funext n
    rw [show 2*d-1=d+(d-1) by omega,pow_add]
    ring
  refine ⟨hA,?_⟩
  have hz := hT.sub hQA'
  rw [critical_outer_balance (by omega : 2 ≤ d),sub_self] at hz
  simpa only [sub_div] using hz

lemma outer_source_leading_pos {d h : ℕ} (hd : 2 ≤ d) (hh : 0 < h) :
    0 < (h : ℝ)/((d-1).factorial : ℝ)-(h : ℝ)*criticalRatio d/((d-1).factorial : ℝ) := by
  have hr := (criticalRatio_bounds hd).2.1
  have he : (h : ℝ)/((d-1).factorial : ℝ)-(h : ℝ)*criticalRatio d/((d-1).factorial : ℝ)=
      (h : ℝ)*(1-criticalRatio d)/((d-1).factorial : ℝ) := by ring
  rw [he]
  exact div_pos (mul_pos (by exact_mod_cast hh) (sub_pos.mpr hr)) (by positivity)

end Froberg
