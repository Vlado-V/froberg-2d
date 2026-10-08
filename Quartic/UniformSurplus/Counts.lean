import Quartic.UniformSurplus.Scaling
import Quartic.UniformScalar
import Quartic.ShadowArithmetic
import Quartic.SharpCertificate.Expression

/-! Source binomial parameters and canonical endpoint instances of the
uniform numerical profile inequality. -/
namespace Quartic.UniformSurplus
open Quartic.Counts Quartic.UniformEndpoint
noncomputable section

/-- The sharp shadow already formalized for the finite certificates agrees
with the arithmetic shadow used in the convolution theorem. -/
theorem coreShadow_eq (c i : ℕ) :
    SharpCertificate.coreShadow c i=ShadowArithmetic.shadow (ProfileCertificate.coreP c) i := by
  simp only [SharpCertificate.coreShadow, ProfileCertificate.coreB,
    FiniteCounts.quadratics_eq_b2, b2, ShadowArithmetic.shadow]

theorem core_shadow_linear (c i : ℕ) (hc : 4 ≤ c) (hi : i ≤ ProfileCertificate.coreA c) :
    (ProfileCertificate.coreB c:ℝ)*(i:ℝ)/(ProfileCertificate.coreA c:ℝ) ≤
      (SharpCertificate.coreShadow c i:ℝ) := by
  have hp : 0 < ProfileCertificate.coreP c := by unfold ProfileCertificate.coreP; omega
  have hpr : 0 < (ProfileCertificate.coreP c:ℝ) := by exact_mod_cast hp
  have h := ShadowArithmetic.shadow_linear_bound (ProfileCertificate.coreP c) i hi
  have hr : ((ProfileCertificate.coreP c:ℝ)+1)*(i:ℝ) ≤
      4*(SharpCertificate.coreShadow c i:ℝ) := by
    rw [coreShadow_eq]
    exact_mod_cast h
  have heq : (ProfileCertificate.coreB c:ℝ)*(i:ℝ)/(ProfileCertificate.coreA c:ℝ)=
      ((ProfileCertificate.coreP c:ℝ)+1)*(i:ℝ)/4 := by
    simp only [ProfileCertificate.coreB, FiniteCounts.quadratics_eq_b2,
      UniformScalar.b2_cast, ProfileCertificate.coreA, Nat.cast_mul, Nat.cast_ofNat]
    field_simp
    ring
  rw [heq]
  linarith

theorem source_core_counts (m c : ℕ) (hc : 4 ≤ c) (hcm : c ≤ m) :
    (ProfileCertificate.coreA c:ℝ)=2*((c:ℝ)-2-1) ∧
    (ProfileCertificate.coreB c:ℝ)=((c:ℝ)-2)*((c:ℝ)-2-1)/2 ∧
    (ProfileCertificate.freeW m c:ℝ)=(m:ℝ)-((c:ℝ)-2) := by
  have hp : (ProfileCertificate.coreP c:ℝ)=(c:ℝ)-3 := by
    simp only [ProfileCertificate.coreP, Nat.cast_sub (by omega : 3 ≤ c), Nat.cast_ofNat]
  refine ⟨?_,?_,?_⟩
  · simp only [ProfileCertificate.coreA, Nat.cast_mul, Nat.cast_ofNat, hp]
    ring
  · simp only [ProfileCertificate.coreB, FiniteCounts.quadratics_eq_b2,
      UniformScalar.b2_cast, hp]
    ring
  · simp only [ProfileCertificate.freeW, Nat.cast_add, Nat.cast_sub hcm, Nat.cast_ofNat]
    ring

theorem source_total (m c : ℕ) :
    (ProfileCertificate.totalA m c:ℝ)=
      (ProfileCertificate.coreA c:ℝ)+3*(ProfileCertificate.freeW m c:ℝ) := by
  simp [ProfileCertificate.totalA]

theorem target_total (m : ℕ) (hm : 320 ≤ m) (upper : Bool) :
    totalReal (ProfileCertificate.coreA (mixedCount m upper))
      (ProfileCertificate.coreB (mixedCount m upper)) (ProfileCertificate.freeW m (mixedCount m upper))=
      (UniformScalar.targetCount m (mixedCount m upper):ℝ) := by
  have h := UniformScalar.target_count_eq_free m hm upper
  dsimp only at h
  have hr : (UniformScalar.targetCount m (mixedCount m upper):ℝ)=
      (ProfileCertificate.coreB (mixedCount m upper):ℝ)*(ProfileCertificate.freeW m (mixedCount m upper):ℝ)+
      (ProfileCertificate.coreA (mixedCount m upper):ℝ)*(b2 (ProfileCertificate.freeW m (mixedCount m upper)):ℝ)+
      3*(b3 (ProfileCertificate.freeW m (mixedCount m upper)):ℝ) := by exact_mod_cast h
  rw [UniformScalar.b2_cast,UniformScalar.b3_cast] at hr
  exact hr.symm

/-- The manuscript's sharp real profile, with all original integer counts. -/
def sourceSharp (m c i : ℕ) (n₁ n₂ n₃ : ℝ) : ℝ :=
  sharpReal (ProfileCertificate.coreA c) (ProfileCertificate.coreB c)
    (ProfileCertificate.freeW m c) (SharpCertificate.coreShadow c i) i n₁ n₂ n₃

/-- Every real sharp profile satisfies `sc:uniform-surplus` for every actual
endpoint configuration with `m≥320`. There is no remaining interpolation
hypothesis in this numerical statement. -/
theorem source_uniform_surplus (m : ℕ) (hm : 320 ≤ m) (upper : Bool)
    (i : ℕ) (hi : i ≤ ProfileCertificate.coreA (mixedCount m upper))
    (n₁ n₂ n₃ : ℝ)
    (hn : 0 ≤ n₃ ∧ n₃ ≤ n₂ ∧ n₂ ≤ n₁ ∧ n₁ ≤ (ProfileCertificate.freeW m (mixedCount m upper):ℝ)) :
    let c := mixedCount m upper
    let d := (i:ℝ)+n₁+n₂+n₃
    (UniformScalar.targetCount m c:ℝ)/(ProfileCertificate.totalA m c:ℝ)*d+
      (m:ℝ)^2/100*min d ((ProfileCertificate.totalA m c:ℝ)-d) ≤ sourceSharp m c i n₁ n₂ n₃ := by
  have hc := UniformScalar.c_range m hm upper
  have hcounts := source_core_counts m (mixedCount m upper) hc.1 hc.2
  have ht := core_count_bounds m hm upper
  rw [coreVariables_eq_mixed_sub_two] at ht
  have htlo : (m:ℝ)/2 ≤ (mixedCount m upper:ℝ)-2 := by
    simpa only [Nat.cast_sub (by omega : 2 ≤ mixedCount m upper), Nat.cast_ofNat] using ht.1
  have hthi : (mixedCount m upper:ℝ)-2 ≤ 14*(m:ℝ)/25 := by
    have h := ht.2
    simp only [Nat.cast_sub (by omega : 2 ≤ mixedCount m upper), Nat.cast_ofNat] at h
    linarith
  have h := sharp_real_surplus (m:ℝ) ((mixedCount m upper:ℝ)-2)
    (ProfileCertificate.coreA (mixedCount m upper)) (ProfileCertificate.coreB (mixedCount m upper))
    (ProfileCertificate.freeW m (mixedCount m upper)) (SharpCertificate.coreShadow (mixedCount m upper) i)
    i n₁ n₂ n₃ (by exact_mod_cast (show 64 ≤ m by omega)) htlo hthi
    hcounts.1 hcounts.2.1 hcounts.2.2 (by positivity) (by exact_mod_cast hi) hn
    (core_shadow_linear (mixedCount m upper) i hc.1 hi)
  rw [target_total m hm upper,←source_total m (mixedCount m upper)] at h
  exact h

end
end Quartic.UniformSurplus
