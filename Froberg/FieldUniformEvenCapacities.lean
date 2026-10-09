module

public import Froberg.UniformShiftedPreparedCapacities
public import Froberg.FieldUniformScalarProfiles
public import Froberg.FieldUniformQuadraticCapacity
public import Froberg.FieldUniformProductCapacity

@[expose] public section

/-! Numerical capacity thresholds that precede the choice of any infinite field. -/
noncomputable section
set_option maxHeartbeats 800000
universe u
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial Filter
open Quartic.PolynomialBilinearCoordinates
open scoped Topology

theorem eventually_field_uniform_empty_higher_capacity {w d : ℕ} (hd : 9≤d)
    (J : Finset ℕ) (R : J) (hR : 4≤R.val) (hRd : R.val≤d)
    (hH : 0<oddOutputDimension w R.val)
    (q : ℕ → ℕ) (counts : ℕ → ℕ → ℕ)
    (hzero : ∀ n,counts n R.val=0)
    (hr : Tendsto (fun n : ℕ => (Fintype.card (Label (q n) J (counts n)) : ℝ)/(n : ℝ)^d)
      atTop (𝓝 (criticalRatio d/(d.factorial : ℝ)))) :
    ∀ᶠ v : ℕ in atTop,
      ∀ (K : Type) [Field K] [Infinite K],
      ∀ (X : Type u) [AddCommGroup X] [Module K X] [Module.Finite K X],
      ∀ (T : ℕ → MvPolynomial (Fin w × Bool) K →ₗ[K] X), T R.val=0 →
      ProductRowCapacity (K := K) (X := X) w v d R.val J (counts (v+v)) →
      (∀ j∈J,0<j) →
      HigherRowCapacity w v d (q (v+v)) 0 J (counts (v+v)) T R := by
  let r := fun n => Fintype.card (Label (q n) J (counts n))
  have hratio : (((d-R.val)+d).choose (d-R.val) : ℝ)*criticalRatio d<1 := by
    have hb := higher_scalar_source_bound hR hRd
    have he : 2*d-R.val=(d-R.val)+d := by omega
    simpa only [scalarCapacityBinomial,he] using hb.trans (by norm_num : (1/8 : ℝ)<1)
  have hgap : (0 : ℝ)+(oddOutputDimension w R.val : ℝ)*
      (((d-R.val)+d).choose (d-R.val) : ℝ)*criticalRatio d<oddOutputDimension w R.val := by
    have hp : (0 : ℝ)<oddOutputDimension w R.val := by exact_mod_cast hH
    nlinarith
  have hbudget := eventually_intermediate_scalar_budget (by omega : d-R.val<d)
    (Nat.zero_le (oddOutputDimension w R.val)) r hr (by simpa only [Nat.cast_zero] using hgap)
  obtain ⟨n₀,hn₀⟩ := eventually_field_uniform_generic_profile_scalar_separation hd
    (show d-R.val+4≤d by omega) r hr
  obtain ⟨n₁,hn₁⟩ := eventually_atTop.mp hbudget
  filter_upwards [eventually_ge_atTop (max n₀ n₁)] with v hv
  intro K _ _ X _ _ _ T hTR hp hpositive
  obtain ⟨D,hD,hgood⟩ := hn₀ (v+v) (by omega) K (balancedScalarHalf v)
    (by simp only [balancedScalarHalf_card,balancedScalarHalf_compl_card]; omega)
    (by simp only [balancedScalarHalf_card,balancedScalarHalf_compl_card];omega)
    (d%2) (Nat.mod_lt d (by decide)) (2*((d-R.val/2)/2))
  exact { hw := hp.positive_output
          hv := hp.positive_scalar
          positive := hpositive
          even := hp.even_degrees
          degree := hp.bounded_degrees
          new_unconstrained := hTR
          diagonal := hp.diagonal
          cross := hp.cross
          output_positive := hH
          enough_generators := by rw [hzero];simp
          divisor_capacity := by simp
          incidence := by simpa only [zero_mul,Nat.sub_zero,r] using hn₁ (v+v) (by omega)
          scalar_open := ⟨D,hD,fun Q hQ => (hgood Q hQ).1⟩ }


theorem eventually_field_uniform_actual_even_capacities_shift {d : ℕ} (hd : 9≤d) :
    ∀ᶠ w : ℕ in atTop,
      ∀ (z extra : ℕ) (e : ℕ → ℕ),
      (∀ᶠ n : ℕ in atTop,(e n : ℝ)<countBeta d*(2*(w : ℝ))^2*(n : ℝ)^(d-2)) →
      ∀ᶠ v : ℕ in atTop,
      ∀ (K : Type) [Field K] [Infinite K],
      ∀ (X : Type u) [AddCommGroup X] [Module K X] [Module.Finite K X],
      ∀ T : ℕ → MvPolynomial (Fin w × Bool) K →ₗ[K] X,
      finrank K X=deletedTargetCount d (2*w) →
      finrank K (constrainedOutputs T 2)=quadraticOutputDimension d (2*w) →
      (∀ R,4≤R → T R=0) →
        QuadraticRowCapacity (v+v) d (upperCount (v+v+z) d)
          (fullSparseBlockCount (countBeta d) 2 (d-2) (2*w)) (allEvenIndices d)
          (allEvenCount d (2*w) (v+v+z) (e (v+v+z)+extra)) (constrainedOutputs T) ∧
        (∀ R : allEvenIndices d,R.val≠2 →
          HigherRowCapacity w v d (upperCount (v+v+z) d)
            (if R.val∈activeEvenIndices d then
              sparseBlockCount ((101/100 : ℝ)*higherCountGamma d R.val) R.val (d-R.val) w else 0)
            (allEvenIndices d) (allEvenCount d (2*w) (v+v+z) (e (v+v+z)+extra)) T R) ∧
        ∀ R,ProductRowCapacity (K := K) (X := X) w v d R (allEvenIndices d)
          (allEvenCount d (2*w) (v+v+z) (e (v+v+z)+extra)) := by
  have hhigh : ∀ᶠ w : ℕ in atTop,∀ R : activeHigherIndices d,
      let b := sparseBlockCount ((101/100 : ℝ)*higherCountGamma d R.val) R.val (d-R.val) w
      let H := oddOutputDimension w R.val
      0<H ∧ b*(d-R.val+d).choose (d-R.val)≤H ∧
      ∀ q : ℕ → ℕ,
        Tendsto (fun n : ℕ => (q n : ℝ)/(n : ℝ)^d) atTop
          (𝓝 (criticalRatio d/(d.factorial : ℝ))) →
        ∀ᶠ n : ℕ in atTop,
          higherGeneratorCount d (2*w) n R.val≤b*(n+(d-R.val)-1).choose (d-R.val) ∧
          H*(d-R.val+d).choose (d-R.val)*
            (q n+H*(n+(d-R.val)-1).choose (d-R.val)+
              (H*2^H)*(n+(d-1)-1).choose (d-1))≤
              (H-b*(d-R.val+d).choose (d-R.val))*(n+(d-R.val)+d-1).choose d :=
    eventually_all.mpr fun R => eventually_higher_sparse_layer_budget hd R.property
  have hpos : ∀ᶠ w : ℕ in atTop,∀ R : allEvenIndices d,0<oddOutputDimension w R.val :=
    eventually_all.mpr fun R => oddOutputDimension_eventually_positive
      (by have := (mem_allEvenIndices.mp R.property).1;omega)
  filter_upwards [hhigh,hpos,eventually_field_uniform_allEven_product_capacities_shift hd,
    tendsto_twice_nat.eventually (eventually_field_uniform_quadratic_capacity_shift_late (by omega : 3≤d))]
    with w hhigher hpos hproduct hquadratic
  intro z extra e he
  have hecast : ∀ᶠ n : ℕ in atTop,(e n : ℝ)<countBeta d*((2*w : ℕ):ℝ)^2*(n:ℝ)^(d-2) := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using he
  let q : ℕ → ℕ := fun n => upperCount (n+z) d
  let counts : ℕ → ℕ → ℕ := fun n => allEvenCount d (2*w) (n+z) (e (n+z)+extra)
  let r := fun n => Fintype.card (Label (q n) (allEvenIndices d) (counts n))
  have hcount : Tendsto (fun n : ℕ => (r n : ℝ)/(n : ℝ)^d) atTop
      (𝓝 (criticalRatio d/(d.factorial : ℝ))) :=
    allEvenLabel_count_limit_shift (by omega) (2*w) extra z e hecast
  have hp : ∀ᶠ v : ℕ in atTop,
      ∀ (K : Type) [Field K] [Infinite K],
      ∀ (X : Type u) [AddCommGroup X] [Module K X] [Module.Finite K X],
      finrank K X=deletedTargetCount d (2*w) →
      ∀ R,ProductRowCapacity (K := K) (X := X) w v d R
        (allEvenIndices d) (counts (v+v)) := by
    filter_upwards [hproduct z extra,
      tendsto_twice_nat.eventually ((tendsto_add_atTop_nat z).eventually he)] with v hv hev
    intro K _ _ X _ _ _ hX
    simpa only [counts,two_mul] using hv K X (e (2*v+z)) hev hX
  have hq0 := tendsto_twice_nat.eventually
    (hquadratic (allEvenIndices d) q counts hcount z extra)
  have hq : ∀ᶠ v : ℕ in atTop,
      ∀ (K : Type) [Field K] [Infinite K],
      ∀ (X : Type u) [AddCommGroup X] [Module K X] [Module.Finite K X],
      ∀ T : ℕ → MvPolynomial (Fin w × Bool) K →ₗ[K] X,
      finrank K (constrainedOutputs T 2)=quadraticOutputDimension d (2*w) →
      QuadraticRowCapacity (v+v) d (q (v+v))
        (fullSparseBlockCount (countBeta d) 2 (d-2) (2*w)) (allEvenIndices d)
        (counts (v+v)) (constrainedOutputs T) := by
    filter_upwards [hq0,tendsto_twice_nat.eventually ((tendsto_add_atTop_nat z).eventually hecast)]
      with v hv hev
    intro K _ _ X _ _ _ T hO
    have hb : e (2*v+z)≤⌈countBeta d*((2*w : ℕ):ℝ)^2*((2*v+z : ℕ):ℝ)^(d-2)⌉₊ := by
      exact_mod_cast hev.le.trans (Nat.le_ceil _)
    have hc : counts (2*v) 2≤⌈countBeta d*((2*w : ℕ):ℝ)^2*((2*v+z : ℕ):ℝ)^(d-2)⌉₊+extra := by
      simpa only [counts,allEvenCount_active _ _ _ (two_mem_activeEvenIndices (d := d) (by omega)),
        targetLayerCount,ite_true] using Nat.add_le_add_right hb extra
    simpa only [two_mul] using hv K (Fin w × Bool) (constrainedOutputs T) hO hc
  have hRcap (R : allEvenIndices d) (hR2 : R.val≠2) :
      ∀ᶠ v : ℕ in atTop,
      ∀ (K : Type) [Field K] [Infinite K],
      ∀ (X : Type u) [AddCommGroup X] [Module K X] [Module.Finite K X],
      ∀ T : ℕ → MvPolynomial (Fin w × Bool) K →ₗ[K] X,
      finrank K X=deletedTargetCount d (2*w) →
      (∀ R,4≤R → T R=0) →
      HigherRowCapacity w v d (q (v+v))
        (if R.val∈activeEvenIndices d then
          sparseBlockCount ((101/100 : ℝ)*higherCountGamma d R.val) R.val (d-R.val) w else 0)
        (allEvenIndices d) (counts (v+v)) T R := by
    obtain ⟨hRlow,hRd,hRe⟩ := mem_allEvenIndices.mp R.property
    have hR4 : 4≤R.val := by omega
    by_cases ha : R.val∈activeEvenIndices d
    · rw [if_pos ha]
      have hRa : R.val∈activeHigherIndices d := Finset.mem_filter.mpr ⟨ha,hR4⟩
      have hsparse := hhigher ⟨R.val,hRa⟩
      have hbudget := tendsto_twice_nat.eventually (hsparse.2.2 r hcount)
      have hRlt := (activeEvenIndices_bounds (by omega : 3≤d) ha).2.1
      have hcover := tendsto_twice_nat.eventually
        (sparseBlockCount_eventually_covers_shift_add ((101/100 : ℝ)*higherCountGamma d R.val)
          (mul_nonneg (by norm_num) (higherCountGamma_pos d R.val).le) R.val w z 0 (by omega : 0<d-R.val))
      obtain ⟨n₀,hn₀⟩ := eventually_field_uniform_generic_profile_scalar_separation hd
        (show d-R.val+4≤d by omega) r hcount
      filter_upwards [hbudget,hcover,hp,eventually_ge_atTop n₀] with v hb hc hprod hv
      intro K _ _ X _ _ _ T hX hT
      have hprod := hprod K X hX
      obtain ⟨D,hD,hgood⟩ := hn₀ (v+v) (by omega) K (balancedScalarHalf v)
        (by simp only [balancedScalarHalf_card,balancedScalarHalf_compl_card];omega)
        (by simp only [balancedScalarHalf_card,balancedScalarHalf_compl_card];omega)
        (d%2) (Nat.mod_lt d (by decide)) (2*((d-R.val/2)/2))
      exact { hw := (hprod R.val).positive_output
              hv := (hprod R.val).positive_scalar
              positive := fun j hj => by have := (mem_allEvenIndices.mp hj).1;omega
              even := (hprod R.val).even_degrees
              degree := (hprod R.val).bounded_degrees
              new_unconstrained := hT _ hR4
              diagonal := (hprod R.val).diagonal
              cross := (hprod R.val).cross
              output_positive := hsparse.1
              enough_generators := by
                simpa only [counts,allEvenCount_active _ _ _ ha,targetLayerCount,if_neg hR2,
                  higherGeneratorCount,Nat.cast_mul,Nat.cast_ofNat,Nat.add_zero,two_mul,Nat.cast_add] using hc
              divisor_capacity := hsparse.2.1
              incidence := by simpa only [r,two_mul] using hb.2
              scalar_open := ⟨D,hD,fun Q hQ => (hgood Q hQ).1⟩ }
    · rw [if_neg ha]
      have hempty := eventually_field_uniform_empty_higher_capacity hd (allEvenIndices d) R
        hR4 hRd (hpos R) q counts
        (fun n => allEvenCount_inactive _ _ _ ha) hcount
      filter_upwards [hempty,hp] with v hv hpv
      intro K _ _ X _ _ _ T hX hT
      exact hv K X T (hT _ hR4) (hpv K X hX R.val) (fun j hj => by have := (mem_allEvenIndices.mp hj).1;omega)
  filter_upwards [hq,hp,eventually_all.mpr (fun R : {R : allEvenIndices d // R.val≠2} =>
    hRcap R.val R.property)] with v hqv hpv hRv
  intro K _ _ X _ _ _ T hX hO hT
  exact ⟨hqv K X T hO,(fun R hR => hRv ⟨R,hR⟩ K X T hX hT),hpv K X hX⟩

end Froberg.PreparedParameters
