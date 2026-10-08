import Froberg.ShiftedPreparedCapacities
import Froberg.UniformShiftedProductCapacity

/-! The output target module can depend on the chosen output dimension. All
thresholds precede its selection, avoiding a fixed-rank asymptotic premise. -/
noncomputable section
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial Filter
open Quartic.PolynomialBilinearCoordinates
open scoped Topology
variable {K : Type} [Field K] [Infinite K]

/-- The block count is fixed before the scalar-variable shift is chosen. -/
theorem eventually_actual_even_capacities_shift_uniform {d : ℕ} (hd : 9≤d) :
    ∀ᶠ w : ℕ in atTop,
      ∀ (X : Type*) [AddCommGroup X] [Module K X] [Module.Finite K X],
      ∀ T : ℕ → MvPolynomial (Fin w × Bool) K →ₗ[K] X,
      finrank K X=deletedTargetCount d (2*w) →
      finrank K (constrainedOutputs T 2)=quadraticOutputDimension d (2*w) →
      (∀ R,4≤R → T R=0) →
      ∀ (z extra : ℕ) (e : ℕ → ℕ),
      (∀ᶠ n : ℕ in atTop,(e n : ℝ)<countBeta d*(2*(w : ℝ))^2*(n : ℝ)^(d-2)) →
      ∀ᶠ v : ℕ in atTop,
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
  filter_upwards [hhigh,hpos,eventually_allEven_product_capacities_shift_uniform (K := K) hd,
    tendsto_twice_nat.eventually (eventually_quadratic_capacity_shift (K := K) (by omega : 3≤d))]
    with w hhigher hpos hproduct hquadratic
  intro X _ _ _ T hX hO hT z extra e he
  have hecast : ∀ᶠ n : ℕ in atTop,(e n : ℝ)<countBeta d*((2*w : ℕ):ℝ)^2*(n:ℝ)^(d-2) := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using he
  let q : ℕ → ℕ := fun n => upperCount (n+z) d
  let counts : ℕ → ℕ → ℕ := fun n => allEvenCount d (2*w) (n+z) (e (n+z)+extra)
  let r := fun n => Fintype.card (Label (q n) (allEvenIndices d) (counts n))
  have hcount : Tendsto (fun n : ℕ => (r n : ℝ)/(n : ℝ)^d) atTop
      (𝓝 (criticalRatio d/(d.factorial : ℝ))) :=
    allEvenLabel_count_limit_shift (by omega) (2*w) extra z e hecast
  have hp : ∀ᶠ v : ℕ in atTop,∀ R,ProductRowCapacity (K := K) (X := X) w v d R
      (allEvenIndices d) (counts (v+v)) := by
    filter_upwards [hproduct z extra,
      tendsto_twice_nat.eventually ((tendsto_add_atTop_nat z).eventually he)] with v hv hev
    simpa only [counts,two_mul] using hv X (e (2*v+z)) hev hX
  have hq0 := tendsto_twice_nat.eventually
    (hquadratic (Fin w × Bool) (constrainedOutputs T) hO (allEvenIndices d) q counts hcount z extra)
  have hq : ∀ᶠ v : ℕ in atTop,QuadraticRowCapacity (v+v) d (q (v+v))
      (fullSparseBlockCount (countBeta d) 2 (d-2) (2*w)) (allEvenIndices d)
      (counts (v+v)) (constrainedOutputs T) := by
    filter_upwards [hq0,tendsto_twice_nat.eventually ((tendsto_add_atTop_nat z).eventually hecast)]
      with v hv hev
    have hb : e (2*v+z)≤⌈countBeta d*((2*w : ℕ):ℝ)^2*((2*v+z : ℕ):ℝ)^(d-2)⌉₊ := by
      exact_mod_cast hev.le.trans (Nat.le_ceil _)
    have hc : counts (2*v) 2≤⌈countBeta d*((2*w : ℕ):ℝ)^2*((2*v+z : ℕ):ℝ)^(d-2)⌉₊+extra := by
      simpa only [counts,allEvenCount_active _ _ _ (two_mem_activeEvenIndices (d := d) (by omega)),
        targetLayerCount,ite_true] using Nat.add_le_add_right hb extra
    simpa only [two_mul] using hv hc
  have hRcap (R : allEvenIndices d) (hR2 : R.val≠2) :
      ∀ᶠ v : ℕ in atTop,HigherRowCapacity w v d (q (v+v))
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
      obtain ⟨n₀,hn₀⟩ := eventually_generic_profile_scalar_separation (K := K) hd
        (show d-R.val+4≤d by omega) r hcount
      filter_upwards [hbudget,hcover,hp,eventually_ge_atTop n₀] with v hb hc hprod hv
      obtain ⟨D,hD,hgood⟩ := hn₀ (v+v) (by omega) (balancedScalarHalf v)
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
      have hempty := eventually_empty_higher_capacity (K := K) (X := X) hd (allEvenIndices d) R
        hR4 hRd T (hT _ hR4) (hpos R) q counts
        (fun n => allEvenCount_inactive _ _ _ ha) hcount
      filter_upwards [hempty,hp] with v hv hpv
      exact hv (hpv R.val) (fun j hj => by have := (mem_allEvenIndices.mp hj).1;omega)
  filter_upwards [hq,hp,eventually_all.mpr (fun R : {R : allEvenIndices d // R.val≠2} =>
    hRcap R.val R.property)] with v hqv hpv hRv
  exact ⟨hqv,(fun R hR => hRv ⟨R,hR⟩),hpv⟩

end Froberg.PreparedParameters
