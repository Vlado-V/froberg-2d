import Froberg.ProductCapacityParameters
import Froberg.PreparedFiniteRows
import Froberg.SmallSparseLayerBudget
import Froberg.ParityProfileScalar

/-! Instantiation of the higher B.4 capacity records with the literal
Section 5 counts and the complete scalar list of the prepared family. -/
noncomputable section
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial Filter
open Quartic.PolynomialBilinearCoordinates
open scoped Topology
variable {K : Type} [Field K] [Infinite K]
variable {X : Type*} [AddCommGroup X] [Module K X] [Module.Finite K X]

theorem targetLayerLabel_count_limit {d : ℕ} (hd : 3≤d) (h extra : ℕ)
    (e : ℕ → ℕ)
    (he : ∀ᶠ n : ℕ in atTop,(e n : ℝ)<countBeta d*(h : ℝ)^2*(n : ℝ)^(d-2)) :
    Tendsto (fun n : ℕ =>
      (Fintype.card (Label (upperCount n d) (activeEvenIndices d)
        (targetLayerCount d h n (e n+extra))) : ℝ)/(n : ℝ)^d)
      atTop (𝓝 (criticalRatio d/(d.factorial : ℝ))) := by
  have hlim := preparedScalarCount_normalized_limit hd h extra e he
  convert hlim using 1
  funext n
  rw [←preparedScalarCount_eq_card hd]
  congr 2
  unfold preparedScalarCount
  omega

theorem eventually_higher_row_capacity {d R : ℕ} (hd : 9≤d)
    (hR : R∈activeHigherIndices d) :
    ∀ᶠ w : ℕ in atTop,
      ∀ (T : ℕ → MvPolynomial (Fin w × Bool) K →ₗ[K] X),
      finrank K X=deletedTargetCount d (2*w) → T R=0 →
      ∀ (extra : ℕ) (e : ℕ → ℕ),
      (∀ᶠ n : ℕ in atTop,(e n : ℝ)<countBeta d*(2*(w : ℝ))^2*(n : ℝ)^(d-2)) →
      ∀ᶠ v : ℕ in atTop,
        HigherRowCapacity w v d (upperCount (v+v) d)
          (sparseBlockCount ((101/100 : ℝ)*higherCountGamma d R) R (d-R) w)
          (activeEvenIndices d) (targetLayerCount d (2*w) (v+v) (e (v+v)+extra)) T
          ⟨R,(Finset.mem_filter.mp hR).1⟩ := by
  have hR4 := (Finset.mem_filter.mp hR).2
  have hRbounds := activeEvenIndices_bounds (by omega : 3≤d) (Finset.mem_filter.mp hR).1
  filter_upwards [eventually_higher_sparse_layer_budget_all (by omega : 3≤d) hR,
    eventually_product_row_capacities (K := K) (X := X) hd,
    eventually_gt_atTop (0 : ℕ)] with w hsparse hprod hw
  intro T hX hTR extra e he
  let r := fun n => Fintype.card (Label (upperCount n d) (activeEvenIndices d)
    (targetLayerCount d (2*w) n (e n+extra)))
  have hr := targetLayerLabel_count_limit (by omega : 3≤d) (2*w) extra e
    (by simpa only [Nat.cast_mul,Nat.cast_ofNat] using he)
  have hbudget := tendsto_twice_nat.eventually (hsparse.2.2 r hr)
  have he' := tendsto_twice_nat.eventually he
  obtain ⟨n₀,hn₀⟩ := eventually_generic_profile_scalar_separation (K := K) hd
    (show d-R+4≤d by omega) r hr
  filter_upwards [hbudget,hprod extra,he',eventually_gt_atTop (0 : ℕ),
    eventually_ge_atTop n₀] with v hbudget hprod hev hv hvlarge
  have hprod' := hprod (e (2*v))
    (by simpa only [Nat.cast_mul,Nat.cast_ofNat] using hev) hX R
  have hscalar := hn₀ (v+v) (by omega) (balancedScalarHalf v)
    (by simp only [balancedScalarHalf_card,balancedScalarHalf_compl_card]; omega)
    (by simp only [balancedScalarHalf_card,balancedScalarHalf_compl_card];omega)
    (d%2) (Nat.mod_lt d (by decide)) (2*((d-R/2)/2))
  obtain ⟨D,hD,hgood⟩ := hscalar
  refine { hw := hw
           hv := hv
           positive := fun j hj => by have := (activeEvenIndices_bounds (by omega) hj).1;omega
           even := fun j hj => (activeEvenIndices_bounds (by omega) hj).2.2
           degree := fun j hj => (activeEvenIndices_bounds (by omega) hj).2.1.le
           new_unconstrained := hTR
           diagonal := ?_
           cross := ?_
           output_positive := hsparse.1
           enough_generators := ?_
           divisor_capacity := hsparse.2.1
           incidence := ?_
           scalar_open := ⟨D,hD,fun Q hQ => (hgood Q hQ).1⟩ }
  · simpa only [two_mul] using hprod'.diagonal
  · simpa only [two_mul] using hprod'.cross
  · simpa only [targetLayerCount,if_neg (show R≠2 by omega),two_mul] using hbudget.1
  · simpa only [r,two_mul] using hbudget.2

end Froberg.PreparedParameters
