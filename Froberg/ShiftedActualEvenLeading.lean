module

public import Froberg.PreparedActualReduction
public import Froberg.ExtendedLeadingWitnesses
public import Froberg.UniformShiftedPreparedCapacities
public import Froberg.CapacityTargetTransport
public import Froberg.PrivateFrameReference

@[expose] public section

/-! Independent leading components for the actual prescribed row counts,
with output constraints chosen after the scalar threshold. -/
noncomputable section
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial Filter
variable {K : Type} [Field K] [Infinite K]
theorem eventually_actual_even_leading_shift_uniform {d : ℕ} (hd : 9≤d) :
    ∀ᶠ w : ℕ in atTop,
      ∀ (z extra : ℕ) (e : ℕ → ℕ),
      (∀ᶠ n : ℕ in atTop,(e n : ℝ)<countBeta d*(2*(w : ℝ))^2*(n : ℝ)^(d-2)) →
      ∀ᶠ v : ℕ in atTop,
      ∀ (X : Type*) [AddCommGroup X] [Module K X] [Module.Finite K X],
      ∀ T : ℕ → MvPolynomial (Fin w × Bool) K →ₗ[K] X,
      finrank K X=deletedTargetCount d (2*w) →
      finrank K (constrainedOutputs T 2)=quadraticOutputDimension d (2*w) →
      (∀ R,4≤R → T R=0) →
        let S := Space (v+v+z) d (upperCount (v+v+z) d) (allEvenIndices d)
          (allEvenCount d (2*w) (v+v+z) (e (v+v+z)+extra)) (constrainedOutputs T)
        ∀ R : allEvenIndices d,∃ p : S,LinearIndependent K (p.2 R) := by
  classical
  obtain ⟨W,hW⟩ := eventually_atTop.mp (block_parameters_eventually (by omega : 3≤d))
  have hb : ∀ᶠ w : ℕ in atTop,outerColumnCount d (2*w)≤2*w := by
    filter_upwards [eventually_ge_atTop W] with w hw
    exact (hW (2*w) (by omega)).1
  filter_upwards [eventually_actual_even_capacities_shift_uniform (K := K) hd,
    hb,eventually_gt_atTop 0] with w hw hblock hwpos
  have hdel : deletedTargetCount d (2*w)≤(2*w+1).choose 2 :=
    Nat.choose_le_choose 2 (Nat.add_le_add_right hblock 1)
  obtain ⟨c₀,T₀,hX₀,hO₀,hT₀⟩ := exists_counted_private_frame_reference (K := K) hwpos hdel
  intro z extra e he
  filter_upwards [hw (Fin c₀ → K) T₀ hX₀ hO₀ hT₀ z extra e he,
    eventually_gt_atTop 0] with v hv hvpos
  intro X _ _ _ T hX hO hT
  have hdim : finrank K X=finrank K (Fin c₀ → K) := hX.trans hX₀.symm
  have hq := hv.1.with_output_dimension (O' := constrainedOutputs T) (hO.trans hO₀.symm)
  have hhigher (R : allEvenIndices d) (hR : R.val≠2) :=
    (hv.2.1 R hR).with_target_dimension (T' := T) hdim (hT R.val (by
      obtain ⟨h2,_,heven⟩ := mem_allEvenIndices.mp R.property
      omega))
  let counts := allEvenCount d (2*w) (v+v+z) (e (v+v+z)+extra)
  let I := Label (upperCount (v+v+z) d) (allEvenIndices d) counts
  letI : LinearOrder I := LinearOrder.lift' (Fintype.equivFin I) (Fintype.equivFin I).injective
  have hJ : ∀ j∈allEvenIndices d,2≤j := fun _ hj => (mem_allEvenIndices.mp hj).1
  have hdegree : ∀ j∈allEvenIndices d,j≤d := fun _ hj => (mem_allEvenIndices.mp hj).2.1
  have heven : ∀ j∈allEvenIndices d,j%2=0 := fun _ hj => (mem_allEvenIndices.mp hj).2.2
  have h2 : 2∈allEvenIndices d := mem_allEvenIndices.mpr ⟨le_rfl,by omega,by decide⟩
  have hcover : ∀ r,0<r → r≤d → r%2=0 → r∈allEvenIndices d := by
    intro r hr hrd hre
    exact mem_allEvenIndices.mpr ⟨by omega,hrd,hre⟩
  exact all_even_extended_leading (by omega) hvpos T hJ hdegree h2 ⟨_,hq⟩
    (fun R hR => ⟨_,hhigher R hR⟩)

end Froberg.PreparedParameters
