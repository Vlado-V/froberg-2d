module

public import Froberg.UniformActualPreparedComparison
public import Froberg.UniformActualRestoredComparison
public import Froberg.UniformCountedPreparedSelection
public import Froberg.UniformCountedRestoredSelection
public import Froberg.UniformOddPureProjection
public import Froberg.UniformComparisonAssembly
public import Froberg.UniformEquivariantReduction

@[expose] public section

/-! The field-uniform higher-degree assembly. All numerical choices precede
the coefficient field. The only base-degree input is the uniform quadratic
endpoint, and no induction on the generating degree is used. -/
noncomputable section
set_option maxHeartbeats 1200000
namespace Froberg
open Filter PreparedParameters PreparedTarget

private theorem uniform_tendsto_double_atTop :
    Tendsto (fun w : ℕ => 2*w) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop b] with w hw
  omega

theorem eventually_uniform_criticalComparisonBlock {d : ℕ} (hd : 3≤d)
    (N₂ : ℕ) (hquad : ∀ h,N₂≤h → ∀ (K : Type) [Field K] [Infinite K],
      GenericEndpoint K h 2 (upperCount h 2)) :
    ∀ᶠ w : ℕ in atTop,UniformCriticalComparisonBlock d (2*w) := by
  by_cases he : d%2=0
  · filter_upwards [uniform_tendsto_double_atTop.eventually
      (eventually_uniform_counted_restored_frame_ready hd he N₂ hquad)] with w hw
    intro hdiv k lo hk hkh hhpos upper a f e ha hc δ hδ hres
    exact uniform_actual_restored_comparison_of_eventual_frames hd he hk hkh hhpos
      upper a f e ha hc hδ hres (hw hdiv k lo hk hkh hhpos upper a f e ha hc δ hδ hres)
  · have ho : d%2=1 := by omega
    have hodd : Odd d := Nat.odd_iff.mpr ho
    filter_upwards [eventually_uniform_counted_prepared_frame_ready hd ho N₂ hquad,
      uniform_tendsto_double_atTop.eventually
        (eventually_odd_pure_projection_data_uniform hd hodd)] with w hw hpure
    intro hdiv k lo hk hkh hhpos upper a f e ha hc δ hδ hres
    have hframes := hw hdiv k lo hk hkh hhpos upper a f e ha hc δ hδ hres
      (tailGeneratorCount d (2*w))
    have hcomparison := eventually_uniform_actual_prepared_comparison hd ho hk hkh hhpos
      upper a f e ha hc hδ hres
    filter_upwards [hframes,hcomparison] with n hfn hcn
    intro K _ _ _
    obtain ⟨pure⟩ := hpure K
    obtain ⟨frame,hframe⟩ := hfn K pure.U
      ⟨pure.cutoff,fun hn => False.elim (hn hodd)⟩
    exact hcn K pure (targetLayerOutput frame)
      (fun j (_ : j∈allEvenIndices d) => targetLayerOutput_homogeneous frame j)
      hframe.base _ (Fintype.equivFin _).symm hframe.enlarged

theorem uniform_high_degree_recurrence_of_quadratic_endpoint
    (hquad : UniformEndpointStatement 2) {d : ℕ} (hd : 3≤d) :
    UniformCriticalRecurrence d := by
  obtain ⟨N₂,hN₂,hbase⟩ := hquad
  apply uniformCriticalRecurrence_of_comparison_blocks hd
  apply eventually_uniform_criticalComparisonBlock hd N₂
  intro h hh K _ _
  exact hbase K h hh _ (upperCount_le_monomial_count (by omega) 2)

theorem uniformMainStatement_of_quadratic_endpoint
    (hquad : UniformEndpointStatement 2) : UniformMainStatement := by
  apply uniformMainStatement_of_uniformEndpoints
  intro d hd
  by_cases heq : d=2
  · subst d
    exact hquad
  · exact (uniform_high_degree_recurrence_of_quadratic_endpoint hquad (by omega)).endpoints hd

end Froberg
