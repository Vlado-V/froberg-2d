module

public import Froberg.QuadraticNonTwoTransfer
public import Froberg.QuadraticEndpointCounts
public import Froberg.EndpointFieldDescent
public import Quartic.SmallTransfer
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

@[expose] public section

/-! Uniform quadratic defect recurrence in characteristic different from two. -/
noncomputable section
namespace Froberg.QuadraticNonTwoRecurrence
open Module Quartic UniformEndpoint QuadraticEndpointCounts
variable {K : Type} [Field K] [Infinite K]
set_option maxHeartbeats 1200000

theorem endpoint_defects [IsAlgClosed K] (m : ℕ) (hm : 320 ≤ m) (upper : Bool)
    (h2 : (2 : K) ≠ 0) :
    (genericHomology K (m+3) 2 (parentCount m upper) : ℤ) ≤ max (genericHomology K m 2 (upperEndpoint m-1) : ℤ)
        ((genericCokernel K m 2 (upperEndpoint m) : ℤ)-Counts.chi (m+3) (parentCount m upper)) ∧
    (genericCokernel K (m+3) 2 (parentCount m upper) : ℤ) ≤ max (genericCokernel K m 2 (upperEndpoint m) : ℤ)
        ((genericHomology K m 2 (upperEndpoint m-1) : ℤ)+Counts.chi (m+3) (parentCount m upper)) := by
  have hw := QuadraticNonTwoTransfer.parent_defect_witness (K := K) m hm upper h2
  rw [SmallTransfer.parent_count m (by omega) upper,Nat.add_comm 3 m] at hw
  obtain ⟨f,hf,hH,hC⟩ := hw
  have hgH := QuadraticDefectBridge.homology_le (by omega : 0 < m+3) f hf
  have hgC := QuadraticDefectBridge.cokernel_le f
  constructor
  · calc
      _ ≤ (finrank K (QuarticHomology f):ℤ) := by exact_mod_cast hgH
      _ ≤ _ := hH
  · calc
      _ ≤ (finrank K (QuadraticChildFlag.Coker f):ℤ) := by exact_mod_cast hgC
      _ ≤ _ := hC

theorem step_algebraicallyClosed [IsAlgClosed K] (m : ℕ) (hm : 320 ≤ m)
    (h2 : (2 : K) ≠ 0) : criticalDefect K (m+3) 2 ≤ criticalDefect K m 2 := by
  have hlow := (endpoint_defects (K := K) m hm false h2).1
  have hhigh := (endpoint_defects (K := K) m hm true h2).2
  have hk := genericHomology_predecessor_le_criticalDefect (K := K) (by omega : 0 < m)
  have hc := genericCokernel_upperEndpoint_le_criticalDefect (K := K) (by omega : 0 < m)
  have hsignlo := lowerEndpoint_chi_nonneg (by omega : 0 < m+3)
  have hsignhi := upper_nonpositive (m+3)
  simp only [parentCount,Bool.false_eq_true,ite_false,ite_true] at hlow hhigh
  rw [criticalDefect_eq (by omega : 0 < m+3)]
  omega

theorem step (m : ℕ) (hm : 320 ≤ m) (h2 : (2 : K) ≠ 0) :
    criticalDefect K (m+3) 2 ≤ criticalDefect K m 2 := by
  let f := algebraMap K (AlgebraicClosure K)
  have h2' : (2 : AlgebraicClosure K) ≠ 0 := by
    intro hz
    apply h2
    apply f.injective
    simpa only [map_ofNat,map_zero] using hz
  rw [criticalDefect_baseChange f (by omega : 0 < m+3),
    criticalDefect_baseChange f (by omega : 0 < m)]
  exact step_algebraicallyClosed m hm h2'

end Froberg.QuadraticNonTwoRecurrence
