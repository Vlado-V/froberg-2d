/-
Copyright (c) 2026 Vlado Vojdanovski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vlado Vojdanovski
-/
module

public import Froberg.QuadraticCertificateFreeTransfer
public import Froberg.QuadraticEndpointCounts
public import Froberg.EndpointFieldDescent
public import Quartic.SmallTransfer
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! Uniform quadratic defect recurrence in every characteristic, without finite bases. -/

@[expose] public section

noncomputable section
namespace Froberg.QuadraticCertificateFreeRecurrence
open Module Quartic UniformEndpoint QuadraticEndpointCounts
variable {K : Type} [Field K] [Infinite K]


set_option maxHeartbeats 1200000 in -- Preserve the budget during this port.
theorem endpoint_defects [IsAlgClosed K] (m : ℕ) (hm : 320 ≤ m) (upper : Bool) :
    (genericHomology K (m+3) 2 (parentCount m upper) : ℤ) ≤ max (genericHomology K m 2
      (upperEndpoint m-1) : ℤ)
        ((genericCokernel K m 2 (upperEndpoint m) : ℤ)-Counts.chi (m+3) (parentCount m upper)) ∧
    (genericCokernel K (m+3) 2 (parentCount m upper) : ℤ) ≤ max (genericCokernel K m 2
      (upperEndpoint m) : ℤ)
        ((genericHomology K m 2 (upperEndpoint m-1) : ℤ)+Counts.chi (m+3) (parentCount m
          upper)) := by
  have hw := QuadraticCertificateFreeTransfer.parent_defect_witness (K := K) m hm upper
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

set_option maxHeartbeats 1200000 in -- Preserve the budget during this port.
theorem step_algebraicallyClosed [IsAlgClosed K] (m : ℕ) (hm : 320 ≤ m) : criticalDefect K (m+3) 2 ≤ criticalDefect K m 2 := by
  have hlow := (endpoint_defects (K := K) m hm false).1
  have hhigh := (endpoint_defects (K := K) m hm true).2
  have hk := genericHomology_predecessor_le_criticalDefect (K := K) (by omega : 0 < m)
  have hc := genericCokernel_upperEndpoint_le_criticalDefect (K := K) (by omega : 0 < m)
  have hsignlo := lowerEndpoint_chi_nonneg (by omega : 0 < m+3)
  have hsignhi := upper_nonpositive (m+3)
  simp only [parentCount,Bool.false_eq_true,ite_false,ite_true] at hlow hhigh
  rw [criticalDefect_eq (by omega : 0 < m+3)]
  omega

set_option maxHeartbeats 1200000 in -- Preserve the budget during this port.
theorem step (m : ℕ) (hm : 320 ≤ m) :
    criticalDefect K (m+3) 2 ≤ criticalDefect K m 2 := by
  let f := algebraMap K (AlgebraicClosure K)
  rw [criticalDefect_baseChange f (by omega : 0 < m+3),
    criticalDefect_baseChange f (by omega : 0 < m)]
  exact step_algebraicallyClosed m hm

end Froberg.QuadraticCertificateFreeRecurrence
