module

public import Froberg.GenericMonotonicity
public import Froberg.AuxiliaryCounts
public import Quartic.UniformEndpoint

@[expose] public section

/-! The quadratic development's sign-defined endpoints are exactly the
floor/ceiling counts used in the general critical-defect recurrence. -/
noncomputable section
namespace Froberg.QuadraticEndpointCounts
open Quartic.UniformEndpoint

private theorem chi_eq (n r : ℕ) : Quartic.Counts.chi n r = euler n 2 r := by
  simp only [Quartic.Counts.chi,Quartic.Counts.b4,Quartic.Counts.b2,euler]
  congr 2 <;> omega

theorem upperEndpoint_eq {n : ℕ} (hn : 0<n) : upperEndpoint n=upperCount n 2 := by
  apply le_antisymm
  · exact Nat.find_min' (endpoint_exists n) (by
      rw [chi_eq]
      exact euler_upperCount_nonpos hn 2)
  · apply (euler_nonpos_iff_upperCount_le hn 2 _ ?_).mp
    · rw [←chi_eq]
      exact upper_nonpositive n
    · convert upper_le_quadratics n using 1 <;> congr 1 <;> omega

theorem lowerEndpoint_eq {n : ℕ} (hn : 0<n) : lowerEndpoint n=lowerCount n 2 := by
  have hu := upperEndpoint_eq hn
  have hlu := lowerCount_le_upperCount n 2
  have hul := upperCount_le_lowerCount_add_one n 2
  unfold lowerEndpoint
  split_ifs with hz
  · have he : 0≤euler n 2 (upperEndpoint n) := by rw [←chi_eq,hz]
    have hb : upperEndpoint n≤(n+2-1).choose 2 := by
      convert upper_le_quadratics n using 1 <;> congr 1 <;> omega
    have hl := (euler_nonneg_iff_le_lowerCount hn 2 _ hb).mp he
    omega
  · have hne : lowerCount n 2≠upperCount n 2 := by
      intro heq
      have hlo := euler_lowerCount_nonneg hn 2
      have hhi := euler_upperCount_nonpos hn 2
      rw [heq] at hlo
      have he : euler n 2 (upperCount n 2)=0 := by omega
      exact hz (by rw [chi_eq,hu,he])
    omega

theorem predecessor_le_lowerCount {n : ℕ} (hn : 0<n) :
    upperEndpoint n-1≤lowerCount n 2 := by
  rw [upperEndpoint_eq hn]
  have h := upperCount_le_lowerCount_add_one n 2
  omega

theorem lowerEndpoint_chi_nonneg {n : ℕ} (hn : 0<n) :
    0≤Quartic.Counts.chi n (lowerEndpoint n) := by
  rw [chi_eq,lowerEndpoint_eq hn]
  exact euler_lowerCount_nonneg hn 2

theorem parentCount_eq (m : ℕ) (upper : Bool) :
    parentCount m upper=adjacentCriticalCount upper (m+3) 2 := by
  cases upper
  · exact lowerEndpoint_eq (by omega : 0 < m + 3)
  · exact upperEndpoint_eq (by omega : 0 < m + 3)

theorem parent_chi_sign (m : ℕ) (upper : Bool) :
    if upper then Quartic.Counts.chi (m+3) (parentCount m upper)≤0
    else 0≤Quartic.Counts.chi (m+3) (parentCount m upper) := by
  cases upper
  · exact lowerEndpoint_chi_nonneg (by omega)
  · exact upper_nonpositive (m+3)

theorem criticalDefect_eq {K : Type} [Field K] {n : ℕ} (hn : 0<n) :
    criticalDefect K n 2 = max
      (genericHomology K n 2 (lowerEndpoint n))
      (genericCokernel K n 2 (upperEndpoint n)) := by
  rw [lowerEndpoint_eq hn,upperEndpoint_eq hn]
  rfl

theorem genericHomology_predecessor_le_criticalDefect
    {K : Type} [Field K] [Infinite K] {n : ℕ} (hn : 0<n) :
    genericHomology K n 2 (upperEndpoint n-1)≤criticalDefect K n 2 :=
  (genericHomology_mono hn (predecessor_le_lowerCount hn)
    (lowerCount_le_monomial_count hn 2)).trans (le_max_left _ _)

theorem genericCokernel_upperEndpoint_le_criticalDefect
    {K : Type} [Field K] {n : ℕ} (hn : 0<n) :
    genericCokernel K n 2 (upperEndpoint n)≤criticalDefect K n 2 := by
  rw [upperEndpoint_eq hn]
  exact le_max_right _ _

end Froberg.QuadraticEndpointCounts
