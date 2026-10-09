module

public import Froberg.IntrinsicTransfer
public import Froberg.AuxiliaryCounts

@[expose] public section

/-! The concrete projected complex and rank certificate consumed by the
two-critical-count recurrence. -/
noncomputable section
namespace Froberg
open Module Filter
variable (K : Type) [Field K] [Infinite K]

structure LocalComparisonData (n d r B : ℕ) where
  deleted : Submodule K (Forms K n (2*d))
  generators : Fin r → Forms K n d
  independent : LinearIndependent K generators
  motion : Fin r → Forms K n d
  retained : Submodule K (ProjectedEndpointHomology deleted.mkQ generators)
  normal_rank : finrank K (projectedNormalMap deleted.mkQ generators motion).range=
    min (finrank K (ProjectedEndpointHomology deleted.mkQ generators ⧸ retained))
      (finrank K (ProjectedEndpointCokernel deleted.mkQ generators))
  retained_bound : finrank K retained ≤ B
  deleted_bound : finrank K deleted ≤ B

variable {K} {n d r B m h : ℕ}

theorem LocalComparisonData.bounds (D : LocalComparisonData K n d r B)
    (hn : 0 < n) (hr : r ≤ (n+d-1).choose d) :
    (genericHomology K n d r : ℤ) ≤ max (B : ℤ) ((B : ℤ)-euler n d r) ∧
    (genericCokernel K n d r : ℤ) ≤ max (B : ℤ) ((B : ℤ)+euler n d r) := by
  apply transfer_bounds_le_of_intrinsic hn hr D.deleted.mkQ D.deleted.mkQ_surjective
    D.generators D.motion D.independent D.retained.mkQ
  · rw [Submodule.ker_mkQ]
    exact D.normal_rank
  · rw [Submodule.ker_mkQ]
    exact D.retained_bound
  · rw [Submodule.ker_mkQ]
    exact D.deleted_bound

theorem criticalDefect_step_of_comparison_data (hm : 0 < m)
    (D : ∀ upper : Bool,LocalComparisonData K (m+h) d
      (adjacentCriticalCount upper (m+h) d) (criticalDefect K m d)) :
    criticalDefect K (m+h) d ≤ criticalDefect K m d := by
  have hn : 0 < m+h := by omega
  apply criticalDefect_step_of_transfer hm hn
  · exact ((D false).bounds hn (lowerCount_le_monomial_count hn d)).1
  · exact ((D true).bounds hn (upperCount_le_monomial_count hn d)).2

theorem eventual_recurrence_of_comparison_data
    (hD : ∀ᶠ m in atTop,∀ upper : Bool,Nonempty (LocalComparisonData K (m+h) d
      (adjacentCriticalCount upper (m+h) d) (criticalDefect K m d))) :
    ∃ start : ℕ,∀ m,start ≤ m → criticalDefect K (m+h) d ≤ criticalDefect K m d := by
  classical
  obtain ⟨N,hN⟩ := eventually_atTop.mp hD
  refine ⟨max N 1,?_⟩
  intro m hm
  exact criticalDefect_step_of_comparison_data (by omega)
    (fun upper => Classical.choice (hN m (by omega) upper))

end Froberg
