module

public import Froberg.GenericFieldDescent
public import Froberg.GenericMonotonicity

@[expose] public section

/-! Field descent for the actual endpoint statement and its defect recurrence. -/
noncomputable section
namespace Froberg
variable {K L : Type} [Field K] [Field L] [Infinite K] [Infinite L]
variable {n d r : ℕ}

theorem genericEndpoint_baseChange (f : K →+* L) (hn : 0 < n)
    (hr : r ≤ (n+d-1).choose d) : GenericEndpoint K n d r ↔ GenericEndpoint L n d r := by
  rw [genericEndpoint_iff_genericCokernel hn hr,genericEndpoint_iff_genericCokernel hn hr,
    GenericFieldDescent.genericCokernel_baseChange f hn]

theorem criticalDefect_baseChange (f : K →+* L) (hn : 0 < n) :
    criticalDefect K n d=criticalDefect L n d := by
  unfold criticalDefect
  rw [GenericFieldDescent.genericHomology_baseChange f hn,
    GenericFieldDescent.genericCokernel_baseChange f hn]

theorem endpoint_recurrence_descends (f : K →+* L) {h start : ℕ}
    (hstep : ∀ n,start ≤ n → criticalDefect L (n+h) d ≤ criticalDefect L n d) :
    ∀ n,max start 1 ≤ n → criticalDefect K (n+h) d ≤ criticalDefect K n d := by
  intro n hn
  rw [criticalDefect_baseChange f (by omega : 0 < n+h),criticalDefect_baseChange f (by omega : 0 < n)]
  exact hstep n (by omega)

theorem eventual_endpoints_descend (f : K →+* L)
    (h : ∃ N : ℕ,1 ≤ N ∧ ∀ n,N ≤ n → ∀ r,r ≤ (n+d-1).choose d → GenericEndpoint L n d r) :
    ∃ N : ℕ,1 ≤ N ∧ ∀ n,N ≤ n → ∀ r,r ≤ (n+d-1).choose d → GenericEndpoint K n d r := by
  obtain ⟨N,hN,h⟩ := h
  exact ⟨N,hN,fun n hn r hr => (genericEndpoint_baseChange f (by omega) hr).mpr (h n hn r hr)⟩

theorem critical_child_defects_le (hn : 0 < n) :
    genericHomology K n d (upperCount n d-1) ≤ criticalDefect K n d ∧
    genericCokernel K n d (upperCount n d) ≤ criticalDefect K n d := by
  have hcount := upperCount_le_lowerCount_add_one n d
  exact ⟨(genericHomology_mono hn (by omega) (lowerCount_le_monomial_count hn d)).trans
    (le_max_left _ _),le_max_right _ _⟩

end Froberg
