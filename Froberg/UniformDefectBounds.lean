module

public import Froberg.GenericMonotonicity
public import Froberg.Recurrence

@[expose] public section

/-! Field-independent bounds for the two critical defects.

The initial recurrence window is bounded by the dimension of the ambient
degree-`2*d` forms, not by a field-dependent maximum of generic ranks. -/
noncomputable section
namespace Froberg

variable {K : Type} [Field K] [Infinite K] {n d h n₀ : ℕ}

theorem genericCokernel_le_target_dimension (hn : 0<n) (r : ℕ) :
    genericCokernel K n d r≤(n+2*d-1).choose (2*d) := by
  obtain ⟨a,ha⟩ := genericCokernel_attained K n d r
  have hdim := endpoint_quotient_add_rank hn (coefficientForms K n d r a)
  change coefficientCokernel K n d r a + _ = _ at hdim
  rw [ha] at hdim
  omega

theorem criticalDefect_le_target_dimension (hn : 0<n) :
    criticalDefect K n d≤(n+2*d-1).choose (2*d) := by
  apply max_le
  · have hc := genericCokernel_le_target_dimension (K := K) (d := d) hn (lowerCount n d)
    have he := euler_lowerCount_nonneg hn d
    unfold genericHomology
    omega
  · exact genericCokernel_le_target_dimension hn (upperCount n d)

/-- The same numeric bound works for every field satisfying the same
recurrence. No generic dimension occurs in the bound itself. -/
theorem criticalDefect_bound_from_recurrence (hh : 0<h) (hn₀ : 1≤n₀)
    (hstep : ∀ n,n₀≤n → criticalDefect K (n+h) d≤criticalDefect K n d) :
    ∀ n,n₀≤n → criticalDefect K n d≤(n₀+h-1+2*d-1).choose (2*d) := by
  apply recurrence_bound_from_window (fun n => criticalDefect K n d) h n₀ _ hh hstep
  intro n hn htop
  apply (criticalDefect_le_target_dimension (K := K) (d := d) (by omega : 0<n)).trans
  apply Nat.choose_le_choose (2*d)
  omega

end Froberg
