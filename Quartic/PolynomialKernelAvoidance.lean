import Quartic.KernelPolynomialCharts

/-!
# Generic avoidance of polynomial families of high-codimension kernels

If a polynomial matrix family has fewer parameters than a prescribed rank,
a nonempty principal open of vectors avoids every kernel whose matrix has at
least that rank. All rational kernel charts and their parameter counts are
constructed in the preceding modules.
-/
noncomputable section
namespace Quartic.PolynomialKernelAvoidance
open MvPolynomial Matrix SubspaceCharts KernelPolynomialCharts
variable {K I : Type*} [Field K] [Infinite K] [Fintype I] {a n r : ℕ}

/-- Generic vectors avoid every high-rank kernel in a lower-dimensional
polynomial family. The rank condition can be restricted to any parameter set. -/
theorem principal_open_avoids_kernels
    (A : Matrix (Fin a) (Fin n) (MvPolynomial I K)) (hr : Fintype.card I < r) :
    ∃ P : MvPolynomial (Fin n) K, (∃ x : Fin n → K, eval x P ≠ 0) ∧
      ∀ x, eval x P ≠ 0 → ∀ t : I → K,
        r ≤ (evaluated A t).rank → evaluated A t *ᵥ x ≠ 0 := by
  classical
  let C := (Fin r ↪ Fin a) × (Fin r ↪ Fin n)
  let Param (c : C) := ChartParameters (I := I) c.2
  let F (c : C) := numerator A c.1 c.2
  let G (c : C) := denominator A c.1 c.2
  have hdim (c : C) : Fintype.card (Param c) < Fintype.card (Fin n) := by
    have hc : r ≤ n := by simpa using Fintype.card_le_of_injective c.2 c.2.injective
    change Fintype.card (ChartParameters (I := I) c.2) < Fintype.card (Fin n)
    rw [parameter_count, Fintype.card_fin]
    omega
  obtain ⟨P, hP, havoid⟩ := RationalImageAvoidance.principal_open_avoids_finite_union Param F G hdim
  refine ⟨P, hP, ?_⟩
  intro x hx t ht hker
  obtain ⟨u, v, hdet⟩ := KernelCharts.exists_minor_of_rank_le (evaluated A t) ht
  obtain ⟨p, hp, hpx⟩ := kernel_in_chart A u v t hdet x hker
  exact havoid x hx (u, v) p hp hpx.symm

/-- In particular, one vector simultaneously avoids every eligible kernel. -/
theorem exists_avoiding_kernels
    (A : Matrix (Fin a) (Fin n) (MvPolynomial I K)) (hr : Fintype.card I < r) :
    ∃ x : Fin n → K, ∀ t : I → K,
      r ≤ (evaluated A t).rank → evaluated A t *ᵥ x ≠ 0 := by
  obtain ⟨P, ⟨x, hx⟩, h⟩ := principal_open_avoids_kernels A hr
  exact ⟨x, h x hx⟩

end Quartic.PolynomialKernelAvoidance
