module

public import Quartic.SharedKernelCharts

@[expose] public section

/-!
# Generic exclusion of a shared kernel condition on several coefficient vectors

The q coefficient vectors are chosen in one common coefficient space, while
the same polynomial matrix acts on each. A family with fewer than q*r
parameters cannot force all q vectors into a kernel of codimension at least r
on a nonempty principal open. This is the shared-Q incidence exclusion step.
-/
noncomputable section
namespace Quartic.SharedKernelAvoidance
open Matrix MvPolynomial KernelPolynomialCharts SharedKernelCharts
variable {K I : Type*} [Field K] [Infinite K] [Fintype I] {a n r q : ℕ}

 theorem principal_open_avoids_shared_kernels
    (A : Matrix (Fin a) (Fin n) (MvPolynomial I K))
    (hr : Fintype.card I < q*r) :
    ∃ P : MvPolynomial (Fin q × Fin n) K,
      (∃ x : Fin q × Fin n → K, eval x P ≠ 0) ∧
      ∀ x, eval x P ≠ 0 → ∀ t : I → K,
        r ≤ (evaluated A t).rank → ∃ i : Fin q, evaluated A t *ᵥ (fun k => x (i,k)) ≠ 0 := by
  classical
  let C := (Fin r ↪ Fin a) × (Fin r ↪ Fin n)
  let Param (c : C) := SharedKernelCharts.Parameters I c.2 q
  let F (c : C) := SharedKernelCharts.numerator (q := q) A c.1 c.2
  let G (c : C) := SharedKernelCharts.denominator (q := q) A c.1 c.2
  have hdim (c : C) : Fintype.card (Param c) < Fintype.card (Fin q × Fin n) := by
    have hc : r ≤ n := by simpa using Fintype.card_le_of_injective c.2 c.2.injective
    have hsum : q*(n-r)+q*r=q*n := by rw [← Nat.mul_add, Nat.sub_add_cancel hc]
    change Fintype.card (SharedKernelCharts.Parameters I c.2 q) < _
    rw [SharedKernelCharts.parameter_count,Fintype.card_prod,Fintype.card_fin,Fintype.card_fin]
    omega
  obtain ⟨P,hP,havoid⟩ := RationalImageAvoidance.principal_open_avoids_finite_union Param F G hdim
  refine ⟨P,hP,?_⟩
  intro x hx t ht
  by_contra! hker
  obtain ⟨u,v,hdet⟩ := KernelCharts.exists_minor_of_rank_le (evaluated A t) ht
  obtain ⟨p,_,hp,he⟩ := cover_kernel_tuple A u v t hdet (fun i k => x (i,k)) hker
  exact havoid x hx (u,v) p hp (by simpa only [Prod.eta] using he.symm)

end Quartic.SharedKernelAvoidance
