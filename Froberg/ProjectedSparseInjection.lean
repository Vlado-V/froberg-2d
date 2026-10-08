import Froberg.ProjectedGeneralVectors
import Froberg.AttachedMultiplication

/-! Sparse attached generators remain injective modulo a finite family of
fixed output relations. The same unrestricted coefficient tuple works for all
projections and all coefficient degrees through the prescribed bound. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial Quartic.PolynomialBilinearCoordinates
variable {K I V : Type*} [Field K] [Infinite K] [Fintype I]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {n s d m H : ℕ}

theorem projected_sparse_injection_open
    (e : Fin m → Fin n →₀ ℕ) (he : ∀ i,(e i).degree=s)
    (F : I → V →ₗ[K] (Fin H → K))
    (hcap : ∀ i (c : ℕ),c≤d → ∀ β : Fin n →₀ ℕ,β.degree=s+c →
      Fintype.card {j : Fin m // e j≤β}≤finrank K (F i).range) :
    ∃ D : MvPolynomial (Fin (finrank K (Fin m → V))) K,
      (∃ x,eval x D≠0) ∧ ∀ x,eval x D≠0 → ∀ i (c : ℕ),c≤d →
        Function.Injective (AttachedMultiplication.multiplication (d := c) e
          (fun j => F i ((coordinates K (Fin m → V)).symm x j))) := by
  classical
  obtain ⟨D,hD,hgood⟩ := finite_projected_general_vectors_open (m := m) F
  refine ⟨D,hD,?_⟩
  intro x hx i c hc
  apply AttachedMultiplication.injective_of_independent_fibers e _ he
  intro β hβ
  let S : Finset (Fin m) := Finset.univ.filter (fun j => e j≤β)
  have hS : S.card≤finrank K (F i).range := by
    simpa only [S,Fintype.card_subtype] using hcap i c hc β hβ
  let g : {j : Fin m // e j≤β} → S := fun j =>
    ⟨j.val,by simp only [S,Finset.mem_filter,Finset.mem_univ,true_and]; exact j.property⟩
  have hg : Function.Injective g := by
    intro j k hjk
    exact Subtype.ext (congrArg (fun z : S => z.val) hjk)
  exact (hgood x hx i S hS).comp g hg

/-- A uniform divisor bound gives the projected open without checking each
coefficient degree separately. -/
theorem projected_sparse_injection_open_of_divisor_bound
    (e : Fin m → Fin n →₀ ℕ) (he : ∀ i,(e i).degree=s) (b : ℕ)
    (hdiv : ∀ β : Fin n →₀ ℕ,Fintype.card {j : Fin m // e j≤β}≤b*β.degree.choose s)
    (F : I → V →ₗ[K] (Fin H → K))
    (hcap : ∀ i,b*(s+d).choose s≤finrank K (F i).range) :
    ∃ D : MvPolynomial (Fin (finrank K (Fin m → V))) K,
      (∃ x,eval x D≠0) ∧ ∀ x,eval x D≠0 → ∀ i (c : ℕ),c≤d →
        Function.Injective (AttachedMultiplication.multiplication (d := c) e
          (fun j => F i ((coordinates K (Fin m → V)).symm x j))) := by
  apply projected_sparse_injection_open e he F
  intro i c hc β hβ
  apply (hdiv β).trans
  rw [hβ]
  exact (Nat.mul_le_mul_left b (Nat.choose_le_choose s (Nat.add_le_add_left hc s))).trans (hcap i)

end Froberg
