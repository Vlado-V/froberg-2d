module

public import Froberg.PreparedWitnessReduction
public import Froberg.PreparedEmptyProfileRow

@[expose] public section

/-! Concrete cubic and quartic witnesses give the full even reduction on
one nonempty principal open, including every inactive even row. -/
noncomputable section
set_option maxHeartbeats 1600000
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial MonomialExpansion
variable {K : Type} [Field K] [Infinite K]
variable {X : Type*} [AddCommGroup X] [Module K X] [Module.Finite K X]
variable {h n q : ℕ} {counts : ℕ → ℕ}

instance kernelOutputSpaceFinite {σ : Type*} [Fintype σ] {d : ℕ} {J : Finset ℕ}
    (T : ℕ → MvPolynomial σ K →ₗ[K] X) :
    Module.Finite K (Space n d q J counts (fun j => homogeneousSubmodule σ K j⊓(T j).ker)) :=
  finite_space (fun _ _ => inf_le_left)

theorem finite_cubic_reduction_open
    [LinearOrder (Label q (allEvenIndices 3) counts)]
    (T : ℕ → Poly K h →ₗ[K] X)
    (hz : ∀ k∈allEvenIndices 3,k≠2 → counts k=0)
    (hm : counts 2≤(2*(h/2).choose 2-finrank K X)*(n/2))
    (hquad : ∃ b,QuadraticRowCapacity n 3 q b (allEvenIndices 3) counts
      (fun j => Forms K h j⊓(T j).ker)) :
    let S := Space n 3 q (allEvenIndices 3) counts (fun j => Forms K h j⊓(T j).ker)
    ∃ D : MvPolynomial (Fin (finrank K S)) K,
      (∃ p : S,eval ((Module.finBasis K S).equivFun p) D≠0) ∧
      ∀ p : S,eval ((Module.finBasis K S).equivFun p) D≠0 → EvenPositiveReduction p := by
  have h2 : 2∈allEvenIndices 3 := mem_allEvenIndices.mpr ⟨le_rfl,by omega,by decide⟩
  apply even_reduction_open_of_witnesses (fun _ _ => inf_le_left)
    (fun _ hj => (mem_allEvenIndices.mp hj).1)
    (fun _ hj => (mem_allEvenIndices.mp hj).2.1)
    (fun _ hj => (mem_allEvenIndices.mp hj).2.2)
    (fun r hr hrd hre => mem_allEvenIndices.mpr ⟨by omega,hrd,hre⟩)
  · intro R
    have hr := mem_allEvenIndices.mp R.property
    have hRv : R.val=2 := by omega
    have hR : R=(⟨2,h2⟩ : allEvenIndices 3) := Subtype.ext hRv
    subst R
    obtain ⟨b,hb⟩ := hquad
    exact exists_quadratic_row_parameter (fun _ _ => inf_le_left)
      (fun _ hj => (mem_allEvenIndices.mp hj).1) h2 hb
  · intro R _ _ _
    obtain ⟨p,hp⟩ := exists_strong_cubic_product_parameter (q := q) T hz hm
    exact ⟨p,hp R⟩

theorem finite_quartic_reduction_open
    [LinearOrder (Label q (allEvenIndices 4) counts)]
    (T : ℕ → Poly K h →ₗ[K] X)
    (hz : ∀ k∈allEvenIndices 4,k≠2 → counts k=0)
    (S : Finset (Fin n)) (hS : S.card≤Sᶜ.card)
    (hm : counts 2≤(2*(h/2).choose 2-finrank K X)*(S.card.choose 2/2))
    (hquad : ∃ b,QuadraticRowCapacity n 4 q b (allEvenIndices 4) counts
      (fun j => Forms K h j⊓(T j).ker))
    (Q : Fin (Fintype.card (Label q (allEvenIndices 4) counts)) → Forms K n 4)
    (hQ : Function.Injective (ProjectedPrefix.multiplication (fun α => partialDegree S α≠2) Q 0)) :
    let A := Space n 4 q (allEvenIndices 4) counts (fun j => Forms K h j⊓(T j).ker)
    ∃ D : MvPolynomial (Fin (finrank K A)) K,
      (∃ p : A,eval ((Module.finBasis K A).equivFun p) D≠0) ∧
      ∀ p : A,eval ((Module.finBasis K A).equivFun p) D≠0 → EvenPositiveReduction p := by
  have h2 : 2∈allEvenIndices 4 := mem_allEvenIndices.mpr ⟨le_rfl,by omega,by decide⟩
  apply even_reduction_open_of_witnesses (fun _ _ => inf_le_left)
    (fun _ hj => (mem_allEvenIndices.mp hj).1)
    (fun _ hj => (mem_allEvenIndices.mp hj).2.1)
    (fun _ hj => (mem_allEvenIndices.mp hj).2.2)
    (fun r hr hrd hre => mem_allEvenIndices.mpr ⟨by omega,hrd,hre⟩)
  · intro R
    by_cases hR : R.val=2
    · have hReq : R=(⟨2,h2⟩ : allEvenIndices 4) := Subtype.ext hR
      subst R
      obtain ⟨b,hb⟩ := hquad
      exact exists_quadratic_row_parameter (fun _ _ => inf_le_left)
        (fun _ hj => (mem_allEvenIndices.mp hj).1) h2 hb
    · have hr := mem_allEvenIndices.mp R.property
      have heq : 4-R.val=0 := by omega
      have hQ' : Function.Injective (ProjectedPrefix.multiplication
          (fun α => partialDegree S α≠2) Q (4-R.val)) := by
        rw [heq]
        exact hQ
      exact exists_strong_quartic_empty_row_parameter T hz R hR S hS hm Q hQ'
  · intro R _ _ _
    obtain ⟨p,hp⟩ := exists_strong_quartic_product_parameter (q := q) T hz S hS hm
    exact ⟨p,hp R⟩

end Froberg.PreparedParameters
