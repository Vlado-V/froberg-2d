import Froberg.PreparedFourthExtendedRow
import Froberg.QuadraticExtendedRow
import Froberg.EmptyPrivateRow
import Froberg.ZeroEmptyExtendedRow
import Froberg.PreparedWitnessReduction

/-! The small-degree row witnesses extend to either parity of the number
of scalar variables. All counts remain the counts of the final space. -/
noncomputable section
set_option maxHeartbeats 2400000
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial
variable {K : Type} [Field K] [Infinite K]
variable {X : Type*} [AddCommGroup X] [Module K X] [Module.Finite K X]

theorem small_extended_witnesses {w v z d q : ℕ} {counts : ℕ → ℕ}
    (hd : 5≤d)
    (T : ℕ → MvPolynomial (Fin w × Bool) K →ₗ[K] X)
    (hz : ∀ k∈allEvenIndices d,k≠2 → k≠4 → counts k=0)
    (hquad : ∃ b,QuadraticRowCapacity (v+v) d q b (allEvenIndices d) counts (constrainedOutputs T))
    (hfour : ∃ b,FourthRowCapacity w v d q b (allEvenIndices d) counts T)
    (hcore : ∀ R : allEvenIndices d,
      ∃ p : Space (v+v) d q (allEvenIndices d) counts (constrainedOutputs T),
        LinearIndependent K (fun i => intrinsicLayerMap (fun j _ => (inf_le_left : constrainedOutputs T j ≤ homogeneousSubmodule (Fin w × Bool) K j)) R i p) ∧
        (row (fun j _ => (inf_le_left : constrainedOutputs T j ≤ homogeneousSubmodule (Fin w × Bool) K j)) R p).ker=(rowConstants (fun j _ => (inf_le_left : constrainedOutputs T j ≤ homogeneousSubmodule (Fin w × Bool) K j)) R p).range)
    (hproducts : ∀ R,d<R → R≤2*d → R%2=0 →
      ∃ p : Space (v+v) d q (allEvenIndices d) counts (constrainedOutputs T),
        Function.Injective (ProductRows.multiplication counts (layers p) (allEvenIndices d) R))
    (ell : Fin 2 → Forms K (v+v) 1) (hell : LinearIndependent K ell) :
    (∀ R : allEvenIndices d,
      ∃ p : Space (v+v+z) d q (allEvenIndices d) counts (constrainedOutputs T),
        LinearIndependent K (fun i => intrinsicLayerMap (fun j _ => (inf_le_left : constrainedOutputs T j ≤ homogeneousSubmodule (Fin w × Bool) K j)) R i p) ∧
        (row (fun j _ => (inf_le_left : constrainedOutputs T j ≤ homogeneousSubmodule (Fin w × Bool) K j)) R p).ker=(rowConstants (fun j _ => (inf_le_left : constrainedOutputs T j ≤ homogeneousSubmodule (Fin w × Bool) K j)) R p).range) ∧
    (∀ R,d<R → R≤2*d → R%2=0 →
      ∃ p : Space (v+v+z) d q (allEvenIndices d) counts (constrainedOutputs T),
        Function.Injective (ProductRows.multiplication counts (layers p) (allEvenIndices d) R)) := by
  classical
  constructor
  · intro R
    have hRd := (mem_allEvenIndices.mp R.property).2.1
    by_cases hR2 : R.val=2
    · have h2 : 2∈allEvenIndices d := hR2 ▸ R.property
      have hReq : R=(⟨2,h2⟩ : allEvenIndices d) := Subtype.ext hR2
      subst R
      obtain ⟨b,hb⟩ := hquad
      exact exists_quadratic_extended_row_parameter (by omega) (fun j _ => (inf_le_left : constrainedOutputs T j ≤ homogeneousSubmodule (Fin w × Bool) K j))
        (fun _ hj => (mem_allEvenIndices.mp hj).1)
        (fun _ hj => (mem_allEvenIndices.mp hj).2.1) h2 hb ell hell
    by_cases hR4 : R.val=4
    · have h4 : 4∈allEvenIndices d := hR4 ▸ R.property
      have hReq : R=(⟨4,h4⟩ : allEvenIndices d) := Subtype.ext hR4
      subst R
      obtain ⟨b,hb⟩ := hfour
      exact exists_fourth_extended_row_parameter h4 hb (by omega) ell hell
    have hzero := hz R.val R.property hR2 hR4
    letI : IsEmpty (Fin (counts R.val)) := ⟨fun i => by have := i.isLt; omega⟩
    obtain ⟨p,hpLI,hp⟩ := hcore R
    refine ⟨coreExtension z p,linearIndependent_empty_type,?_⟩
    by_cases hlt : R.val<d
    · exact empty_row_core_extended_exact (fun j _ => (inf_le_left : constrainedOutputs T j ≤ homogeneousSubmodule (Fin w × Bool) K j))
        (fun _ hj => (mem_allEvenIndices.mp hj).2.1) R hlt hzero p hp ell hell
    · exact empty_row_core_extended_exact_zero (fun j _ => (inf_le_left : constrainedOutputs T j ≤ homogeneousSubmodule (Fin w × Bool) K j))
        (fun _ hj => (mem_allEvenIndices.mp hj).2.1) R (by omega) hzero p hp ell hell
  · intro R hRd hR2d hRe
    obtain ⟨p,hp⟩ := hproducts R hRd hR2d hRe
    refine ⟨coreExtension z p,?_⟩
    rw [coreExtension_products]
    exact (rename_injective _ (Function.Injective.sumMap Function.injective_id
      (Fin.castAdd_injective (v+v) z))).comp hp

theorem small_extended_reduction_open {w v z d q : ℕ} {counts : ℕ → ℕ}
    [LinearOrder (Label q (allEvenIndices d) counts)] (hd : 5≤d)
    (T : ℕ → MvPolynomial (Fin w × Bool) K →ₗ[K] X)
    (hz : ∀ k∈allEvenIndices d,k≠2 → k≠4 → counts k=0)
    (hquad : ∃ b,QuadraticRowCapacity (v+v) d q b (allEvenIndices d) counts (constrainedOutputs T))
    (hfour : ∃ b,FourthRowCapacity w v d q b (allEvenIndices d) counts T)
    (hcore : ∀ R : allEvenIndices d,
      ∃ p : Space (v+v) d q (allEvenIndices d) counts (constrainedOutputs T),
        LinearIndependent K (fun i => intrinsicLayerMap (fun j _ => (inf_le_left : constrainedOutputs T j ≤ homogeneousSubmodule (Fin w × Bool) K j)) R i p) ∧
        (row (fun j _ => (inf_le_left : constrainedOutputs T j ≤ homogeneousSubmodule (Fin w × Bool) K j)) R p).ker=(rowConstants (fun j _ => (inf_le_left : constrainedOutputs T j ≤ homogeneousSubmodule (Fin w × Bool) K j)) R p).range)
    (hproducts : ∀ R,d<R → R≤2*d → R%2=0 →
      ∃ p : Space (v+v) d q (allEvenIndices d) counts (constrainedOutputs T),
        Function.Injective (ProductRows.multiplication counts (layers p) (allEvenIndices d) R))
    (ell : Fin 2 → Forms K (v+v) 1) (hell : LinearIndependent K ell) :
    let A := Space (v+v+z) d q (allEvenIndices d) counts (constrainedOutputs T)
    ∃ D : MvPolynomial (Fin (finrank K A)) K,
      (∃ p : A,eval ((Module.finBasis K A).equivFun p) D≠0) ∧
      ∀ p : A,eval ((Module.finBasis K A).equivFun p) D≠0 → EvenPositiveReduction p := by
  obtain ⟨hr,hp⟩ := small_extended_witnesses (z := z) hd T hz hquad hfour hcore hproducts ell hell
  exact even_reduction_open_of_witnesses (fun j _ => (inf_le_left : constrainedOutputs T j ≤ homogeneousSubmodule (Fin w × Bool) K j))
    (fun _ hj => (mem_allEvenIndices.mp hj).1)
    (fun _ hj => (mem_allEvenIndices.mp hj).2.1)
    (fun _ hj => (mem_allEvenIndices.mp hj).2.2)
    (fun r hr hrd hre => mem_allEvenIndices.mpr ⟨by omega,hrd,hre⟩) hr hp

end Froberg.PreparedParameters
