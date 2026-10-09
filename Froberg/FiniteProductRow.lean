module

public import Froberg.ConstrainedCrossPair
public import Froberg.ProductRowAssignments

@[expose] public section

/-! A finite, constrained polynomial witness for the complete formal
product row. All degree and output constraints hold for the same family. -/
noncomputable section
set_option maxHeartbeats 800000
namespace Froberg.ProductRows
open Froberg MvPolynomial Module
variable {K : Type} [Field K] [Infinite K]
variable {X : Type*} [AddCommGroup X] [Module K X] [Module.Finite K X]

/-- The actual degree constraints of a layer in a fixed row. -/
def layerCondition (w v R d j : ℕ)
    (T : MvPolynomial (Fin w × Bool) K →ₗ[K] X)
    (f : MvPolynomial (FourBlocks.Variables (Fin w) (Fin v)) K) : Prop :=
  f.IsHomogeneous d ∧
  f.IsWeightedHomogeneous (FourBlocks.outputWeight (A := Fin w × Bool) (B := Fin v × Bool)) j ∧
  f.IsWeightedHomogeneous FourBlocks.xHalfWeight (assignedDegree R j) ∧
  f.IsWeightedHomogeneous FourBlocks.yHalfWeight (assignedScalarDegree R d j) ∧
  biformOutputMap T f = 0

/-- Exact finite capacities suffice for an injective product row with the
prescribed output constraints. No separate-pair independence is assumed. -/
theorem exists_constrained_product_row {w v d R : ℕ} (hw : 0<w) (hv : 0<v)
    (J : Finset ℕ) (e : ℕ → ℕ)
    (heven : ∀ j∈J, Even j) (hdegree : ∀ j∈J, j≤d)
    (T : ℕ → MvPolynomial (Fin w × Bool) K →ₗ[K] X)
    (hdiag : ∀ r : Row J R, r.val.val=R-r.val.val →
      e r.val.val ≤ (w.choose r.val.val-finrank K X) * (v.choose (d-r.val.val)/2))
    (hcross : ∀ r : Row J R, r.val.val≠R-r.val.val →
      e r.val.val ≤ ((w+r.val.val-1).choose r.val.val-finrank K X) * (v+(d-r.val.val)-1).choose (d-r.val.val) ∧
      e (R-r.val.val) ≤ ((w+(R-r.val.val)-1).choose (R-r.val.val)-finrank K X) *
        (v+(d-(R-r.val.val))-1).choose (d-(R-r.val.val))) :
    ∃ q : (j : ℕ) → Fin (e j) → MvPolynomial (FourBlocks.Variables (Fin w) (Fin v)) K,
      (∀ j i, layerCondition w v R d j (T j) (q j i)) ∧
      Function.Injective (multiplication e q J R) := by
  classical
  let P := fun j (f : Fin (e j) → MvPolynomial (FourBlocks.Variables (Fin w) (Fin v)) K) =>
    ∀ i, layerCondition w v R d j (T j) (f i)
  have hzero : ∀ j, P j 0 := by
    intro j i
    exact ⟨(homogeneousSubmodule _ K d).zero_mem,isWeightedHomogeneous_zero K _ _,
      isWeightedHomogeneous_zero K _ _,isWeightedHomogeneous_zero K _ _,map_zero _⟩
  apply exists_injective_product_row_with_conditions e FourBlocks.xHalfWeight P hzero heven
  · intro q hq j hj i
    exact (hq j i).2.2.1
  · intro r
    have hjd := hdegree _ r.property.1
    have hld := hdegree _ r.property.2.1
    by_cases h : r.val.val=R-r.val.val
    · obtain ⟨f,hf,hi,hT,ho⟩ := exists_fourBlock_diagonal_pair
        w v r.val.val (d-r.val.val) (e r.val.val) (T r.val.val) (hdiag r h)
      have htwo : 2*r.val.val=R := by have := r.property.2.2; omega
      have hp : P r.val.val f := by
        intro i
        refine ⟨?_,ho i,?_,?_,hT i⟩
        · simpa only [Nat.add_sub_of_le hjd] using (hf i).1
        · simpa [assignedDegree,htwo] using (hf i).2.1
        · simpa [assignedScalarDegree,htwo] using (hf i).2.2
      obtain ⟨q,hq,hqf⟩ := exists_diagonal_assignment e r.val.val P hzero f hp
      refine ⟨q,hq,?_⟩
      let c : Columns e r ≃ Sym2 (Fin (e r.val.val)) := Equiv.cast (if_pos h)
      have hh := hi.comp c c.injective
      convert hh using 1
      funext p
      simp only [products,dif_pos h,hqf,Function.comp_apply]
      rfl
    · obtain ⟨f,g,hf,hg,hi,hfo,hgo⟩ := exists_constrained_fourBlock_cross_pair hw hv
        (T r.val.val) (T (R-r.val.val)) (hcross r h).1 (hcross r h).2
      have hsmall : 2*r.val.val<R := by have := r.property.2.2; omega
      have hlarge : R<2*(R-r.val.val) := by omega
      have hpf : P r.val.val f := by
        intro i
        refine ⟨?_,hfo i,?_,?_,(hf i).2.2.2⟩
        · simpa only [Nat.add_sub_of_le hjd] using (hf i).1
        · simpa [assignedDegree,hsmall] using (hf i).2.1
        · simpa [assignedScalarDegree,hsmall] using (hf i).2.2.1
      have hpg : P (R-r.val.val) g := by
        intro i
        refine ⟨?_,hgo i,?_,?_,(hg i).2.2.2⟩
        · simpa only [Nat.add_sub_of_le hld] using (hg i).1
        · simpa [assignedDegree,show ¬2*(R-r.val.val)<R by omega,
            show ¬2*(R-r.val.val)=R by omega] using (hg i).2.1
        · simpa [assignedScalarDegree,show ¬2*(R-r.val.val)<R by omega,
            show ¬2*(R-r.val.val)=R by omega] using (hg i).2.2.1
      obtain ⟨q,hq,hqf,hqg⟩ := exists_cross_assignment e h P hzero f g hpf hpg
      refine ⟨q,hq,?_⟩
      let c : Columns e r ≃ Fin (e r.val.val) × Fin (e (R-r.val.val)) := Equiv.cast (if_neg h)
      have hh := hi.comp c c.injective
      convert hh using 1
      funext p
      simp only [products,dif_neg h,hqf,hqg,Function.comp_apply]
      rfl

end Froberg.ProductRows
