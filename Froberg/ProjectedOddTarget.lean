module

public import Froberg.ActualParityCoefficientKernel
public import Froberg.OddBottomDetection

@[expose] public section

/-! The full target quotient after an even deletion is the actual odd
endpoint quotient when the even target is generated modulo that deletion. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace Froberg
open Module
variable {K : Type} [Field K] {n d r : ℕ}

def projectedTargetClass (D : Submodule K (Forms K n (2*d)))
    (q : Fin r → Forms K n d) :
    Forms K n (2*d) →ₗ[K] ProjectedEndpointCokernel D.mkQ q :=
  (projectedEndpointMultiplication D.mkQ q).range.mkQ.comp D.mkQ

@[simp] theorem projectedTargetClass_zero_iff (D : Submodule K (Forms K n (2*d)))
    (q : Fin r → Forms K n d) (p : Forms K n (2*d)) :
    projectedTargetClass D q p=0 ↔ p∈D ⊔ (endpointMultiplication q).range := by
  change (projectedEndpointMultiplication D.mkQ q).range.mkQ (D.mkQ p)=0 ↔ _
  change Submodule.Quotient.mk (D.mkQ p)=0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨c,hc⟩
    have hd : p-endpointMultiplication q c∈D := by
      apply (Submodule.Quotient.mk_eq_zero _).mp
      change D.mkQ (p-endpointMultiplication q c)=0
      rw [map_sub,show D.mkQ (endpointMultiplication q c)=D.mkQ p from hc,sub_self]
    have hh := Submodule.add_mem_sup hd (LinearMap.mem_range_self (endpointMultiplication q) c)
    simpa only [sub_add_cancel] using hh
  · intro hp
    obtain ⟨a,ha,b,⟨c,rfl⟩,hab⟩ := Submodule.mem_sup.mp hp
    refine ⟨c,?_⟩
    change D.mkQ (endpointMultiplication q c)=D.mkQ p
    rw [←hab,map_add,show D.mkQ a=0 from (Submodule.Quotient.mk_eq_zero _).mpr ha,zero_add]

theorem projectedTargetClass_surjective (D : Submodule K (Forms K n (2*d)))
    (q : Fin r → Forms K n d) : Function.Surjective (projectedTargetClass D q) :=
  (projectedEndpointMultiplication D.mkQ q).range.mkQ_surjective.comp D.mkQ_surjective

def projectedToOddTarget (D : Submodule K (Forms K n (2*d)))
    (w : Fin n → ZMod 2) (e : Fin r → ZMod 2)
    (q : Fin r → Forms K n d) (hq : ∀ i,(q i).val.IsWeightedHomogeneous w (e i))
    (hD : D≤(parityForm w 1).ker) :
    ProjectedEndpointCokernel D.mkQ q →ₗ[K] oddTargetSpace w q := by
  let L := D.liftQ (oddTargetClass w q) (by
    intro p hp
    apply Subtype.ext
    change (projectedEndpointMultiplication (LinearMap.id : Forms K n (2*d) →ₗ[K] _) q).range.mkQ
      (parityForm w 1 p)=0
    rw [show parityForm w 1 p=0 from hD hp,map_zero])
  exact (projectedEndpointMultiplication D.mkQ q).range.liftQ L (by
    rintro _ ⟨c,rfl⟩
    exact oddTargetClass_product w e q hq c)

@[simp] theorem projectedToOddTarget_class (D : Submodule K (Forms K n (2*d)))
    (w : Fin n → ZMod 2) (e : Fin r → ZMod 2)
    (q : Fin r → Forms K n d) (hq : ∀ i,(q i).val.IsWeightedHomogeneous w (e i))
    (hD : D≤(parityForm w 1).ker) (p : Forms K n (2*d)) :
    projectedToOddTarget D w e q hq hD (projectedTargetClass D q p)=oddTargetClass w q p := rfl

theorem projectedToOddTarget_bijective (D : Submodule K (Forms K n (2*d)))
    (w : Fin n → ZMod 2) (e : Fin r → ZMod 2)
    (q : Fin r → Forms K n d) (hq : ∀ i,(q i).val.IsWeightedHomogeneous w (e i))
    (hD : D≤(parityForm w 1).ker)
    (heven : ∀ p,parityForm w 0 p∈D ⊔ (endpointMultiplication q).range) :
    Function.Bijective (projectedToOddTarget D w e q hq hD) := by
  constructor
  · apply (LinearMap.ker_eq_bot).mp
    refine le_antisymm ?_ bot_le
    intro z hz
    obtain ⟨p,rfl⟩ := projectedTargetClass_surjective D q z
    have hp : parityForm w 1 p∈(endpointMultiplication q).range := by
      have hh := congrArg Subtype.val hz
      change (projectedEndpointMultiplication (LinearMap.id : Forms K n (2*d) →ₗ[K] _) q).range.mkQ
        (parityForm w 1 p)=0 at hh
      exact (Submodule.Quotient.mk_eq_zero _).mp hh
    change projectedTargetClass D q p=0
    apply (projectedTargetClass_zero_iff D q p).mpr
    have hsum := (D ⊔ (endpointMultiplication q).range).add_mem (heven p) ((show (endpointMultiplication q).range≤D ⊔ (endpointMultiplication q).range from le_sup_right) hp)
    have hdec : parityForm w 0 p+parityForm w 1 p=p := by
      simpa only [zero_add] using parityForm_decomposition w 0 p
    rwa [hdec] at hsum
  · intro z
    obtain ⟨p,rfl⟩ := oddTargetClass_surjective w q z
    exact ⟨projectedTargetClass D q p,rfl⟩

def projectedOddTargetEquiv (D : Submodule K (Forms K n (2*d)))
    (w : Fin n → ZMod 2) (e : Fin r → ZMod 2)
    (q : Fin r → Forms K n d) (hq : ∀ i,(q i).val.IsWeightedHomogeneous w (e i))
    (hD : D≤(parityForm w 1).ker)
    (heven : ∀ p,parityForm w 0 p∈D ⊔ (endpointMultiplication q).range) :
    ProjectedEndpointCokernel D.mkQ q ≃ₗ[K] oddTargetSpace w q :=
  LinearEquiv.ofBijective (projectedToOddTarget D w e q hq hD)
    (projectedToOddTarget_bijective D w e q hq hD heven)

@[simp] theorem projectedOddTargetEquiv_class (D : Submodule K (Forms K n (2*d)))
    (w : Fin n → ZMod 2) (e : Fin r → ZMod 2)
    (q : Fin r → Forms K n d) (hq : ∀ i,(q i).val.IsWeightedHomogeneous w (e i))
    (hD : D≤(parityForm w 1).ker)
    (heven : ∀ p,parityForm w 0 p∈D ⊔ (endpointMultiplication q).range)
    (p : Forms K n (2*d)) :
    projectedOddTargetEquiv D w e q hq hD heven (projectedTargetClass D q p)=
      oddTargetClass w q p := rfl

variable {P : Type*} [AddCommGroup P] [Module K P]

theorem projectedOddTargetEquiv_product (D : Submodule K (Forms K n (2*d)))
    (w : Fin n → ZMod 2) (e : Fin r → ZMod 2)
    (q : Fin r → Forms K n d) (hq : ∀ i,(q i).val.IsWeightedHomogeneous w (e i))
    (hD : D≤(parityForm w 1).ker)
    (heven : ∀ p,parityForm w 0 p∈D ⊔ (endpointMultiplication q).range)
    (F : P →ₗ[K] Forms K n d) (hF : ∀ p,(F p).val.IsWeightedHomogeneous w 0)
    (p : P) (a : generatorQuotient q) :
    projectedOddTargetEquiv D w e q hq hD heven (projectedQuotientProduct D.mkQ q (F p) a)=
      oddQuotientProduct w q F hF p (oddCoefficientProjection w e q hq a) := by
  obtain ⟨v,rfl⟩ := (Submodule.span K (Set.range q)).mkQ_surjective a
  apply Subtype.ext
  change (projectedEndpointMultiplication (LinearMap.id : Forms K n (2*d) →ₗ[K] _) q).range.mkQ
    (parityForm w 1 (mulForm (F p) v))=
      (projectedEndpointMultiplication (LinearMap.id : Forms K n (2*d) →ₗ[K] _) q).range.mkQ
        (mulForm (F p) (parityForm w 1 v))
  rw [parityForm_mul w 1 0 _ _ (hF p)]
  norm_num

end Froberg
