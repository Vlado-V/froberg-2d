import Froberg.OddBackgroundBlocks
import Froberg.OddSourceBaseCoordinates
import Froberg.ProjectedQuotientEquiv
import Froberg.FactoredGraphCoordinates

/-! All rows of the actual Q,F target quotient, with its bottom row
separated before the mixed private scalar relations are imposed. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial TensorProduct
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] {h m d q f u : ℕ}

def oddTargetBottomIndex (hd : 1≤d) : Fin ((2*d+1)/2) := ⟨0,by omega⟩

abbrev OddTargetRowQuotient
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1) (r : Fin ((2*d+1)/2)) :=
  OddTargetBlock K h m d r ⧸ coordinateRelation (oddBackgroundBlockRelations Q F) r

instance oddTargetRowQuotientGroup
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1) (r : Fin ((2*d+1)/2)) :
    AddCommGroup (OddTargetRowQuotient Q F r) := Submodule.Quotient.addCommGroup _

instance oddTargetRowQuotientModule
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1) (r : Fin ((2*d+1)/2)) :
    Module K (OddTargetRowQuotient Q F r) := Submodule.Quotient.module _

abbrev HigherOddTargetRows (hd : 1≤d)
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1) :=
  (r : {r : Fin ((2*d+1)/2) // r≠oddTargetBottomIndex hd}) → OddTargetRowQuotient Q F r.val

instance higherOddTargetRowsGroup (hd : 1≤d)
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1) :
    AddCommGroup (HigherOddTargetRows hd Q F) := Pi.addCommGroup

instance higherOddTargetRowsModule (hd : 1≤d)
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1) :
    Module K (HigherOddTargetRows hd Q F) := Pi.module _ _ _

abbrev OddTargetBaseSpace (hd : 1≤d)
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1) :=
  OddTargetRowQuotient Q F (oddTargetBottomIndex hd) × HigherOddTargetRows hd Q F

instance oddTargetBaseSpaceGroup (hd : 1≤d)
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1) :
    AddCommGroup (OddTargetBaseSpace hd Q F) := Prod.instAddCommGroup

instance oddTargetBaseSpaceModule (hd : 1≤d)
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1) :
    Module K (OddTargetBaseSpace hd Q F) := Prod.instModule

def oddTargetBaseEquiv (hd : 1≤d)
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1)
    (hQ : ∀ i,(Q i).val.IsWeightedHomogeneous (blockWeight h m) 0)
    (hF : ∀ i,(F i).val.IsWeightedHomogeneous (blockWeight h m) 1) :
    (biformParitySpace K h m (2*d) 1 ⧸ oddBackgroundRelations Q F) ≃ₗ[K]
      OddTargetBaseSpace hd Q F :=
  (oddBackgroundBlocksEquiv Q F hQ hF).trans
    (piSplitAtLinear (OddTargetRowQuotient Q F) (oddTargetBottomIndex hd))

def oddTargetBaseMap (hd : 1≤d)
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1)
    (hQ : ∀ i,(Q i).val.IsWeightedHomogeneous (blockWeight h m) 0)
    (hF : ∀ i,(F i).val.IsWeightedHomogeneous (blockWeight h m) 1) :
    biformParitySpace K h m (2*d) 1 →ₗ[K] OddTargetBaseSpace hd Q F :=
  (oddTargetBaseEquiv hd Q F hQ hF).toLinearMap.comp (oddBackgroundRelations Q F).mkQ

theorem oddTargetBaseMap_surjective (hd : 1≤d)
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1)
    (hQ : ∀ i,(Q i).val.IsWeightedHomogeneous (blockWeight h m) 0)
    (hF : ∀ i,(F i).val.IsWeightedHomogeneous (blockWeight h m) 1) :
    Function.Surjective (oddTargetBaseMap hd Q F hQ hF) :=
  (oddTargetBaseEquiv hd Q F hQ hF).surjective.comp (Submodule.mkQ_surjective _)

theorem oddTargetBaseMap_kernel (hd : 1≤d)
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1)
    (hQ : ∀ i,(Q i).val.IsWeightedHomogeneous (blockWeight h m) 0)
    (hF : ∀ i,(F i).val.IsWeightedHomogeneous (blockWeight h m) 1) :
    (oddTargetBaseMap hd Q F hQ hF).ker=oddBackgroundRelations Q F := by
  ext p
  change (oddTargetBaseEquiv hd Q F hQ hF) ((oddBackgroundRelations Q F).mkQ p)=0 ↔ _
  rw [LinearEquiv.map_eq_zero_iff]
  exact Submodule.Quotient.mk_eq_zero _

@[simp] theorem oddTargetBaseMap_bottom (hd : 1≤d)
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1)
    (hQ : ∀ i,(Q i).val.IsWeightedHomogeneous (blockWeight h m) 0)
    (hF : ∀ i,(F i).val.IsWeightedHomogeneous (blockWeight h m) 1)
    (p : biformParitySpace K h m (2*d) 1) :
    (oddTargetBaseMap hd Q F hQ hF p).1=
      (coordinateRelation (oddBackgroundBlockRelations Q F) (oddTargetBottomIndex hd)).mkQ
        (oddBiformCoordinatesEquiv p (oddTargetBottomIndex hd)) := rfl

@[simp] theorem oddTargetBaseMap_higher (hd : 1≤d)
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1)
    (hQ : ∀ i,(Q i).val.IsWeightedHomogeneous (blockWeight h m) 0)
    (hF : ∀ i,(F i).val.IsWeightedHomogeneous (blockWeight h m) 1)
    (p : biformParitySpace K h m (2*d) 1)
    (r : {r : Fin ((2*d+1)/2) // r≠oddTargetBottomIndex hd}) :
    (oddTargetBaseMap hd Q F hQ hF p).2 r=
      (coordinateRelation (oddBackgroundBlockRelations Q F) r.val).mkQ
        (oddBiformCoordinatesEquiv p r.val) := rfl

end Froberg
