import Froberg.GraphQuotientCoordinates
import Mathlib.LinearAlgebra.Pi

/-! Elementary quotient coordinates used to isolate the bottom odd row. -/
noncomputable section
namespace Froberg
open Module
variable {K : Type*} [Field K]

def piSplitAtLinear {I : Type*} [DecidableEq I] (V : I → Type*)
    [∀ i,AddCommGroup (V i)] [∀ i,Module K (V i)] (i : I) :
    ((j : I) → V j) ≃ₗ[K] V i × ((j : {j // j≠i}) → V j.val) :=
  { Equiv.piSplitAt i V with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

variable {X Y : Type*} [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]

def productLeftQuotientMap (T : Submodule K X) : (X × Y) →ₗ[K] (X ⧸ T) × Y :=
  T.mkQ.prodMap (LinearMap.id : Y →ₗ[K] Y)

theorem productLeftQuotientMap_kernel (T : Submodule K X) :
    (productLeftQuotientMap (Y := Y) T).ker=T.map (LinearMap.inl K X Y) := by
  ext z
  rcases z with ⟨x,y⟩
  constructor
  · intro hz
    have hx : T.mkQ x=0 := congrArg Prod.fst hz
    have hy : y=0 := congrArg Prod.snd hz
    exact ⟨x,(Submodule.Quotient.mk_eq_zero T).mp hx,Prod.ext rfl hy.symm⟩
  · rintro ⟨z,hz,he⟩
    rw [←he]
    change (T.mkQ z,(0 : Y))=(0,0)
    exact Prod.ext ((Submodule.Quotient.mk_eq_zero T).mpr hz) rfl

theorem productLeftQuotientMap_surjective (T : Submodule K X) :
    Function.Surjective (productLeftQuotientMap (Y := Y) T) := by
  rintro ⟨x,y⟩
  obtain ⟨z,rfl⟩ := T.mkQ_surjective x
  exact ⟨(z,y),rfl⟩

def productLeftQuotientEquiv (T : Submodule K X) :
    ((X × Y) ⧸ T.map (LinearMap.inl K X Y)) ≃ₗ[K] (X ⧸ T) × Y :=
  (Submodule.quotEquivOfEq _ _ (productLeftQuotientMap_kernel T).symm).trans
    ((productLeftQuotientMap T).quotKerEquivOfSurjective
      (productLeftQuotientMap_surjective T))

@[simp] theorem productLeftQuotientEquiv_mk (T : Submodule K X) (x : X) (y : Y) :
    productLeftQuotientEquiv T ((T.map (LinearMap.inl K X Y)).mkQ (x,y))=(T.mkQ x,y) := rfl

end Froberg
