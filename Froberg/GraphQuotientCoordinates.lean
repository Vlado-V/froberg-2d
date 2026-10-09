module

public import Froberg.CoupledCoordinates

@[expose] public section

/-! Explicit source coordinates for the odd mixed quotient. A graph
relation with injective top coordinate can be eliminated while preserving
the bottom coordinate subspace. -/
noncomputable section
namespace Froberg
open Module
variable {K U X Y : Type*} [Field K]
  [AddCommGroup U] [Module K U] [AddCommGroup X] [Module K X]
  [AddCommGroup Y] [Module K Y]

def graphQuotientCoordinatesMap (P : U →ₗ[K] X) (C : U →ₗ[K] Y) (B : Y →ₗ[K] U) :
    (X × Y) →ₗ[K] X × (Y ⧸ C.range) :=
  ((LinearMap.fst K X Y)-(P.comp B).comp (LinearMap.snd K X Y)).prod
    (C.range.mkQ.comp (LinearMap.snd K X Y))

@[simp] theorem graphQuotientCoordinatesMap_apply
    (P : U →ₗ[K] X) (C : U →ₗ[K] Y) (B : Y →ₗ[K] U) (x : X) (y : Y) :
    graphQuotientCoordinatesMap P C B (x,y)=(x-P (B y),C.range.mkQ y) := rfl

theorem graphQuotientCoordinatesMap_kernel
    (P : U →ₗ[K] X) (C : U →ₗ[K] Y) (B : Y →ₗ[K] U)
    (hB : B.comp C=LinearMap.id) :
    (graphQuotientCoordinatesMap P C B).ker=(P.prod C).range := by
  ext z
  rcases z with ⟨x,y⟩
  constructor
  · intro hz
    have hx : x-P (B y)=0 := congrArg Prod.fst hz
    have hy : C.range.mkQ y=0 := congrArg Prod.snd hz
    obtain ⟨u,rfl⟩ := (Submodule.Quotient.mk_eq_zero C.range).mp hy
    have hu : B (C u)=u := LinearMap.congr_fun hB u
    exact ⟨u,Prod.ext (by simpa [hu] using (sub_eq_zero.mp hx).symm) rfl⟩
  · rintro ⟨u,huv⟩
    rw [←huv]
    change (P u-P (B (C u)),C.range.mkQ (C u))=(0,0)
    have hu : B (C u)=u := LinearMap.congr_fun hB u
    simp only [hu,sub_self,Prod.mk.injEq,true_and]
    exact (Submodule.Quotient.mk_eq_zero C.range).mpr ⟨u,rfl⟩

theorem graphQuotientCoordinatesMap_surjective
    (P : U →ₗ[K] X) (C : U →ₗ[K] Y) (B : Y →ₗ[K] U) :
    Function.Surjective (graphQuotientCoordinatesMap P C B) := by
  rintro ⟨x,y⟩
  obtain ⟨z,rfl⟩ := C.range.mkQ_surjective y
  exact ⟨(x+P (B z),z),by simp⟩

def graphQuotientCoordinates (P : U →ₗ[K] X) (C : U →ₗ[K] Y) (B : Y →ₗ[K] U)
    (hB : B.comp C=LinearMap.id) :
    ((X × Y) ⧸ (P.prod C).range) ≃ₗ[K] X × (Y ⧸ C.range) :=
  (Submodule.quotEquivOfEq _ _ (graphQuotientCoordinatesMap_kernel P C B hB).symm).trans
    ((graphQuotientCoordinatesMap P C B).quotKerEquivOfSurjective
      (graphQuotientCoordinatesMap_surjective P C B))

theorem exists_graph_quotient_coordinates
    (P : U →ₗ[K] X) (C : U →ₗ[K] Y) (hC : Function.Injective C) :
    Nonempty (((X × Y) ⧸ (P.prod C).range) ≃ₗ[K] X × (Y ⧸ C.range)) := by
  obtain ⟨B,hB⟩ := C.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hC)
  exact ⟨graphQuotientCoordinates P C B hB⟩

end Froberg
