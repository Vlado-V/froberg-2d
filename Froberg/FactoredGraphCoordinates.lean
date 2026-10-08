import Froberg.GraphQuotientCoordinates
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! Graph elimination when the presentation of the graph has a kernel.
The bottom map must vanish on precisely the relations already killed by
the higher map; no injectivity of the presentation is assumed. -/
noncomputable section
namespace Froberg
open Module
variable {K U X Y : Type*} [Field K]
  [AddCommGroup U] [Module K U] [AddCommGroup X] [Module K X]
  [AddCommGroup Y] [Module K Y]

theorem exists_graph_correction (P : U →ₗ[K] X) (C : U →ₗ[K] Y)
    (hker : C.ker ≤ P.ker) : ∃ D : Y →ₗ[K] X, D.comp C=P := by
  let p : C.range →ₗ[K] X := C.rangeRestrict.liftOfSurjective
    (by rintro ⟨y,u,rfl⟩; exact ⟨u,rfl⟩) ⟨P,by simpa using hker⟩
  obtain ⟨D,hD⟩ := p.exists_extend
  refine ⟨D,?_⟩
  apply LinearMap.ext
  intro u
  have he := LinearMap.congr_fun hD (C.rangeRestrict u)
  exact he.trans (LinearMap.equivOfSurjective_apply _ _)

def factoredGraphMap (D : Y →ₗ[K] X) (C : U →ₗ[K] Y) :
    (X × Y) →ₗ[K] X × (Y ⧸ C.range) :=
  ((LinearMap.fst K X Y)-D.comp (LinearMap.snd K X Y)).prod
    (C.range.mkQ.comp (LinearMap.snd K X Y))

theorem factoredGraphMap_kernel (P : U →ₗ[K] X) (C : U →ₗ[K] Y)
    (D : Y →ₗ[K] X) (hD : D.comp C=P) :
    (factoredGraphMap D C).ker=(P.prod C).range := by
  ext z
  rcases z with ⟨x,y⟩
  constructor
  · intro hz
    have hx : x-D y=0 := congrArg Prod.fst hz
    have hy : C.range.mkQ y=0 := congrArg Prod.snd hz
    obtain ⟨u,rfl⟩ := (Submodule.Quotient.mk_eq_zero C.range).mp hy
    refine ⟨u,Prod.ext ?_ rfl⟩
    change P u=x
    exact (LinearMap.congr_fun hD u).symm.trans (sub_eq_zero.mp hx).symm
  · rintro ⟨u,he⟩
    rw [←he]
    change (P u-D (C u),C.range.mkQ (C u))=(0,0)
    rw [show D (C u)=P u from LinearMap.congr_fun hD u,sub_self]
    exact Prod.ext rfl ((Submodule.Quotient.mk_eq_zero C.range).mpr ⟨u,rfl⟩)

theorem factoredGraphMap_surjective (D : Y →ₗ[K] X) (C : U →ₗ[K] Y) :
    Function.Surjective (factoredGraphMap D C) := by
  rintro ⟨x,y⟩
  obtain ⟨z,rfl⟩ := C.range.mkQ_surjective y
  exact ⟨(x+D z,z),by simp [factoredGraphMap]⟩

def factoredGraphCoordinates (P : U →ₗ[K] X) (C : U →ₗ[K] Y)
    (D : Y →ₗ[K] X) (hD : D.comp C=P) :
    ((X × Y) ⧸ (P.prod C).range) ≃ₗ[K] X × (Y ⧸ C.range) :=
  (Submodule.quotEquivOfEq _ _ (factoredGraphMap_kernel P C D hD).symm).trans
    ((factoredGraphMap D C).quotKerEquivOfSurjective (factoredGraphMap_surjective D C))

@[simp] theorem factoredGraphCoordinates_mk (P : U →ₗ[K] X) (C : U →ₗ[K] Y)
    (D : Y →ₗ[K] X) (hD : D.comp C=P) (x : X) (y : Y) :
    factoredGraphCoordinates P C D hD ((P.prod C).range.mkQ (x,y))=
      (x-D y,C.range.mkQ y) := rfl

@[simp] theorem factoredGraphCoordinates_bottom (P : U →ₗ[K] X) (C : U →ₗ[K] Y)
    (D : Y →ₗ[K] X) (hD : D.comp C=P) (x : X) :
    factoredGraphCoordinates P C D hD ((P.prod C).range.mkQ (x,0))=(x,0) := by
  rw [factoredGraphCoordinates_mk,map_zero,map_zero,sub_zero]

end Froberg
