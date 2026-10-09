module

public import Froberg.CoupledCovectors

@[expose] public section

/-! Explicit linear coordinates for the coupled bottom/top covectors.
The top coordinate is the dual of the actual quotient relation space. -/
noncomputable section
namespace Froberg
open Module
variable {K U X Y : Type*} [Field K]
  [AddCommGroup U] [Module K U] [AddCommGroup X] [Module K X]
  [AddCommGroup Y] [Module K Y]

def coupledParameterization (P : U →ₗ[K] X) (C : U →ₗ[K] Y)
    (B : Y →ₗ[K] U) (hB : Function.LeftInverse B C) :
    ((X →ₗ[K] K) × ((Y ⧸ C.range) →ₗ[K] K)) →ₗ[K] coupledCovectors P C :=
  ((LinearMap.fst K _ _).prod
    (((-precomposeDual (P.comp B)).comp (LinearMap.fst K _ _))+
      ((precomposeDual C.range.mkQ).comp (LinearMap.snd K _ _)))).codRestrict _ (by
        intro x u
        change x.1 (P u)+(-x.1 (P (B (C u)))+x.2 (C.range.mkQ (C u)))=0
        have hq : C.range.mkQ (C u)=0 := (Submodule.Quotient.mk_eq_zero _).mpr ⟨u,rfl⟩
        rw [hB u,hq,map_zero,add_zero,add_neg_cancel])

@[simp] theorem coupledParameterization_fst (P : U →ₗ[K] X) (C : U →ₗ[K] Y)
    (B : Y →ₗ[K] U) (hB : Function.LeftInverse B C)
    (x : (X →ₗ[K] K) × ((Y ⧸ C.range) →ₗ[K] K)) :
    (coupledParameterization P C B hB x).val.1=x.1 := rfl

@[simp] theorem coupledParameterization_snd (P : U →ₗ[K] X) (C : U →ₗ[K] Y)
    (B : Y →ₗ[K] U) (hB : Function.LeftInverse B C)
    (x : (X →ₗ[K] K) × ((Y ⧸ C.range) →ₗ[K] K)) (y : Y) :
    (coupledParameterization P C B hB x).val.2 y=
      -x.1 (P (B y))+x.2 (C.range.mkQ y) := rfl

theorem coupledParameterization_bijective (P : U →ₗ[K] X) (C : U →ₗ[K] Y)
    (B : Y →ₗ[K] U) (hB : Function.LeftInverse B C) :
    Function.Bijective (coupledParameterization P C B hB) := by
  constructor
  · intro x y h
    have hfst : x.1=y.1 := congrArg (fun z : coupledCovectors P C => z.val.1) h
    apply Prod.ext hfst
    apply LinearMap.ext
    intro q
    obtain ⟨v,rfl⟩ := C.range.mkQ_surjective q
    have hs := congrArg (fun z : coupledCovectors P C => z.val.2 v) h
    simp only [coupledParameterization_snd,hfst] at hs
    exact add_left_cancel hs
  · intro z
    let theta : Y →ₗ[K] K := z.val.2+(z.val.1.comp (P.comp B))
    have htheta : C.range≤theta.ker := by
      rintro _ ⟨u,rfl⟩
      change z.val.2 (C u)+z.val.1 (P (B (C u)))=0
      rw [hB u]
      simpa only [add_comm] using z.property u
    refine ⟨(z.val.1,C.range.liftQ theta htheta),?_⟩
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply LinearMap.ext
      intro y
      change -z.val.1 (P (B y))+(z.val.2 y+z.val.1 (P (B y)))=z.val.2 y
      abel

def coupledCoordinates (P : U →ₗ[K] X) (C : U →ₗ[K] Y)
    (B : Y →ₗ[K] U) (hB : Function.LeftInverse B C) :
    ((X →ₗ[K] K) × ((Y ⧸ C.range) →ₗ[K] K)) ≃ₗ[K] coupledCovectors P C :=
  LinearEquiv.ofBijective (coupledParameterization P C B hB)
    (coupledParameterization_bijective P C B hB)

/-- Injectivity of the actual top relation map supplies the required coordinates. -/
theorem exists_coupled_coordinates (P : U →ₗ[K] X) (C : U →ₗ[K] Y)
    (hC : Function.Injective C) :
    ∃ e : ((X →ₗ[K] K) × ((Y ⧸ C.range) →ₗ[K] K)) ≃ₗ[K] coupledCovectors P C,
      ∀ x,(e x).val.1=x.1 := by
  obtain ⟨B,hB⟩ := C.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hC)
  let hBC : Function.LeftInverse B C := fun u => LinearMap.congr_fun hB u
  exact ⟨coupledCoordinates P C B hBC,fun _ => rfl⟩

end Froberg
