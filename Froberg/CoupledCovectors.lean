module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Tactic

@[expose] public section

/-! Coupled low/top covectors in odd degree. An injective top relation map
makes every bottom covector extend, and its extensions form precisely an
affine translate of the dual top quotient. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg
open Module
variable {K U X Y : Type*} [Field K]
  [AddCommGroup U] [Module K U] [AddCommGroup X] [Module K X]
  [AddCommGroup Y] [Module K Y]

/-- All actual low/top covectors satisfying the mixed generator relation. -/
def coupledCovectors (P : U →ₗ[K] X) (C : U →ₗ[K] Y) :
    Submodule K ((X →ₗ[K] K) × (Y →ₗ[K] K)) where
  carrier := {z | ∀ u,z.1 (P u)+z.2 (C u)=0}
  zero_mem' := by intro u; simp
  add_mem' := by
    intro z w hz hw u
    change z.1 (P u)+w.1 (P u)+(z.2 (C u)+w.2 (C u))=0
    linear_combination hz u+hw u
  smul_mem' := by
    intro k z hz u
    change k*z.1 (P u)+k*z.2 (C u)=0
    rw [←mul_add,hz u,mul_zero]

/-- Restriction to the bottom covector is an actual linear map. -/
def coupledRestriction (P : U →ₗ[K] X) (C : U →ₗ[K] Y) :
    coupledCovectors P C →ₗ[K] (X →ₗ[K] K) :=
  (LinearMap.fst K _ _).comp (coupledCovectors P C).subtype

theorem coupledRestriction_surjective (P : U →ₗ[K] X) (C : U →ₗ[K] Y)
    (hC : Function.Injective C) : Function.Surjective (coupledRestriction P C) := by
  obtain ⟨p,hp⟩ := C.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hC)
  intro ell
  refine ⟨⟨(ell,-((ell.comp P).comp p)),?_⟩,rfl⟩
  intro u
  change ell (P u)+ -ell (P (p (C u)))=0
  have he : p (C u)=u := LinearMap.congr_fun hp u
  rw [he,add_neg_cancel]

/-- Differences of two extensions are exactly covectors annihilating the
injected relation space. This is the affine-fiber assertion in C.12. -/
theorem coupled_extension_difference (P : U →ₗ[K] X) (C : U →ₗ[K] Y)
    (ell : X →ₗ[K] K) (eta theta : Y →ₗ[K] K)
    (heta : (ell,eta)∈coupledCovectors P C) :
    (ell,theta)∈coupledCovectors P C ↔ (theta-eta).comp C=0 := by
  constructor
  · intro ht
    ext u
    have he := heta u
    have hf := ht u
    change theta (C u)-eta (C u)=0
    linear_combination hf-he
  · intro h u
    have he := LinearMap.congr_fun h u
    change theta (C u)-eta (C u)=0 at he
    have hf := heta u
    change ell (P u)+theta (C u)=0
    linear_combination hf+he

/-- Restriction of a linear functional along the specified map. -/
def precomposeDual (C : U →ₗ[K] Y) : (Y →ₗ[K] K) →ₗ[K] (U →ₗ[K] K) where
  toFun ell := ell.comp C
  map_add' ell eta := rfl
  map_smul' c ell := rfl

/-- The direction of the extension fiber is literally the dual of the top
quotient, by the universal property of that quotient. -/
def topExtensionDirectionEquiv (C : U →ₗ[K] Y) :
    ((Y ⧸ C.range) →ₗ[K] K) ≃ₗ[K]
      LinearMap.ker (precomposeDual C) := by
  let F : ((Y ⧸ C.range) →ₗ[K] K) →ₗ[K] (Y →ₗ[K] K) :=
    precomposeDual C.range.mkQ
  have hF : ∀ ell,F ell∈LinearMap.ker (precomposeDual C) := by
    intro ell
    ext u
    change ell (C.range.mkQ (C u))=0
    have hz : C.range.mkQ (C u)=0 := by
      exact (Submodule.Quotient.mk_eq_zero C.range).mpr ⟨u,rfl⟩
    rw [hz,map_zero]
  let G := F.codRestrict _ hF
  apply LinearEquiv.ofBijective G
  constructor
  · intro ell eta he
    apply LinearMap.ext
    intro y
    obtain ⟨x,rfl⟩ := C.range.mkQ_surjective y
    exact congrArg (fun z : LinearMap.ker (precomposeDual C) => z.val x) he
  · intro ell
    have hk : C.range≤ell.val.ker := by
      rintro _ ⟨u,rfl⟩
      exact LinearMap.congr_fun ell.property u
    refine ⟨C.range.liftQ ell.val hk,?_⟩
    apply Subtype.ext
    ext y
    rfl

end Froberg
