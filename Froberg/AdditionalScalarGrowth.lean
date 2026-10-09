module

public import Froberg.BilinearScalarFamily
public import Quartic.BilinearImage

@[expose] public section

/-! An injective additional scalar family supplies uniform growth of every
subspace in the actual quotient. This is the C.19 augmentation argument. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module
variable {K P V W U : Type*} [Field K]
  [AddCommGroup P] [Module K P]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  [AddCommGroup U] [Module K U]
variable {q : ℕ}

theorem scalar_growth_of_injective_family (mu : P →ₗ[K] V →ₗ[K] W)
    (Q : Fin q → P) (hQ : Function.Injective (BilinearScalarFamily.multiplication mu Q))
    (L : Submodule K V) :
    q*finrank K L≤finrank K (Quartic.BilinearImage.image mu L) := by
  let inc : (Fin q → L) →ₗ[K] (Fin q → V) := LinearMap.piMap (fun _ => L.subtype)
  let F := (BilinearScalarFamily.multiplication mu Q).comp inc
  have hinc : Function.Injective inc := by
    intro x y h
    funext i
    exact Subtype.ext (congrFun h i)
  have hF : Function.Injective F := hQ.comp hinc
  have hle : F.range≤Quartic.BilinearImage.image mu L := by
    rintro _ ⟨v,rfl⟩
    change Quartic.BilinearImage.tupleMap mu (inc v) Q∈_
    rw [Quartic.BilinearImage.tupleMap_apply]
    exact Submodule.sum_mem _ (fun i _ => Quartic.BilinearImage.product_mem mu L (Q i) _ (v i).property)
  calc
    q*finrank K L=finrank K (Fin q → L) := by
      rw [Module.finrank_pi_fintype]
      simp
    _=finrank K F.range := (LinearMap.finrank_range_of_inj hF).symm
    _≤_ := Submodule.finrank_mono hle

/-- Literal multiplication followed by the quotient by the old relation image. -/
def scalarModulo (old : U →ₗ[K] W) (mu : P →ₗ[K] V →ₗ[K] W) :
    P →ₗ[K] V →ₗ[K] (W ⧸ old.range) :=
  (LinearMap.llcomp K V W (W ⧸ old.range) old.range.mkQ).comp mu

@[simp] theorem scalarModulo_apply (old : U →ₗ[K] W) (mu : P →ₗ[K] V →ₗ[K] W)
    (p : P) (v : V) : scalarModulo old mu p v=old.range.mkQ (mu p v) := rfl

/-- Injectivity before quotienting gives actual scalar-family injectivity
in the old quotient; no rank equality is assumed. -/
theorem scalarModulo_family_injective (old : U →ₗ[K] W)
    (mu : P →ₗ[K] V →ₗ[K] W) (Q : Fin q → P)
    (h : Function.Injective (old.coprod (BilinearScalarFamily.multiplication mu Q))) :
    Function.Injective (BilinearScalarFamily.multiplication (scalarModulo old mu) Q) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  have hz : old.range.mkQ (BilinearScalarFamily.multiplication mu Q v)=0 := by
    change Quartic.BilinearImage.tupleMap (scalarModulo old mu) v Q=0 at hv
    change old.range.mkQ (Quartic.BilinearImage.tupleMap mu v Q)=0
    rw [Quartic.BilinearImage.tupleMap_apply] at hv ⊢
    simpa only [scalarModulo_apply,map_sum] using hv
  have hm : BilinearScalarFamily.multiplication mu Q v∈old.range :=
    (Submodule.Quotient.mk_eq_zero old.range).mp hz
  obtain ⟨u,hu⟩ := hm
  have he : old.coprod (BilinearScalarFamily.multiplication mu Q) (-u,v)=0 := by
    simp only [LinearMap.coprod_apply,map_neg,hu,neg_add_cancel]
  have hp : (-u,v)=(0,0) := h (he.trans (map_zero _).symm)
  exact congrArg Prod.snd hp

/-- A successful additional q-tuple gives the full C.19 bound uniformly
for every source subspace in the actual old quotient. -/
theorem additional_scalar_quotient_growth (old : U →ₗ[K] W)
    (mu : P →ₗ[K] V →ₗ[K] W) (Q : Fin q → P)
    (h : Function.Injective (old.coprod (BilinearScalarFamily.multiplication mu Q)))
    (L : Submodule K V) :
    q*finrank K L≤finrank K (Quartic.BilinearImage.image (scalarModulo old mu) L) :=
  scalar_growth_of_injective_family _ Q (scalarModulo_family_injective old mu Q h) L

end Froberg
