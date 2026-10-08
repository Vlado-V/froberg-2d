import Froberg.AdditionalScalarGrowth
import Froberg.TwoFamilyIntrinsic

/-! Splitting off additional scalar columns preserves the actual old family
and supplies uniform growth in its quotient. -/
noncomputable section
namespace Froberg
open Module
variable {K P V W A : Type*} [Field K]
  [AddCommGroup P] [Module K P] [FiniteDimensional K P]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  [AddCommGroup A] [Module K A]
variable {q r : ℕ}

theorem scalar_family_append (mu : P →ₗ[K] V →ₗ[K] W)
    (Q : Fin q → P) (R : Fin r → P) (x : Fin q → V) (y : Fin r → V) :
    BilinearScalarFamily.multiplication mu (Fin.append Q R) (Fin.append x y)=
      BilinearScalarFamily.multiplication mu Q x+BilinearScalarFamily.multiplication mu R y := by
  simp [BilinearScalarFamily.multiplication_apply,Fin.sum_univ_add]

theorem scalar_append_coprod_injective (f : A →ₗ[K] W)
    (mu : P →ₗ[K] V →ₗ[K] W) (Q : Fin q → P) (R : Fin r → P)
    (h : Function.Injective (f.coprod (BilinearScalarFamily.multiplication mu (Fin.append Q R)))) :
    Function.Injective ((f.coprod (BilinearScalarFamily.multiplication mu Q)).coprod
      (BilinearScalarFamily.multiplication mu R)) := by
  rintro ⟨⟨a,x⟩,y⟩ ⟨⟨a',x'⟩,y'⟩ he
  have he' : f.coprod (BilinearScalarFamily.multiplication mu (Fin.append Q R))
      (a,Fin.append x y)=f.coprod (BilinearScalarFamily.multiplication mu (Fin.append Q R))
      (a',Fin.append x' y') := by
    simpa only [LinearMap.coprod_apply,scalar_family_append,add_assoc] using he
  have hh := h he'
  have ha : a=a' := congrArg Prod.fst hh
  have hp : Fin.append x y=Fin.append x' y' := congrArg Prod.snd hh
  have hx : x=x' := by
    funext i
    simpa using congrFun hp (Fin.castAdd r i)
  have hy : y=y' := by
    funext i
    simpa using congrFun hp (Fin.natAdd q i)
  subst a'
  subst x'
  subst y'
  rfl

theorem scalar_augmentation_growth (f : A →ₗ[K] W)
    (mu : P →ₗ[K] V →ₗ[K] W) (Q : Fin q → P) (R : Fin r → P)
    (h : Function.Injective (f.coprod (BilinearScalarFamily.multiplication mu (Fin.append Q R))))
    (L : Submodule K V) :
    r*finrank K L≤finrank K (Quartic.BilinearImage.image
      (scalarModulo (f.coprod (BilinearScalarFamily.multiplication mu Q)) mu) L) :=
  additional_scalar_quotient_growth _ mu R (scalar_append_coprod_injective f mu Q R h) L

end Froberg
