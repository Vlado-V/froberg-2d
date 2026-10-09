module

public import Quartic.MovingMiddleCorrectionOmega

@[expose] public section

/-! The optional extra column in D.12 enlarges the distinguished trace
space by exactly one while preserving its disjointness from mixed products. -/
noncomputable section
namespace Quartic.ExtraTraceOmega
open Module HomologyCoordinates AugmentedGenericOmega MovingMiddleCorrectionOmega
variable {K S A : Type*} [Field K] [AddCommGroup S] [Module K S]
  [AddCommGroup A] [Module K A]
variable (ω : K)

def withColumn (F : S →ₗ[K] A × A) (z : A × A) : (S × K) →ₗ[K] A × A :=
  F.coprod (LinearMap.toSpanSingleton K _ z)

theorem product_injective (F : S →ₗ[K] A × A) (z : A × A) (r : Fin 4 → A)
    (ha : Function.Injective (augmented ω (withColumn F z) r)) : Function.Injective F := by
  intro b b' he
  have hi := MovingMiddleCorrectionOmega.product_injective ω (withColumn F z) r ha
  have h : withColumn F z (b,0) = withColumn F z (b',0) := by
    simpa [withColumn] using he
  exact congrArg Prod.fst (hi h)

def extraTrace (z : A × A) (r : Fin 4 → A) (U : Submodule K A) :
    (K × (U × BlockHomology K)) →ₗ[K] A × A :=
  (LinearMap.toSpanSingleton K _ z).coprod (traceMap ω r U)

@[simp] theorem extraTrace_apply (z : A × A) (r : Fin 4 → A) (U : Submodule K A)
    (t : K) (a : U) (ξ : BlockHomology K) :
    extraTrace ω z r U (t,a,ξ) = t • z + traceMap ω r U (a,ξ) := rfl

theorem augmented_decomposition (F : S →ₗ[K] A × A) (z : A × A)
    (r : Fin 4 → A) (U : Submodule K A) (b : S) (t : K) (a : U) (ξ : BlockHomology K) :
    augmented ω (withColumn F z) r ((b,t),a.val,ξ) =
      F b + extraTrace ω z r U (t,a,ξ) := by
  rw [MovingMiddleCorrectionOmega.augmented_decomposition ω _ r U]
  change (F b + t • z) + traceMap ω r U (a,ξ) = _
  exact add_assoc _ _ _

theorem extraTrace_injective (F : S →ₗ[K] A × A) (z : A × A) (r : Fin 4 → A)
    (ha : Function.Injective (augmented ω (withColumn F z) r)) (U : Submodule K A) :
    Function.Injective (extraTrace ω z r U) := by
  rintro ⟨t,a,ξ⟩ ⟨t',a',ξ'⟩ he
  have h : augmented ω (withColumn F z) r ((0,t),a.val,ξ) =
      augmented ω (withColumn F z) r ((0,t'),a'.val,ξ') := by
    rw [augmented_decomposition ω F z r U, augmented_decomposition ω F z r U, he]
  have h' := ha h
  exact Prod.ext (congrArg (fun p => p.1.2) h')
    (Prod.ext (Subtype.ext (congrArg (fun p => p.2.1) h'))
      (congrArg (fun p => p.2.2) h'))

theorem product_disjoint_extraTrace (F : S →ₗ[K] A × A) (z : A × A) (r : Fin 4 → A)
    (ha : Function.Injective (augmented ω (withColumn F z) r)) (U : Submodule K A) :
    Disjoint F.range (extraTrace ω z r U).range := by
  apply Submodule.disjoint_def.mpr
  rintro p ⟨b,hb⟩ ⟨⟨t,a,ξ⟩,ht⟩
  have he : augmented ω (withColumn F z) r ((b,0),0,0) =
      augmented ω (withColumn F z) r ((0,t),a.val,ξ) := by
    rw [augmented_decomposition ω F z r U 0 t a ξ]
    simpa [AugmentedGenericOmega.augmented_apply, withColumn] using hb.trans ht.symm
  have hb0 : b = 0 := congrArg (fun p => p.1.1) (ha he)
  simpa only [hb0,map_zero] using hb.symm

theorem extraTrace_finrank [FiniteDimensional K A]
    (F : S →ₗ[K] A × A) (z : A × A) (r : Fin 4 → A)
    (ha : Function.Injective (augmented ω (withColumn F z) r)) (U : Submodule K A) :
    finrank K (extraTrace ω z r U).range = finrank K U + 4 := by
  rw [LinearMap.finrank_range_of_inj (extraTrace_injective ω F z r ha U),
    Module.finrank_prod, Module.finrank_prod]
  have hH : finrank K (BlockHomology K) = 3 :=
    ((HomologyCoordinates.homologyEquiv (K := K)).finrank_eq).symm.trans (by simp)
  simp only [Module.finrank_self, hH]
  omega

end Quartic.ExtraTraceOmega
