module

public import Froberg.EvenBackgroundEquivalence
public import Froberg.OddEvenAffineRelations

@[expose] public section

/-! Literal even-family multiplication transported to the even-case
Q/F coordinates. -/
noncomputable section
set_option maxHeartbeats 1200000
namespace Froberg
open Module MvPolynomial TensorProduct
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] {h m d q f e : ℕ}

def evenBackgroundProduct (hdp : 1 ≤ d)
    (Q : Fin q → Forms K m d) (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1)) :
    biformParitySpace K h m d 0 →ₗ[K] EvenBackgroundSource hdp F →ₗ[K] EvenBackgroundTarget hdp Q F where
  toFun p := (evenBackgroundTargetEquiv hdp Q F).symm.toLinearMap.comp
    ((oddBackgroundQuotientProduct (fun i => scalarEvenBiform (h := h) (Q i))
      (fun i => oddBiformEmbedding hdp (by decide) (F i)) emptyOddFamily p).comp
        (evenBackgroundSourceEquiv hdp F).toLinearMap)
  map_add' p z := by ext v; simp only [map_add,LinearMap.add_apply,LinearMap.comp_apply,LinearEquiv.map_add]
  map_smul' c p := by ext v; simp only [map_smul,LinearMap.smul_apply,LinearMap.comp_apply,LinearEquiv.map_smul,RingHom.id_apply]

theorem evenBackgroundProduct_scalar (hdp : 1 ≤ d)
    (Q : Fin q → Forms K m d) (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (p : Forms K m d) (v : EvenBackgroundSource hdp F) :
    evenBackgroundProduct hdp Q F (scalarEvenBiform p) v=evenBackgroundScalar hdp Q F p v := by
  apply (evenBackgroundTargetEquiv hdp Q F).injective
  simp only [evenBackgroundProduct,LinearMap.coe_mk,AddHom.coe_mk,LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap,LinearEquiv.apply_symm_apply]
  exact (evenBackgroundEquiv_scalar hdp Q F p v).symm

def evenRelativeFamily (hdp : 1 ≤ d)
    (Q : Fin q → Forms K m d) (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (E : Fin e → biformParitySpace K h m d 0) :
    (Fin e → EvenBackgroundSource hdp F) →ₗ[K] EvenBackgroundTarget hdp Q F :=
  ∑ i,(evenBackgroundProduct hdp Q F (E i)).comp (LinearMap.proj i)

@[simp] theorem evenRelativeFamily_apply (hdp : 1 ≤ d)
    (Q : Fin q → Forms K m d) (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (E : Fin e → biformParitySpace K h m d 0) (a : Fin e → EvenBackgroundSource hdp F) :
    evenRelativeFamily hdp Q F E a=∑ i,evenBackgroundProduct hdp Q F (E i) (a i) := by
  simp only [evenRelativeFamily,LinearMap.sum_apply,LinearMap.comp_apply,LinearMap.proj_apply]

theorem evenRelativeFamily_compatible (hdp : 1 ≤ d)
    (Q : Fin q → Forms K m d) (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (E : Fin e → biformParitySpace K h m d 0) (a : Fin e → EvenBackgroundSource hdp F) :
    evenBackgroundTargetEquiv hdp Q F (evenRelativeFamily hdp Q F E a)=
      oddEvenRelativeMap (fun i => scalarEvenBiform (h := h) (Q i))
        (fun i => oddBiformEmbedding hdp (by decide) (F i)) emptyOddFamily E
        (fun i => evenBackgroundSourceEquiv hdp F (a i)) := by
  rw [evenRelativeFamily_apply,oddEvenRelativeMap_apply,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (evenBackgroundTargetEquiv hdp Q F).apply_symm_apply _

theorem evenRelativeFamily_injective (hdp : 1 ≤ d)
    (Q : Fin q → Forms K m d) (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
    (E : Fin e → biformParitySpace K h m d 0)
    (hi : Function.Injective (oddEvenRelativeMap (fun i => scalarEvenBiform (h := h) (Q i))
      (fun i => oddBiformEmbedding hdp (by decide) (F i)) emptyOddFamily E)) :
    Function.Injective (evenRelativeFamily hdp Q F E) := by
  intro a b hab
  have he := congrArg (evenBackgroundTargetEquiv hdp Q F) hab
  rw [evenRelativeFamily_compatible,evenRelativeFamily_compatible] at he
  have hv := hi he
  funext i
  exact (evenBackgroundSourceEquiv hdp F).injective (congrFun hv i)

end Froberg
