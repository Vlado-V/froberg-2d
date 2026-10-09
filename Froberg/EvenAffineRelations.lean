module

public import Froberg.EvenRelativeQuotient
public import Froberg.EvenCovectorGrowth
public import Froberg.OddTargetBottomCoordinates

@[expose] public section

/-! Affine even relations in the Q/F background, with the actual B.7
bottom-detection consequence. -/
noncomputable section
set_option maxHeartbeats 1600000
namespace Froberg
open Module MvPolynomial TensorProduct Quartic
attribute [local instance] tensorFormGroup
variable {K : Type} [Field K] [Infinite K] {h m d q f e : ℕ}
variable (hdp : 1 ≤ d) (Q : Fin q → Forms K m d)
  (F : Fin f → Forms K h 1 ⊗[K] Forms K m (d-1))
local notation "Q₀" => fun i => scalarEvenBiform (h := h) (Q i)
local notation "F₁" => fun i => oddBiformEmbedding hdp (by decide) (F i)
local notation "V" => EvenBackgroundSource hdp F
local notation "W" => EvenBackgroundTarget hdp Q F
local notation "ec" => oddTargetBaseEquiv hdp Q₀ F₁
  (fun i => scalarEvenBiform_weighted (h := h) (Q i))
  (fun i => oddLinearBiform_weighted hdp (F i))

def evenAffineRelations (E : Fin e → biformParitySpace K h m d 0)
    (a : Fin e → Forms K m d) : Submodule K W :=
  (evenRelativeFamily hdp Q F (oddEvenAffineFamily E a)).range

theorem evenAffineRelations_generator_mem (E : Fin e → biformParitySpace K h m d 0)
    (a : Fin e → Forms K m d) (i : Fin e) (v : V) :
    evenBackgroundScalar hdp Q F (a i) v+evenBackgroundProduct hdp Q F (E i) v ∈
      evenAffineRelations hdp Q F E a := by
  classical
  refine ⟨Pi.single i v,?_⟩
  rw [evenRelativeFamily_apply,Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
    change evenBackgroundProduct hdp Q F (E i+scalarEvenBiform (a i)) v=_
    rw [map_add,LinearMap.add_apply,evenBackgroundProduct_scalar,add_comm]
  · intro j _ hji
    rw [Pi.single_eq_of_ne hji,map_zero]
  · simp

theorem evenAffineRelations_finrank (E : Fin e → biformParitySpace K h m d 0)
    (a : Fin e → Forms K m d)
    (hi : Function.Injective (oddEvenRelativeMap Q₀ F₁ emptyOddFamily (oddEvenAffineFamily E a))) :
    finrank K (W ⧸ evenAffineRelations hdp Q F E a)=finrank K W-e*finrank K V := by
  exact Nat.eq_sub_of_add_eq (injective_pi_quotient_finrank
    (evenRelativeFamily hdp Q F (oddEvenAffineFamily E a))
    (evenRelativeFamily_injective hdp Q F _ hi)).symm

theorem even_affine_bottom_detects (E : Fin e → biformParitySpace K h m d 0)
    (a : Fin e → Forms K m d)
    (hupper : Function.Surjective (upperTargetMap
      (backgroundEnumeratedForms (Fin.append Q₀ (oddEvenAffineFamily E a)) F₁ emptyOddFamily)))
    (ell : W →ₗ[K] K) (hA : evenAffineRelations hdp Q F E a ≤ ell.ker)
    (hb : splitTargetBottom ec ell=0) : ell=0 := by
  let ell' := ell.comp (evenBackgroundTargetEquiv hdp Q F).symm.toLinearMap
  have hzero : ell'=0 := by
    apply odd_even_append_bottom_detects Q₀ F₁ emptyOddFamily (oddEvenAffineFamily E a) hupper ell'
    · rintro _ ⟨v,rfl⟩
      let v' := fun i => (evenBackgroundSourceEquiv hdp F).symm (v i)
      have hv := evenRelativeFamily_compatible hdp Q F (oddEvenAffineFamily E a) v'
      have hvv : (fun i => evenBackgroundSourceEquiv hdp F (v' i))=v := by
        funext i
        exact (evenBackgroundSourceEquiv hdp F).apply_symm_apply _
      rw [hvv] at hv
      change ell ((evenBackgroundTargetEquiv hdp Q F).symm _)=0
      rw [←hv,LinearEquiv.symm_apply_apply]
      exact hA ⟨v',rfl⟩
    · intro v hv
      have he := splitTarget_evaluation ec ell ((oddBackgroundRelations Q₀ F₁).mkQ v)
      have hz : (ec ((oddBackgroundRelations Q₀ F₁).mkQ v)).2=0 :=
        oddTargetBaseMap_weighted_higher_zero hdp Q₀ F₁ _ _ v hv
      rw [hz,hb,LinearMap.zero_apply,map_zero,zero_add] at he
      exact he
  apply LinearMap.ext
  intro x
  have hx := congrArg (fun z : _ →ₗ[K] K => z (evenBackgroundTargetEquiv hdp Q F x)) hzero
  simpa only [ell',LinearMap.comp_apply,LinearEquiv.coe_toLinearMap,
    LinearEquiv.symm_apply_apply,LinearMap.zero_apply] using hx

end Froberg
