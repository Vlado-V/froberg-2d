module

public import Froberg.RestoredOuterIndependence
public import Froberg.UpperTargetOpen

@[expose] public section

/-! The restored endpoint is a linear polynomial family on its full
coefficient space, so successful upper-target generation is rank-open. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial Quartic
variable {K : Type} [Field K] [Infinite K] {h m d q r f : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ} {O : ℕ → Submodule K (Poly K h)}

theorem restoredOuterEndpoint_back (hdp : 1≤d) (hd : d%2=0)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (idx : Fin r ≃ Label q J counts) (slot : Fin (finrank K (Forms K h d)) → Fin r)
    (p : RestoredOuterSpace m d q f J counts O) (i : Fin r ⊕ Fin f) :
    rename finSumFinEquiv.symm (restoredOuterEndpoint hdp hd hO hJ heven idx slot p (finSumFinEquiv i)).val=
      Sum.elim (fun j => (restoredFamilyLinear hd hO hJ heven idx slot p.1 j).val)
        (fun j => (p.2 j).val) i := by
  rw [restoredOuterEndpoint,biformSplitEndpoint_back]
  cases i with
  | inl i => rfl
  | inr i =>
    change sumBiformMap (linearOutputTensorEquiv (PreparedTarget.outerVectorEquiv.symm (p.2 i)))=(p.2 i).val
    rw [←PreparedTarget.outerVectorEquiv_val,LinearEquiv.apply_symm_apply]

def restoredOuterEndpointLinear (hdp : 1≤d) (hd : d%2=0)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (idx : Fin r ≃ Label q J counts) (slot : Fin (finrank K (Forms K h d)) → Fin r) :
    RestoredOuterSpace m d q f J counts O →ₗ[K] (Fin (r+f) → Forms K (h+m) d) where
  toFun := restoredOuterEndpoint hdp hd hO hJ heven idx slot
  map_add' p p' := by
    funext i
    obtain ⟨i,rfl⟩ := finSumFinEquiv.surjective i
    apply Subtype.ext
    apply (renameEquiv K finSumFinEquiv.symm).injective
    change rename finSumFinEquiv.symm
      (restoredOuterEndpoint hdp hd hO hJ heven idx slot (p+p') (finSumFinEquiv i)).val=
      rename finSumFinEquiv.symm ((restoredOuterEndpoint hdp hd hO hJ heven idx slot p (finSumFinEquiv i)).val+
        (restoredOuterEndpoint hdp hd hO hJ heven idx slot p' (finSumFinEquiv i)).val)
    rw [map_add,restoredOuterEndpoint_back,restoredOuterEndpoint_back,restoredOuterEndpoint_back]
    cases i with
    | inl i => exact congrArg Subtype.val (congrFun (map_add (restoredFamilyLinear hd hO hJ heven idx slot) p.1 p'.1) i)
    | inr i => rfl
  map_smul' a p := by
    funext i
    obtain ⟨i,rfl⟩ := finSumFinEquiv.surjective i
    apply Subtype.ext
    apply (renameEquiv K finSumFinEquiv.symm).injective
    change rename finSumFinEquiv.symm
      (restoredOuterEndpoint hdp hd hO hJ heven idx slot (a • p) (finSumFinEquiv i)).val=
      rename finSumFinEquiv.symm (a • (restoredOuterEndpoint hdp hd hO hJ heven idx slot p (finSumFinEquiv i)).val)
    rw [map_smul,restoredOuterEndpoint_back,restoredOuterEndpoint_back]
    cases i with
    | inl i => exact congrArg Subtype.val (congrFun (map_smul (restoredFamilyLinear hd hO hJ heven idx slot) a p.1) i)
    | inr i => rfl

theorem restored_upper_open_of_witness (hdp : 1≤d) (hd : d%2=0)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (idx : Fin r ≃ Label q J counts) (slot : Fin (finrank K (Forms K h d)) → Fin r)
    (p₀ : RestoredOuterSpace m d q f J counts O)
    (hp₀ : Function.Surjective (upperTargetMap (restoredOuterEndpoint hdp hd hO hJ heven idx slot p₀))) :
    letI : Module.Finite K (Space m d q J counts O) := finite_space hO
    ∃ P : MvPolynomial (Fin (finrank K (RestoredOuterSpace m d q f J counts O))) K,
      eval ((Module.finBasis K _).equivFun p₀) P≠0 ∧
      ∀ p : RestoredOuterSpace m d q f J counts O,eval ((Module.finBasis K _).equivFun p) P≠0 →
        Function.Surjective (upperTargetMap (restoredOuterEndpoint hdp hd hO hJ heven idx slot p)) := by
  letI : Module.Finite K (Space m d q J counts O) := finite_space hO
  let coord := (Module.finBasis K (RestoredOuterSpace m d q f J counts O)).equivFun
  let L := restoredOuterEndpointLinear (m := m) (f := f) hdp hd hO hJ heven idx slot
  obtain ⟨P,hP,hgood⟩ := upperTarget_principal_open (fun a => L (coord.symm a))
    (isPolynomialFamily_linear (L.comp coord.symm.toLinearMap)) (coord p₀)
    (by simpa only [LinearEquiv.symm_apply_apply,L,restoredOuterEndpointLinear,LinearMap.coe_mk,AddHom.coe_mk] using hp₀)
  refine ⟨P,hP,?_⟩
  intro p hp
  simpa only [LinearEquiv.symm_apply_apply,L,restoredOuterEndpointLinear,LinearMap.coe_mk,AddHom.coe_mk] using hgood (coord p) hp

end Froberg.PreparedParameters
