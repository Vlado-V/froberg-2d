import Froberg.RestoredScalarFiber
import Froberg.PreparedScalarFiberCompatibility
import Froberg.RestoredEndpointPolynomial
import Froberg.EvenBackgroundEquivalence
import Froberg.UpperTargetRange
import Froberg.OddExactEnumeration

/-! The restored scalar fiber is the literal Q/E/F family: the base Q
and outer F are fixed, while every positive even column is E_i+a_i. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial
variable {K : Type} [Field K] [Infinite K] {h m d q r f : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ} {O : ℕ → Submodule K (Poly K h)}

def restoredBaseBiform (hd : d%2=0)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (idx : Fin r ≃ Label q J counts) (slot : Fin (finrank K (Forms K h d)) → Fin r)
    (p : RestoredSpace m d q J counts O) : Fin q → biformParitySpace K h m d 0 :=
  fun i => restoredBiformFamily hd hO hJ heven idx slot p (idx.symm (Sum.inl i))

def restoredPositiveBiform (hd : d%2=0)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (idx : Fin r ≃ Label q J counts) (slot : Fin (finrank K (Forms K h d)) → Fin r)
    (p : RestoredSpace m d q J counts O) :
    Fin (Fintype.card (ProductRows.LayerLabel J counts)) → biformParitySpace K h m d 0 :=
  fun i => restoredBiformFamily hd hO hJ heven idx slot p
    (idx.symm (Sum.inr ((Fintype.equivFin _).symm i)))

theorem restoredBaseBiform_eq_scalar (hd : d%2=0)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (idx : Fin r ≃ Label q J counts) (slot : Fin (finrank K (Forms K h d)) → Fin r)
    (hslot : ∀ k,0<degree (idx (slot k))) (p : RestoredSpace m d q J counts O) :
    restoredBaseBiform hd hO hJ heven idx slot p=
      fun i => scalarEvenBiform (h := h) (p.1.1 (Sum.inl i)) := by
  funext i
  apply Subtype.ext
  change generator p.1 (idx (idx.symm (Sum.inl i)))+
    (PolynomialRestoration.pureShift (pureEvenEmbed hd) slot p.2 (idx.symm (Sum.inl i))).val=_
  have haway : ∀ k,slot k≠idx.symm (Sum.inl i) := by
    intro k hk
    have hh := hslot k
    rw [hk,Equiv.apply_symm_apply] at hh
    exact (Nat.not_lt_zero _) hh
  rw [pureShift_eq_zero_away _ _ _ _ haway,Submodule.coe_zero,add_zero,Equiv.apply_symm_apply]
  simp [generator,scalar,high]

theorem restoredScalarFiber_positive (hd : d%2=0)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (idx : Fin r ≃ Label q J counts) (slot : Fin (finrank K (Forms K h d)) → Fin r)
    (a : PositiveScalars (K := K) m d J counts) (rest : RestoredScalarRest m d q f J counts O) :
    restoredPositiveBiform hd hO hJ heven idx slot (restoredScalarFiberCoordinates.symm (a,rest)).1=
      oddEvenAffineFamily
        (restoredPositiveBiform hd hO hJ heven idx slot (restoredScalarFiberCoordinates.symm (0,rest)).1) a := by
  funext i
  apply Subtype.ext
  change generator (scalarFiberCoordinates.symm (a,rest.1))
      (idx (idx.symm (Sum.inr ((Fintype.equivFin _).symm i)))) +
      (PolynomialRestoration.pureShift (pureEvenEmbed hd) slot rest.2.1
        (idx.symm (Sum.inr ((Fintype.equivFin _).symm i)))).val =
    (generator (scalarFiberCoordinates.symm (0,rest.1))
      (idx (idx.symm (Sum.inr ((Fintype.equivFin _).symm i)))) +
      (PolynomialRestoration.pureShift (pureEvenEmbed hd) slot rest.2.1
        (idx.symm (Sum.inr ((Fintype.equivFin _).symm i)))).val)+
      (scalarEvenBiform (h := h) (a i)).val
  simp only [Equiv.apply_symm_apply,generator,scalarFiberCoordinates,LinearEquiv.coe_symm_mk,
    scalar,high,Sum.elim_inr,Pi.zero_apply,Equiv.apply_symm_apply,Submodule.coe_zero,map_zero,add_zero,scalarEvenBiform_val]
  abel


def restoredEvenIndex (idx : Fin r ≃ Label q J counts) :
    Fin r ≃ Fin (q+Fintype.card (ProductRows.LayerLabel J counts)) :=
  idx.trans ((Equiv.sumCongr (Equiv.refl (Fin q)) (Fintype.equivFin _)).trans finSumFinEquiv)

theorem restored_split_value (hd : d%2=0)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (idx : Fin r ≃ Label q J counts) (slot : Fin (finrank K (Forms K h d)) → Fin r)
    (p : RestoredSpace m d q J counts O) (i : Fin r) :
    Fin.append (restoredBaseBiform hd hO hJ heven idx slot p)
      (restoredPositiveBiform hd hO hJ heven idx slot p) (restoredEvenIndex idx i)=
        restoredBiformFamily hd hO hJ heven idx slot p i := by
  obtain ⟨j,rfl⟩ := idx.symm.surjective i
  cases j <;> simp [restoredEvenIndex,restoredBaseBiform,restoredPositiveBiform]

theorem restored_split_odd_exact (hd : d%2=0)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (idx : Fin r ≃ Label q J counts) (slot : Fin (finrank K (Forms K h d)) → Fin r)
    (p : RestoredSpace m d q J counts O) (F : Fin f → biformParitySpace K h m d 1)
    (H : OddSplitExact (restoredBiformFamily hd hO hJ heven idx slot p) F) :
    OddSplitExact (Fin.append (restoredBaseBiform hd hO hJ heven idx slot p)
      (restoredPositiveBiform hd hO hJ heven idx slot p)) (Fin.append F emptyOddFamily) := by
  let S := Fin.append (restoredBaseBiform hd hO hJ heven idx slot p)
    (restoredPositiveBiform hd hO hJ heven idx slot p)
  let T := Fin.append F (emptyOddFamily (K := K) (h := h) (m := m) (d := d))
  let e := restoredEvenIndex idx
  let t : Fin (f+0) ≃ Fin f := finCongr (Nat.add_zero f)
  have hS (i) : (S (e i)).val=(restoredBiformFamily hd hO hJ heven idx slot p i).val :=
    congrArg Subtype.val (restored_split_value hd hO hJ heven idx slot p i)
  have hT (i) : (T (t.symm i)).val=(F i).val := by
    simp [T,t,emptyOddFamily]
  intro c v hr
  apply constant_pair_kernel_reindex e.symm t (fun i => (S i).val) (fun i => (T i).val)
    (biformParitySpace K h m d 1) (biformParitySpace K h m d 0) ?_
    (fun i => (c i).val) (fun i => (v i).val) (fun i => (c i).property)
    (fun i => (v i).property) hr
  intro x y hx hy hrel
  obtain ⟨B,hB,hB'⟩ := H (fun i => ⟨x i,hx i⟩) (fun i => ⟨y i,hy i⟩)
    (by simpa only [Equiv.symm_symm,hS,hT] using hrel)
  exact ⟨B,by simpa only [Equiv.symm_symm,hT] using hB,
    by simpa only [Equiv.symm_symm,hS] using hB'⟩

theorem restored_scalar_fiber_relative_injective (hdp : 1≤d) (hd : d%2=0)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (idx : Fin r ≃ Label q J counts) (slot : Fin (finrank K (Forms K h d)) → Fin r)
    (hslot : ∀ k,0<degree (idx (slot k)))
    (a : PositiveScalars (K := K) m d J counts) (rest : RestoredScalarRest m d q f J counts O)
    (H : OddSplitExact
      (restoredBiformFamily hd hO hJ heven idx slot (restoredScalarFiberCoordinates.symm (a,rest)).1)
      (fun i => linearOddForm hdp (PreparedTarget.outerVectorEquiv.symm (rest.2.2 i)))) :
    Function.Injective (oddEvenRelativeMap (fun i => scalarEvenBiform (h := h) (rest.1.1 i))
      (fun i => linearOddForm hdp (PreparedTarget.outerVectorEquiv.symm (rest.2.2 i))) emptyOddFamily
      (oddEvenAffineFamily
        (restoredPositiveBiform hd hO hJ heven idx slot (restoredScalarFiberCoordinates.symm (0,rest)).1) a)) := by
  have hex := restored_split_odd_exact hd hO hJ heven idx slot
    (restoredScalarFiberCoordinates.symm (a,rest)).1 _ H
  have hi := odd_split_relative_injective _ _ _ _ hex
  rw [restoredBaseBiform_eq_scalar hd hO hJ heven idx slot hslot,restoredScalarFiber_positive] at hi
  exact hi


def restoredBackgroundIndex (idx : Fin r ≃ Label q J counts) :
    (Fin r ⊕ Fin f) ≃ BackgroundLabel (q+Fintype.card (ProductRows.LayerLabel J counts)) f 0 :=
  Equiv.sumCongr (restoredEvenIndex idx) (Equiv.sumEmpty (Fin f) (Fin 0)).symm

theorem restored_background_value (hdp : 1≤d) (hd : d%2=0)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (idx : Fin r ≃ Label q J counts) (slot : Fin (finrank K (Forms K h d)) → Fin r)
    (p : RestoredOuterSpace m d q f J counts O) (i : Fin r ⊕ Fin f) :
    (backgroundEnumeratedForms
      (Fin.append (restoredBaseBiform hd hO hJ heven idx slot p.1)
        (restoredPositiveBiform hd hO hJ heven idx slot p.1))
      (fun i => linearOddForm hdp (PreparedTarget.outerVectorEquiv.symm (p.2 i))) emptyOddFamily
      (Fintype.equivFin _ (restoredBackgroundIndex idx i))).val=
      (restoredOuterEndpoint hdp hd hO hJ heven idx slot p (finSumFinEquiv i)).val := by
  apply (renameEquiv K finSumFinEquiv.symm).injective
  simp only [renameEquiv_apply]
  rw [restoredOuterEndpoint_back,backgroundEnumeratedForms_back]
  cases i with
  | inl i =>
    change (Fin.append (restoredBaseBiform hd hO hJ heven idx slot p.1)
      (restoredPositiveBiform hd hO hJ heven idx slot p.1) (restoredEvenIndex idx i)).val=_
    exact congrArg Subtype.val (restored_split_value hd hO hJ heven idx slot p.1 i)
  | inr i =>
    change sumBiformMap (linearOutputTensorEquiv (PreparedTarget.outerVectorEquiv.symm (p.2 i)))=(p.2 i).val
    rw [←PreparedTarget.outerVectorEquiv_val,LinearEquiv.apply_symm_apply]

theorem restored_background_upper (hdp : 1≤d) (hd : d%2=0)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (idx : Fin r ≃ Label q J counts) (slot : Fin (finrank K (Forms K h d)) → Fin r)
    (p : RestoredOuterSpace m d q f J counts O)
    (hu : Function.Surjective (upperTargetMap (restoredOuterEndpoint hdp hd hO hJ heven idx slot p))) :
    Function.Surjective (upperTargetMap (backgroundEnumeratedForms
      (Fin.append (restoredBaseBiform hd hO hJ heven idx slot p.1)
        (restoredPositiveBiform hd hO hJ heven idx slot p.1))
      (fun i => linearOddForm hdp (PreparedTarget.outerVectorEquiv.symm (p.2 i))) emptyOddFamily)) := by
  apply upperTargetMap_surjective_of_range _ _ _ hu
  ext x
  constructor
  · rintro ⟨k,rfl⟩
    obtain ⟨i,rfl⟩ := finSumFinEquiv.surjective k
    exact ⟨Fintype.equivFin _ (restoredBackgroundIndex idx i),
      restored_background_value hdp hd hO hJ heven idx slot p i⟩
  · rintro ⟨k,rfl⟩
    obtain ⟨i,rfl⟩ := (Fintype.equivFin _).surjective k
    obtain ⟨j,rfl⟩ := (restoredBackgroundIndex idx).surjective i
    exact ⟨finSumFinEquiv j,(restored_background_value hdp hd hO hJ heven idx slot p j).symm⟩

theorem restored_scalar_fiber_upper (hdp : 1≤d) (hd : d%2=0)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (idx : Fin r ≃ Label q J counts) (slot : Fin (finrank K (Forms K h d)) → Fin r)
    (hslot : ∀ k,0<degree (idx (slot k)))
    (a : PositiveScalars (K := K) m d J counts) (rest : RestoredScalarRest m d q f J counts O)
    (hu : Function.Surjective (upperTargetMap (restoredOuterEndpoint hdp hd hO hJ heven idx slot
      (restoredScalarFiberCoordinates.symm (a,rest))))) :
    Function.Surjective (upperTargetMap (backgroundEnumeratedForms
      (Fin.append (fun i => scalarEvenBiform (h := h) (rest.1.1 i))
        (oddEvenAffineFamily
          (restoredPositiveBiform hd hO hJ heven idx slot (restoredScalarFiberCoordinates.symm (0,rest)).1) a))
      (fun i => linearOddForm hdp (PreparedTarget.outerVectorEquiv.symm (rest.2.2 i))) emptyOddFamily)) := by
  have hi := restored_background_upper hdp hd hO hJ heven idx slot _ hu
  rw [restoredBaseBiform_eq_scalar hd hO hJ heven idx slot hslot,restoredScalarFiber_positive] at hi
  exact hi

end Froberg.PreparedParameters
