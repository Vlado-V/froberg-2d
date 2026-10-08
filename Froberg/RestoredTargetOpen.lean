import Froberg.RestoredUpperWitness
import Froberg.PreparedTargetOpen

/-! The simultaneous high-target witness gives a nonempty open on the
actual even restored coefficient space. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial
variable {K : Type} [Field K] [Infinite K] {h m d q r f : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ} {O : ℕ → Submodule K (Poly K h)}

def HasRestoredUpperOpen (hdp : 1≤d) (hd : d%2=0)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (idx : Fin r ≃ Label q J counts) (slot : Fin (finrank K (Forms K h d)) → Fin r) : Prop :=
  letI : Module.Finite K (Space m d q J counts O) := finite_space hO
  ∃ P : MvPolynomial (Fin (finrank K (RestoredOuterSpace m d q f J counts O))) K,
    (∃ p : RestoredOuterSpace m d q f J counts O,eval ((Module.finBasis K _).equivFun p) P≠0) ∧
    ∀ p : RestoredOuterSpace m d q f J counts O,eval ((Module.finBasis K _).equivFun p) P≠0 →
      Function.Surjective (upperTargetMap (restoredOuterEndpoint hdp hd hO hJ heven idx slot p))

end Froberg.PreparedParameters

namespace Froberg.PreparedTarget
open Froberg Module MvPolynomial PreparedParameters
variable {K : Type} [Field K] [CharZero K] {h m d q r f H e : ℕ}

theorem HasUpperWitness.restored_upper_open (hd : 3≤d) (he : d%2=0)
    (frame : Fin H → Forms K h 2)
    (U : Fin (finrank K (Forms K h d)) → Forms K h d)
    (idx : Fin r ≃ PreparedParameters.Label q (allEvenIndices d)
      (allEvenCount d h m (e+finrank K (Forms K h d))))
    (hw : HasUpperWitness (m := m) d f e q frame U (fun _ => 0)) :
    HasRestoredUpperOpen (m := m) (f := f) (by omega) he
      (fun j _ => targetLayerOutput_homogeneous frame j)
      (fun j hj => (mem_allEvenIndices.mp hj).2.1)
      (fun j hj => (mem_allEvenIndices.mp hj).2.2) idx
      (fun k => idx.symm (quadraticTailSlot hd q h m e _ k)) := by
  let hO := fun j (_ : j∈allEvenIndices d) => targetLayerOutput_homogeneous frame j
  letI : Module.Finite K (PreparedParameters.Space m d q (allEvenIndices d)
      (allEvenCount d h m (e+finrank K (Forms K h d))) (targetLayerOutput frame)) :=
    PreparedParameters.finite_space hO
  obtain ⟨p,hp,hlift⟩ := hw
  let pall := zeroLayers (activeEven_subset_allEven hd)
    (fun j hj => (allEvenCount_active h m e hj).symm)
    (fun j _ hj => allEvenCount_inactive h m e hj) p
  have hpall : pall.2.2=0 := hp
  have hliftall := zeroLayers_target_lifts (activeEven_subset_allEven hd)
    (fun j hj => (allEvenCount_active h m e hj).symm)
    (fun j _ hj => allEvenCount_inactive h m e hj) p U (fun _ => 0) hlift
  have hsurj : Function.Surjective (upperTargetMap
      (enumerateForms (forms (by omega) hO
        (fun j hj => (mem_allEvenIndices.mp hj).2.1) U (fun _ => 0)
        (fun _ => isHomogeneous_zero _ _ _) pall))) := by
    apply upperTargetMap_surjective_of_lifts _ (by omega)
    simpa only [enumerate_forms_productSpace] using hliftall
  have hr := restored_upper_point_surjective hd he hO idx pall hpall U hsurj
  obtain ⟨P,hP,hgood⟩ := restored_upper_open_of_witness (by omega) he hO
    (fun j hj => (mem_allEvenIndices.mp hj).2.1)
    (fun j hj => (mem_allEvenIndices.mp hj).2.2) idx
    (fun k => idx.symm (quadraticTailSlot hd q h m e _ k)) (restoredUpperPoint hd pall U) hr
  exact ⟨P,⟨restoredUpperPoint hd pall U,hP⟩,hgood⟩

end Froberg.PreparedTarget
