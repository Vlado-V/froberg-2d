import Froberg.RestoredTargetOpen
import Froberg.PreparedCountCompatibility
import Froberg.UpperTargetSpan

/-! Enlarging the even row counts preserves an actual upper-target witness.
The pure slots follow the retained-label injection, so an appended extra
column does not move any existing pure generator. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial
variable {K : Type} [Field K] [Infinite K] {h m d q f r r' : ℕ}
variable {J : Finset ℕ} {c c' : ℕ → ℕ} {O : ℕ → Submodule K (Poly K h)}

def restoredOuterCountIndexMap (hc : ∀ j∈J,c j≤c' j)
    (idx : Fin r ≃ Label q J c) (idx' : Fin r' ≃ Label q J c') :
    Fin (r+f) → Fin (r'+f) := fun i =>
  finSumFinEquiv (Sum.map (countIndexMap hc idx idx') id (finSumFinEquiv.symm i))

theorem restoredOuterEndpoint_restrictCounts
    (hdp : 1≤d) (hd : d%2=0)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (hc : ∀ j∈J,c j≤c' j)
    (idx : Fin r ≃ Label q J c) (idx' : Fin r' ≃ Label q J c')
    (slot : Fin (finrank K (Forms K h d)) → Fin r)
    (p : RestoredOuterSpace m d q f J c' O) (i : Fin (r+f)) :
    restoredOuterEndpoint hdp hd hO hJ heven idx slot (restoredRestrictCounts hc p) i=
      restoredOuterEndpoint hdp hd hO hJ heven idx' (countIndexMap hc idx idx' ∘ slot) p
        (restoredOuterCountIndexMap hc idx idx' i) := by
  obtain ⟨i,rfl⟩ := finSumFinEquiv.surjective i
  apply Subtype.ext
  apply (renameEquiv K finSumFinEquiv.symm).injective
  change rename finSumFinEquiv.symm
      (restoredOuterEndpoint hdp hd hO hJ heven idx slot (restoredRestrictCounts hc p)
        (finSumFinEquiv i)).val=
    rename finSumFinEquiv.symm
      (restoredOuterEndpoint hdp hd hO hJ heven idx' (countIndexMap hc idx idx' ∘ slot) p
        (restoredOuterCountIndexMap hc idx idx' (finSumFinEquiv i))).val
  simp only [restoredOuterCountIndexMap,Equiv.symm_apply_apply]
  rw [restoredOuterEndpoint_back,restoredOuterEndpoint_back]
  cases i with
  | inl i =>
    exact congrArg Subtype.val
      (restoredFamilyLinear_restrictCounts hd hO hJ heven hc idx idx' slot p.1 i)
  | inr i => rfl

theorem HasRestoredUpperOpen.extend_counts
    (hdp : 1≤d) (hd : d%2=0)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (hc : ∀ j∈J,c j≤c' j)
    (idx : Fin r ≃ Label q J c) (idx' : Fin r' ≃ Label q J c')
    (slot : Fin (finrank K (Forms K h d)) → Fin r)
    (hu : HasRestoredUpperOpen (m := m) (f := f) hdp hd hO hJ heven idx slot) :
    HasRestoredUpperOpen (m := m) (f := f) hdp hd hO hJ heven idx'
      (countIndexMap hc idx idx' ∘ slot) := by
  classical
  letI : Module.Finite K (Space m d q J c O) := finite_space hO
  letI : Module.Finite K (Space m d q J c' O) := finite_space hO
  obtain ⟨D,⟨p,hp⟩,hgood⟩ := hu
  obtain ⟨p',hp'⟩ := restoredRestrictCounts_surjective hc p
  have hsurj : Function.Surjective (upperTargetMap
      (restoredOuterEndpoint hdp hd hO hJ heven idx'
        (countIndexMap hc idx idx' ∘ slot) p')) := by
    apply upperTargetMap_surjective_of_span_le
      (restoredOuterEndpoint hdp hd hO hJ heven idx slot p) _ _ (hgood p hp)
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    dsimp only
    rw [←hp',restoredOuterEndpoint_restrictCounts hdp hd hO hJ heven hc idx idx' slot p' i]
    exact Submodule.subset_span ⟨restoredOuterCountIndexMap hc idx idx' i,rfl⟩
  obtain ⟨P,hP,hPgood⟩ := restored_upper_open_of_witness hdp hd hO hJ heven idx'
    (countIndexMap hc idx idx' ∘ slot) p' hsurj
  exact ⟨P,⟨p',hP⟩,hPgood⟩

end Froberg.PreparedParameters
