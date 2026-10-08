import Froberg.PreparedBiformFamilies
import Froberg.UpperTargetRange

/-! The prepared endpoint family and the Q/E/F/G family are the same
literal generators, up to their finite enumeration. -/
noncomputable section
set_option maxHeartbeats 1200000
namespace Froberg.PreparedTarget
open Froberg Module MvPolynomial
variable {K : Type} [Field K] [Infinite K] {h m d q f u : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ} {O : ℕ → Submodule K (Poly K h)}

def preparedBackgroundIndex : Label q f u J counts ≃
    BackgroundLabel (q+Fintype.card (ProductRows.LayerLabel J counts)) f u :=
  Equiv.sumCongr
    ((Equiv.sumCongr (Equiv.refl (Fin q)) (Fintype.equivFin _)).trans finSumFinEquiv)
    (Equiv.refl _)

theorem prepared_background_value (hd : 0 < d) (hdodd : d%2=1)
    (hO : ∀ j ∈ J,O j ≤ Forms K h j) (hJ : ∀ j ∈ J,j ≤ d) (heven : ∀ j ∈ J,j%2=0)
    (U : Fin u → Forms K h d) (P : OuterSpace K (Fin h) m d u)
    (p : PreparedParameters.Space m d q J counts O × OuterSpace K (Fin h) m d f)
    (i : Label q f u J counts) :
    (backgroundEnumeratedForms
      (Fin.append (preparedBaseBiform hO hJ heven p.1) (preparedPositiveBiform hO hJ heven p.1))
      (fun i => preparedOddBiform hd hdodd U P p.2 (Sum.inl i))
      (fun i => preparedOddBiform hd hdodd U P p.2 (Sum.inr i))
      (Fintype.equivFin _ (preparedBackgroundIndex i))).val=
      (zeroScalarEndpointFamily hd hO hJ U P p (Fintype.equivFin _ i)).val := by
  apply (renameEquiv K finSumFinEquiv.symm).injective
  change rename finSumFinEquiv.symm _ = rename finSumFinEquiv.symm _
  rw [zeroScalarEndpointFamily_back]
  change rename finSumFinEquiv.symm (rename finSumFinEquiv _)=_
  have hcancel (z : MvPolynomial (Fin h ⊕ Fin m) K) :
      rename finSumFinEquiv.symm (rename finSumFinEquiv z)=z :=
    (renameEquiv K finSumFinEquiv).left_inv z
  rw [hcancel]
  rw [Equiv.symm_apply_apply]
  rcases i with (i | i) | (i | i)
  · change (Fin.append (preparedBaseBiform hO hJ heven p.1)
      (preparedPositiveBiform hO hJ heven p.1) (Fin.castAdd _ i)).val = _
    simp [preparedBaseBiform,preparedEvenBiform]
  · change (Fin.append (preparedBaseBiform hO hJ heven p.1)
      (preparedPositiveBiform hO hJ heven p.1)
      (Fin.natAdd q ((Fintype.equivFin (ProductRows.LayerLabel J counts)) i))).val = _
    simp [preparedPositiveBiform,preparedEvenBiform]
  · rfl
  · rfl

theorem prepared_background_upper (hd : 0 < d) (hdodd : d%2=1)
    (hO : ∀ j ∈ J,O j ≤ Forms K h j) (hJ : ∀ j ∈ J,j ≤ d) (heven : ∀ j ∈ J,j%2=0)
    (U : Fin u → Forms K h d) (P : OuterSpace K (Fin h) m d u)
    (p : PreparedParameters.Space m d q J counts O × OuterSpace K (Fin h) m d f)
    (hu : Function.Surjective (upperTargetMap (zeroScalarEndpointFamily hd hO hJ U P p))) :
    Function.Surjective (upperTargetMap (backgroundEnumeratedForms
      (Fin.append (preparedBaseBiform hO hJ heven p.1) (preparedPositiveBiform hO hJ heven p.1))
      (fun i => preparedOddBiform hd hdodd U P p.2 (Sum.inl i))
      (fun i => preparedOddBiform hd hdodd U P p.2 (Sum.inr i)))) := by
  apply upperTargetMap_surjective_of_range _ _ _ hu
  ext x
  constructor
  · rintro ⟨k,rfl⟩
    obtain ⟨i,rfl⟩ := (Fintype.equivFin (Label q f u J counts)).surjective k
    exact ⟨Fintype.equivFin _ (preparedBackgroundIndex i),
      prepared_background_value hd hdodd hO hJ heven U P p i⟩
  · rintro ⟨k,rfl⟩
    obtain ⟨i,rfl⟩ := (Fintype.equivFin _).surjective k
    obtain ⟨j,rfl⟩ := preparedBackgroundIndex.surjective i
    exact ⟨Fintype.equivFin _ j,(prepared_background_value hd hdodd hO hJ heven U P p j).symm⟩

end Froberg.PreparedTarget
