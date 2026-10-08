import Froberg.PreparedPositiveQuotient
import Froberg.PreparedBiformFamilies
import Froberg.BackgroundFlagSpan
import Froberg.RestoredScalarCompatibility

/-! Scalar-quotient independence for the literal even/private indexing
used in the final flag comparison. -/
noncomputable section
set_option maxHeartbeats 300000
namespace Froberg.PreparedTarget
open Froberg Module MvPolynomial PreparedParameters
variable {K : Type} [Field K] [Infinite K] {h m d q f u r : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ} {O : ℕ → Submodule K (Poly K h)}

theorem prepared_positive_background_scalar_independent (hd : 1<d) (hdodd : d%2=1)
    (hO : ∀ j∈J,O j≤Forms K h j) (hmin : ∀ j∈J,2≤j)
    (hJ : ∀ j∈J,j≤d) (hJlt : ∀ j∈J,0<counts j → j<d) (heven : ∀ j∈J,j%2=0)
    (U : Fin u → Forms K h d) (P : OuterSpace K (Fin h) m d u)
    (p : PreparedParameters.Space m d q J counts O × OuterSpace K (Fin h) m d f)
    (hp : ∀ j,LinearIndependent K (p.1.2 j)) (hP : LinearIndependent K P) :
    LinearIndependent K (fun i =>
      (renameForm (K := K) (d := d) (Fin.natAdd h : Fin m → Fin (h+m))).range.mkQ
        (backgroundPositiveForms (preparedPositiveBiform hO hJ heven p.1)
          (fun j => preparedOddBiform (by omega) hdodd U P p.2 (Sum.inr j)) i)) := by
  let e : Fin (Fintype.card (ProductRows.LayerLabel J counts)) ⊕ Fin u ≃
      ProductRows.LayerLabel J counts ⊕ Fin u :=
    Equiv.sumCongr (Fintype.equivFin _).symm (Equiv.refl _)
  have hi := (prepared_positive_endpoint_scalar_independent hd hO hmin hJ hJlt U P p hp hP).comp
    e e.injective
  convert hi using 1
  funext i
  congr 1
  apply Subtype.ext
  apply (renameEquiv K finSumFinEquiv.symm).injective
  have hcancel (z : MvPolynomial (Fin h ⊕ Fin m) K) :
      rename finSumFinEquiv.symm (rename finSumFinEquiv z)=z :=
    (renameEquiv K finSumFinEquiv).left_inv z
  cases i with
  | inl i =>
    change rename finSumFinEquiv.symm (rename finSumFinEquiv
      (PreparedParameters.generator p.1 (Sum.inr ((Fintype.equivFin _).symm i))))=_
    rw [hcancel]
    exact (zeroScalarEndpointFamily_back (by omega) hO hJ U P p
      (Sum.inl (Sum.inr ((Fintype.equivFin _).symm i)))).symm
  | inr i =>
    change rename finSumFinEquiv.symm (rename finSumFinEquiv (oddGenerator U P p.2 (Sum.inr i)))=_
    rw [hcancel]
    exact (zeroScalarEndpointFamily_back (by omega) hO hJ U P p (Sum.inr (Sum.inr i))).symm

theorem restored_positive_biform_scalar_independent (hd : d%2=0)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (hpos : ∀ j∈J,0<j) (hJlt : ∀ j∈J,0<counts j → j<d)
    (idx : Fin r ≃ PreparedParameters.Label q J counts) (slot : Fin (finrank K (Forms K h d)) → Fin r)
    (p : RestoredSpace m d q J counts O) (hp : ∀ j,LinearIndependent K (p.1.2 j)) :
    LinearIndependent K (fun i =>
      (renameForm (K := K) (d := d) (Fin.natAdd h : Fin m → Fin (h+m))).range.mkQ
        (evenPolynomialToForms (restoredPositiveBiform hd hO hJ heven idx slot p i))) := by
  have hi := (restored_positive_endpoint_scalar_independent hd hO hJ heven hpos hJlt idx slot p hp).comp
    (Fintype.equivFin _).symm (Fintype.equivFin _).symm.injective
  convert hi using 1
  funext i
  congr 1

end Froberg.PreparedTarget
