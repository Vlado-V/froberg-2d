import Froberg.PreparedBiformFamilies
import Froberg.OddEvenAffineRelations

/-! The prepared biform families are exactly the scalar, linear, mixed
pure, and affine higher families used in the C.4 quotient construction. -/
noncomputable section
namespace Froberg.PreparedTarget
open Froberg Module MvPolynomial
variable {K : Type} [Field K] [Infinite K] {h m d q f u : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ} {O : ℕ → Submodule K (Poly K h)}

theorem preparedBaseBiform_eq_scalar (hO : ∀ j∈J,O j≤Forms K h j)
    (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (p : PreparedParameters.Space m d q J counts O) (i : Fin q) :
    preparedBaseBiform hO hJ heven p i=scalarEvenBiform (p.1 (Sum.inl i)) := by
  apply Subtype.ext
  simp [preparedBaseBiform,preparedEvenBiform,PreparedParameters.generator,
    PreparedParameters.scalar,PreparedParameters.high]

theorem preparedOddBiform_outer (hd : 0<d) (hdodd : d%2=1)
    (U : Fin u → Forms K h d) (P : OuterSpace K (Fin h) m d u)
    (F : OuterSpace K (Fin h) m d f) (i : Fin f) :
    preparedOddBiform hd hdodd U P F (Sum.inl i)=
      linearOddForm (by omega) (outerVectorEquiv.symm (F i)) := by
  apply Subtype.ext
  change (F i).val+0=sumBiformMap (linearOutputTensorEquiv (outerVectorEquiv.symm (F i)))
  rw [add_zero,←outerVectorEquiv_val,LinearEquiv.apply_symm_apply]

theorem preparedOddBiform_private (hd : 0<d) (hdodd : d%2=1)
    (U : Fin u → Forms K h d) (P : OuterSpace K (Fin h) m d u)
    (F : OuterSpace K (Fin h) m d f) (i : Fin u) :
    preparedOddBiform hd hdodd U P F (Sum.inr i)=
      mixedPureOddGenerator (Nat.odd_iff.mpr hdodd) (U i) (sumBiformEquiv.symm (P i)) := by
  apply Subtype.ext
  rw [mixedPureOddGenerator_val]
  change (P i).val+rename Sum.inl (U i).val=
    rename Sum.inl (U i).val+(sumBiformEquiv (sumBiformEquiv.symm (P i))).val
  rw [LinearEquiv.apply_symm_apply,add_comm]

def preparedHighBiform (hO : ∀ j∈J,O j≤Forms K h j)
    (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (p : PreparedParameters.Space m d q J counts O)
    (i : Fin (Fintype.card (ProductRows.LayerLabel J counts))) : biformParitySpace K h m d 0 :=
  preparedPositiveBiform hO hJ heven p i-
    scalarEvenBiform (p.1 (Sum.inr ((Fintype.equivFin _).symm i)))

theorem preparedHighBiform_val (hO : ∀ j∈J,O j≤Forms K h j)
    (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (p : PreparedParameters.Space m d q J counts O)
    (i : Fin (Fintype.card (ProductRows.LayerLabel J counts))) :
    (preparedHighBiform hO hJ heven p i).val=
      PreparedParameters.high p (Sum.inr ((Fintype.equivFin _).symm i)) := by
  simp only [preparedHighBiform,Submodule.coe_sub,preparedPositiveBiform,preparedEvenBiform,
    scalarEvenBiform_val,PreparedParameters.generator,PreparedParameters.scalar,add_sub_cancel_left]

theorem preparedPositiveBiform_eq_affine (hO : ∀ j∈J,O j≤Forms K h j)
    (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (p : PreparedParameters.Space m d q J counts O) :
    preparedPositiveBiform hO hJ heven p=
      oddEvenAffineFamily (preparedHighBiform hO hJ heven p)
        (fun i => p.1 (Sum.inr ((Fintype.equivFin _).symm i))) := by
  funext i
  exact (sub_add_cancel _ _).symm

end Froberg.PreparedTarget
