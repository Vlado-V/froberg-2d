import Froberg.PreparedBackgroundUpper

/-! The canonical Q/E/F/G enumeration inherits independence from the
literal prepared endpoint family. -/
noncomputable section
set_option maxHeartbeats 500000
namespace Froberg.PreparedTarget
open Froberg Module MvPolynomial PreparedParameters
variable {K : Type} [Field K] [Infinite K]
variable {h m d q f u : ℕ} {J : Finset ℕ} {counts : ℕ → ℕ}
variable {O : ℕ → Submodule K (Poly K h)}

theorem prepared_background_independent (hd : 0<d) (ho : d%2=1)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (U : Fin u → Forms K h d) (P : OuterSpace K (Fin h) m d u)
    (p : PreparedParameters.Space m d q J counts O × OuterSpace K (Fin h) m d f)
    (hi : LinearIndependent K (zeroScalarEndpointFamily hd hO hJ U P p)) :
    LinearIndependent K (backgroundEnumeratedForms
      (Fin.append (preparedBaseBiform hO hJ heven p.1) (preparedPositiveBiform hO hJ heven p.1))
      (fun i => preparedOddBiform hd ho U P p.2 (Sum.inl i))
      (fun i => preparedOddBiform hd ho U P p.2 (Sum.inr i))) := by
  let e : Fin (Fintype.card (BackgroundLabel (q+Fintype.card (ProductRows.LayerLabel J counts)) f u)) ≃
      Fin (Fintype.card (PreparedTarget.Label q f u J counts)) :=
    (Fintype.equivFin _).symm.trans (preparedBackgroundIndex.symm.trans (Fintype.equivFin _))
  convert hi.comp e e.injective using 1
  funext k
  obtain ⟨j,rfl⟩ := (Fintype.equivFin _).surjective k
  obtain ⟨i,rfl⟩ := preparedBackgroundIndex.surjective j
  apply Subtype.ext
  simpa only [Function.comp_apply,e,Equiv.trans_apply,Equiv.symm_apply_apply] using
    prepared_background_value hd ho hO hJ heven U P p i

end Froberg.PreparedTarget
