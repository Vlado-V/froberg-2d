module

public import Froberg.RestoredCertificateOpen
public import Froberg.RestoredScalarCompatibility

@[expose] public section

/-! The restored certificate gives the literal scalar/positive/outer
background used in the local comparison, including its enumeration. -/
noncomputable section
set_option maxHeartbeats 1200000
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial
variable {K : Type} [Field K] [Infinite K] {h m d q r f : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ} {O : ℕ → Submodule K (Poly K h)}

theorem restored_background_independent (hdp : 1≤d) (hd : d%2=0)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (idx : Fin r ≃ Label q J counts) (slot : Fin (finrank K (Forms K h d)) → Fin r)
    (p : RestoredOuterSpace m d q f J counts O)
    (hi : LinearIndependent K (restoredOuterEndpoint hdp hd hO hJ heven idx slot p)) :
    LinearIndependent K (backgroundEnumeratedForms
      (Fin.append (restoredBaseBiform hd hO hJ heven idx slot p.1)
        (restoredPositiveBiform hd hO hJ heven idx slot p.1))
      (fun i => linearOddForm hdp (PreparedTarget.outerVectorEquiv.symm (p.2 i))) emptyOddFamily) := by
  let e := finSumFinEquiv.symm.trans ((restoredBackgroundIndex (f := f) idx).trans (Fintype.equivFin _))
  have he (i : Fin (r+f)) :
      backgroundEnumeratedForms
        (Fin.append (restoredBaseBiform hd hO hJ heven idx slot p.1)
          (restoredPositiveBiform hd hO hJ heven idx slot p.1))
        (fun i => linearOddForm hdp (PreparedTarget.outerVectorEquiv.symm (p.2 i))) emptyOddFamily
          (e i)=restoredOuterEndpoint hdp hd hO hJ heven idx slot p i := by
    obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective i
    apply Subtype.ext
    simpa only [e,Equiv.trans_apply,Equiv.symm_apply_apply] using
      restored_background_value hdp hd hO hJ heven idx slot p j
  convert hi.comp e.symm e.symm.injective using 1
  funext i
  simpa only [Equiv.apply_symm_apply,Function.comp_apply] using he (e.symm i)

theorem restored_certificate_background (hdp : 1≤d) (hd : d%2=0)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (idx : Fin r ≃ Label q J counts) (slot : Fin (finrank K (Forms K h d)) → Fin r)
    (hslot : ∀ k,0<degree (idx (slot k)))
    (p : RestoredOuterSpace m d q f J counts O)
    (hp : RestoredCertificate hdp hd hO hJ heven idx slot p) :
    let S := Fin.append (fun i => scalarEvenBiform (h := h) (p.1.1.1 (Sum.inl i)))
      (restoredPositiveBiform hd hO hJ heven idx slot p.1)
    let F := fun i => linearOddForm hdp (PreparedTarget.outerVectorEquiv.symm (p.2 i))
    LinearIndependent K (backgroundEnumeratedForms S F emptyOddFamily) ∧
      OddSplitExact S (Fin.append F emptyOddFamily) ∧
      Function.Surjective (upperTargetMap (backgroundEnumeratedForms S F emptyOddFamily)) := by
  dsimp only
  have hi := restored_background_independent hdp hd hO hJ heven idx slot p hp.independent
  have ho := restored_split_odd_exact hd hO hJ heven idx slot p.1 _ hp.odd_exact
  have hu := restored_background_upper hdp hd hO hJ heven idx slot p hp.upper_surjective
  rw [restoredBaseBiform_eq_scalar hd hO hJ heven idx slot hslot] at hi ho hu
  exact ⟨hi,ho,hu⟩

end Froberg.PreparedParameters
