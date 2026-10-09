module

public import Froberg.ComponentQuotientIndependence
public import Froberg.PreparedFamilyIndependence
public import Froberg.HomogeneousRename

@[expose] public section

/-! Independence modulo weight-zero polynomials implies the exact
independence modulo the scalar form space used by replacement. -/
noncomputable section
namespace Froberg
open Module MvPolynomial
variable {K : Type} [Field K] [Infinite K] {h m d : ℕ} {I : Type*}

theorem scalar_quotient_independence_transport (g : I → Forms K (h+m) d)
    (hg : LinearIndependent K (fun i =>
      (weightedHomogeneousSubmodule K (blockWeight h m) 0).mkQ
        (rename finSumFinEquiv.symm (g i).val))) :
    LinearIndependent K (fun i =>
      (renameForm (K := K) (d := d) (Fin.natAdd h : Fin m → Fin (h+m))).range.mkQ (g i)) := by
  let P : Forms K (h+m) d →ₗ[K]
      MvPolynomial (Fin h ⊕ Fin m) K ⧸ weightedHomogeneousSubmodule K (blockWeight h m) 0 :=
    (weightedHomogeneousSubmodule K (blockWeight h m) 0).mkQ.comp
      ((rename finSumFinEquiv.symm).toLinearMap.comp (Forms K (h+m) d).subtype)
  apply quotient_independent_of_projection _ _ P _ hg
  rintro z ⟨a,rfl⟩
  change (weightedHomogeneousSubmodule K (blockWeight h m) 0).mkQ
    (rename finSumFinEquiv.symm (rename (Fin.natAdd h) a.val))=0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  rw [rename_rename]
  have he : (finSumFinEquiv.symm : Fin (h+m) → Fin h ⊕ Fin m) ∘ Fin.natAdd h=Sum.inr := by
    funext i
    exact finSumFinEquiv_symm_apply_natAdd i
  rw [he]
  exact rename_weightedHomogeneous
    (⟨Sum.inr,Sum.inr_injective⟩ : Fin m ↪ Fin h ⊕ Fin m)
    (fun _ => 0) (blockWeight h m) (fun _ => rfl) (weightedHomogeneous_zero_weight a.val)

end Froberg
