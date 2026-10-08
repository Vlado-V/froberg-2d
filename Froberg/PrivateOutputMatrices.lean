import Froberg.PrivateOutputTransport

/-! Actual multiplication by a nonzero linear output form gives the
coordinate maps used in private-row separation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
namespace Froberg
open Module MvPolynomial
variable {K : Type} [Field K] [Infinite K] {σ : Type*} {R H L : ℕ}

lemma outputCombination_basis (O : Submodule K (MvPolynomial σ K))
    (b : Basis (Fin H) K O) (x : O) :
    outputCombination (fun i => (b i).val) (b.equivFun x)=x.val := by
  have hh := congrArg Subtype.val (b.equivFun_symm_apply (b.equivFun x))
  simpa only [LinearEquiv.symm_apply_apply,Submodule.coe_sum,Submodule.coe_smul,
    outputCombination,LinearMap.coe_mk,AddHom.coe_mk] using hh.symm

/-- A literal output multiplication matrix in any two homogeneous bases. -/
def privateOutputMatrix
    (hi : Basis (Fin L) K (homogeneousSubmodule σ K R))
    (ho : Basis (Fin H) K (homogeneousSubmodule σ K (R+1)))
    (w : homogeneousSubmodule σ K 1) : (Fin L → K) →ₗ[K] (Fin H → K) :=
  let F : homogeneousSubmodule σ K R →ₗ[K] homogeneousSubmodule σ K (R+1) :=
    (((LinearMap.mul K (MvPolynomial σ K)) w.val).comp
      (homogeneousSubmodule σ K R).subtype).codRestrict
      (homogeneousSubmodule σ K (R+1)) (by
        intro x
        change (w.val*x.val).IsHomogeneous (R+1)
        simpa only [Nat.add_comm 1 R] using w.property.mul x.property)
  ho.equivFun.toLinearMap.comp (F.comp hi.equivFun.symm.toLinearMap)

/-- Each column is exactly the product of its lower basis element with w. -/
theorem privateOutputMatrix_column
    (hi : Basis (Fin L) K (homogeneousSubmodule σ K R))
    (ho : Basis (Fin H) K (homogeneousSubmodule σ K (R+1)))
    (w : homogeneousSubmodule σ K 1) (j : Fin L) :
    outputCombination (fun k => (ho k).val) (privateOutputMatrix hi ho w (Pi.single j 1))=
      w.val*(hi j).val := by
  classical
  have hsingle : hi.equivFun.symm (Pi.single j 1)=hi j := by
    rw [hi.equivFun_symm_apply]
    simp [Pi.single_apply]
  change outputCombination (fun k => (ho k).val) (ho.equivFun _) = _
  rw [outputCombination_basis]
  change w.val*(hi.equivFun.symm (Pi.single j 1)).val=w.val*(hi j).val
  rw [hsingle]

theorem privateOutputMatrix_injective
    (hi : Basis (Fin L) K (homogeneousSubmodule σ K R))
    (ho : Basis (Fin H) K (homogeneousSubmodule σ K (R+1)))
    (w : homogeneousSubmodule σ K 1) (hw : w≠0) :
    Function.Injective (privateOutputMatrix hi ho w) := by
  have hli : LinearIndependent K (fun j => (hi j).val) :=
    hi.linearIndependent.map' (homogeneousSubmodule σ K R).subtype
      (LinearMap.ker_eq_bot.mpr (homogeneousSubmodule σ K R).subtype_injective)
  exact private_output_map_injective (fun k => (ho k).val) (fun j => (hi j).val)
    hli w.val (fun h => hw (Subtype.ext h)) (privateOutputMatrix hi ho w)
      (privateOutputMatrix_column hi ho w)

end Froberg
