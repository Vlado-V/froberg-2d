import Froberg.PrivateBiformFamily
import Froberg.PrivateBoundaryTransport
import Froberg.PrivateOutputMatrices

/-! The distinct private powers give independent literal biforms even when
their nonzero linear output factors are not independent. -/
noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial PrivateColumns
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} [Fintype σ] {a z d b : ℕ}

theorem privatePowerBiform_val_linearIndependent (hs : 0<d-1)
    (l : Fin b → homogeneousSubmodule σ K 1) (hl : ∀ i,l i≠0)
    (ι : Fin b ↪ Fin z) :
    LinearIndependent K (fun i => (privatePowerBiform (a := a) (d := d) l ι i).val) := by
  letI : Module.Finite K (homogeneousSubmodule σ K 1) :=
    Module.Finite.of_basis (finiteVariableFormsBasis σ 1)
  let bo := Module.finBasis K (homogeneousSubmodule σ K 1)
  let w := fun i => bo.equivFun (l i)
  have hw (i : Fin b) : w i≠0 := by
    intro hz
    apply hl i
    exact bo.equivFun.injective (hz.trans bo.equivFun.map_zero.symm)
  choose dual hdual using fun i => Module.Projective.exists_dual_eq_one K (hw i)
  let o := fun j => (bo j).val
  have ho : LinearIndependent K o :=
    bo.linearIndependent.map' (homogeneousSubmodule σ K 1).subtype (Submodule.ker_subtype _)
  have hi := privateGenerator_linearIndependent (a := a) hs ι w dual hdual
  have hpol := hi.map' (polynomialFormVector o (d-1))
    (LinearMap.ker_eq_bot.mpr (polynomialFormVector_injective o ho))
  change LinearIndependent K (fun i => polynomialFormVector o (d-1)
    (privateGenerator (a := a) (s := d-1) ι w i)) at hpol
  have heq : (fun i => polynomialFormVector o (d-1)
      (privateGenerator (a := a) (s := d-1) ι w i))=
      (fun i => (privatePowerBiform (a := a) (d := d) l ι i).val) := by
    funext i
    rw [privateGenerator_polynomial]
    change rename Sum.inl (outputCombination (fun j => (bo j).val) (bo.equivFun (l i)))*
      rename Sum.inr (monomial (privateExponent a (d-1) ι i) (1:K))=_
    rw [outputCombination_basis]
    rfl
  rwa [heq] at hpol

theorem privatePowerBiform_linearIndependent (hs : 0<d-1)
    (l : Fin b → homogeneousSubmodule σ K 1) (hl : ∀ i,l i≠0)
    (ι : Fin b ↪ Fin z) :
    LinearIndependent K (privatePowerBiform (a := a) (d := d) l ι) := by
  apply LinearIndependent.of_comp (FullBiform K σ (a+z) 1 (d-1)).subtype
  exact privatePowerBiform_val_linearIndependent hs l hl ι

end Froberg
