module

public import Froberg.PolynomialVectorRows

@[expose] public section

/-! Coordinates for embedding a prescribed homogeneous output subspace in
all homogeneous output directions. -/
noncomputable section
namespace Froberg
open Module MvPolynomial
open scoped Classical
variable {K : Type} [Field K]

/-- The monomial basis, for any finite variable type. -/
def finiteVariableFormsBasis (σ : Type*) [Fintype σ] (R : ℕ) :
    Basis (Sym σ R) K (homogeneousSubmodule σ K R) := by
  rw [homogeneousSubmodule_eq_finsupp_supported]
  exact (MvPolynomial.basisRestrictSupport K {e : σ →₀ ℕ | e.degree=R}).reindex
    (Sym.equivNatSum σ R).symm

def outputCombination {J σ : Type*} [Fintype J] (o : J → MvPolynomial σ K) :
    (J → K) →ₗ[K] MvPolynomial σ K where
  toFun v := ∑ j,v j • o j
  map_add' v v' := by simp only [Pi.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' c v := by simp only [Pi.smul_apply,smul_smul,Finset.smul_sum,RingHom.id_apply,smul_eq_mul]

/-- A complete homogeneous output basis can be chosen together with an
injective coordinate inclusion of every specified homogeneous subspace. -/
theorem homogeneous_output_coordinate_embedding {σ : Type*} [Fintype σ] {R : ℕ}
    (O : Submodule K (MvPolynomial σ K)) (hO : O≤homogeneousSubmodule σ K R) :
    ∃ (o : Fin (finrank K (homogeneousSubmodule σ K R)) → MvPolynomial σ K)
      (L : (Fin (finrank K O) → K) →ₗ[K]
        (Fin (finrank K (homogeneousSubmodule σ K R)) → K)),
      LinearIndependent K o ∧ (∀ j,(o j).IsHomogeneous R) ∧
      Function.Injective L ∧ ∀ z,outputCombination o (L z)∈O := by
  let F := homogeneousSubmodule σ K R
  letI : Module.Finite K F := Module.Finite.of_basis (finiteVariableFormsBasis (K := K) σ R)
  letI : FiniteDimensional K O := Submodule.finiteDimensional_of_le hO
  let b := Module.finBasis K F
  let a := Module.finBasis K O
  let f : O →ₗ[K] F := O.subtype.codRestrict F (fun x => hO x.property)
  let L := b.equivFun.toLinearMap.comp (f.comp a.equivFun.symm.toLinearMap)
  let o := fun j => (b j).val
  refine ⟨o,L,?_,?_,?_,?_⟩
  · exact b.linearIndependent.map' F.subtype (LinearMap.ker_eq_bot.mpr F.subtype_injective)
  · exact fun j => (b j).property
  · exact b.equivFun.injective.comp ((by
      intro x y h
      apply Subtype.ext
      exact congrArg (fun z : F => (z : MvPolynomial σ K)) h : Function.Injective f).comp
        a.equivFun.symm.injective)
  · intro z
    have heq : outputCombination o (L z)=(a.equivFun.symm z).val := by
      have hb := b.equivFun_symm_apply (L z)
      have hh := congrArg Subtype.val hb
      change (b.equivFun.symm (b.equivFun (f (a.equivFun.symm z)))).val = _ at hh
      simpa [LinearEquiv.symm_apply_apply,Submodule.coe_sum,Submodule.coe_smul,
        outputCombination,o,f] using hh.symm
    rw [heq]
    exact (a.equivFun.symm z).property

end Froberg
