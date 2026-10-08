import Froberg.PolynomialVectorRows
import Froberg.HomogeneousOutputCoordinates
import Froberg.BiformScalarProjection

/-! Exact coordinates for every homogeneous biform coefficient. -/
noncomputable section
namespace Froberg
open Module MvPolynomial TensorProduct Finset
variable {K : Type} [Field K] [Infinite K]
variable {σ τ I : Type*} [Fintype σ] [Fintype τ] [Fintype I]

/-- The exponent's output weight is exactly its first block's degree. -/
theorem output_weight_sumElim (a : σ →₀ ℕ) (b : τ →₀ ℕ) :
    Finsupp.weight (Sum.elim (fun _ : σ => 1) (fun _ : τ => 0)) (a.sumElim b)=a.degree := by
  rw [Finsupp.weight_eq_sum,Fintype.sum_sum_type,Finsupp.degree_eq_sum]
  simp

/-- Total homogeneity and output homogeneity characterize the actual biform
space; no tensor-image membership assumption is needed. -/
theorem mem_biformImage_of_homogeneous {R s : ℕ} {f : MvPolynomial (σ ⊕ τ) K}
    (hf : f.IsHomogeneous (R+s))
    (hR : f.IsWeightedHomogeneous (Sum.elim (fun _ : σ => 1) (fun _ : τ => 0)) R) :
    f∈biformImage (homogeneousSubmodule σ K R) (homogeneousSubmodule τ K s) := by
  classical
  rw [f.as_sum]
  apply Submodule.sum_mem
  intro α hα
  have hc : f.coeff α≠0 := mem_support_iff.mp hα
  have ht := hf hc
  have hx := hR hc
  obtain ⟨⟨a,b⟩,hab⟩ :=
    (Finsupp.sumFinsuppEquivProdFinsupp (α := σ) (β := τ) (γ := ℕ)).symm.surjective α
  change a.sumElim b=α at hab
  subst α
  have ha : a.degree=R := by simpa only [output_weight_sumElim] using hx
  have htotal : a.degree+b.degree=R+s := by
    have ht' : (a.sumElim b).degree=R+s := by
      simpa only [Finsupp.degree_eq_weight_one,Pi.one_def] using ht
    simpa only [Finsupp.sumElim_eq_add,map_add,Finsupp.degree_mapDomain] using ht'
  have hb : b.degree=s := by omega
  rw [monomial_sumElim]
  exact mul_mem_biformImage _ _ (isHomogeneous_monomial _ ha) (isHomogeneous_monomial _ hb)

/-- Every element of the biform space is represented by homogeneous scalar
coordinates against an output basis. -/
theorem polynomialFormVector_range_basis {n s : ℕ}
    (O : Submodule K (MvPolynomial σ K)) (b : Basis I K O) :
    (polynomialFormVector (fun i => (b i).val) s (n := n)).range=
      biformImage O (Forms K n s) := by
  classical
  apply le_antisymm
  · rintro f ⟨p,rfl⟩
    exact polynomialFormVector_mem_biform _ O (Forms K n s) (fun i => (b i).property) p (fun i => (p i).property)
  · rintro f ⟨a,⟨z,rfl⟩,rfl⟩
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
      refine ⟨fun i => (b.equivFun x i) • y,?_⟩
      change polynomialFormVector (fun i => (b i).val) s
        (fun i => (b.equivFun x i) • y)=
        tensorEquivSum K σ (Fin n) K (x.val ⊗ₜ[K] y.val)
      rw [tensorEquivSum_tmul,polynomialFormVector_apply,polynomialVector_apply]
      have hx : (∑ i,(b.equivFun x i) • (b i).val)=x.val := by
        have hh := congrArg Subtype.val (b.equivFun_symm_apply (b.equivFun x))
        simpa only [LinearEquiv.symm_apply_apply,Submodule.coe_sum,Submodule.coe_smul] using hh.symm
      rw [← hx,map_sum,Finset.sum_mul]
      apply sum_congr rfl
      intro i hi
      simp only [Submodule.coe_smul,map_smul,mul_smul_comm,smul_mul_assoc]
    | add z z' hz hz' =>
      rcases hz with ⟨p,hp⟩
      rcases hz' with ⟨q,hq⟩
      exact ⟨p+q,by simpa only [map_add] using congrArg₂ HAdd.hAdd hp hq⟩

/-- A linearly independent complete output list supplies all coordinates in
its ordinary homogeneous biform space. -/
theorem polynomialFormVector_range_complete {n R s : ℕ}
    (o : Fin (finrank K (homogeneousSubmodule σ K R)) → MvPolynomial σ K)
    (ho : LinearIndependent K o) (hdeg : ∀ i,(o i).IsHomogeneous R) :
    (polynomialFormVector (n := n) o s).range=
      biformImage (homogeneousSubmodule σ K R) (Forms K n s) := by
  let O := homogeneousSubmodule σ K R
  letI : Module.Finite K O := Module.Finite.of_basis (finiteVariableFormsBasis (K := K) σ R)
  let b' : Fin (finrank K O) → O := fun i => ⟨o i,hdeg i⟩
  have hbi : LinearIndependent K b' := LinearIndependent.of_comp O.subtype ho
  let b := basisOfLinearIndependentOfCardEqFinrank' b' hbi (by simp)
  have hb : (fun i => (b i).val)=o := by
    funext i
    have h := congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' b' hbi (by simp)) i
    exact congrArg Subtype.val h
  rw [← hb]
  exact polynomialFormVector_range_basis O b

end Froberg
