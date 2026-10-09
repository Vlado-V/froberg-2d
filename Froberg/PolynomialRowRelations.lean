module

public import Froberg.BiformCoordinates
public import Froberg.PolynomialOutputImage

@[expose] public section

/-! Unpacked scalar coefficients of the exact polynomial row kernel. -/
noncomputable section
namespace Froberg
open MvPolynomial Module AttachedMultiplication
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} [Fintype σ]
variable {n R s d r : ℕ}
variable {J : Type*} [Fintype J]

theorem zero_form_eq_C (f : Forms K n 0) : f.val=C (f.val.coeff 0) := by
  simpa only [homogeneousComponent_zero] using (homogeneousComponent_eq_self f.property).symm

/-- A kernel equality yields literal constant coefficients for every scalar
and new-layer term, and kills the complete product summand. -/
theorem polynomial_row_relation_constants
    {W : Type*} [AddCommGroup W] [Module K W]
    (o : Fin (finrank K (homogeneousSubmodule σ K R)) → MvPolynomial σ K)
    (ho : LinearIndependent K o) (hdeg : ∀ i,(o i).IsHomogeneous R)
    (e : J → Fin n →₀ ℕ)
    (v : J → Fin (finrank K (homogeneousSubmodule σ K R)) → K)
    (he : ∀ i,(e i).degree=s) (Q : Fin r → Forms K n d)
    (P : W →ₗ[K] MvPolynomial (σ ⊕ Fin n) K)
    (hker : (addRow (polynomialIntermediateRow o e v he Q) P).ker=
      ((LinearMap.inl K
        ((Fin r → Fin (finrank K (homogeneousSubmodule σ K R)) → Forms K n s) ×
          (J → Forms K n d)) W).comp (intermediateKoszul e v he Q)).range)
    (U : Fin r → MvPolynomial (σ ⊕ Fin n) K)
    (hU : ∀ i,U i∈biformImage (homogeneousSubmodule σ K R) (Forms K n s))
    (B : J → Forms K n d) (p : MvPolynomial (σ ⊕ Fin n) K) (hp : p∈P.range)
    (hrel : (∑ i,rename Sum.inr (Q i).val*U i)+
      (∑ a,attachedPolynomialFamily o e v a*rename Sum.inr (B a).val)+p=0) :
    ∃ C : Fin r → J → K,
      (∀ i,U i=∑ a,C i a • attachedPolynomialFamily o e v a) ∧
      (∀ a,(B a).val = -∑ i,C i a • (Q i).val) ∧ p=0 := by
  have hcoords (i : Fin r) : ∃ u : Fin (finrank K (homogeneousSubmodule σ K R)) → Forms K n s,
      polynomialFormVector o s u=U i := by
    change U i∈(polynomialFormVector (n := n) o s).range
    rw [polynomialFormVector_range_complete o ho hdeg]
    exact hU i
  choose u hu using hcoords
  obtain ⟨a,ha⟩ := hp
  have hx : ((u,B),a)∈(addRow (polynomialIntermediateRow o e v he Q) P).ker := by
    change polynomialIntermediateRow o e v he Q (u,B)+P a=0
    rw [polynomialIntermediateRow_eq_addRow,addRow_apply,polynomialLayerRow_apply,ha]
    have hS : polynomialScalarRow o Q u=∑ i,rename Sum.inr (Q i).val*U i := by
      unfold polynomialScalarRow
      rw [LinearMap.comp_apply,BilinearScalarFamily.multiplication_apply,map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [polynomialFormVector_vectorMultiply,hu]
    rw [hS]
    exact hrel
  rw [hker] at hx
  obtain ⟨c,hc⟩ := hx
  have hcfirst : (intermediateKoszul e v he Q c).1=u := congrArg (fun x => x.1.1) hc
  have hcsecond : (intermediateKoszul e v he Q c).2=B := congrArg (fun x => x.1.2) hc
  have hca : (0 : W)=a := congrArg Prod.snd hc
  refine ⟨fun i a => (c i a).val.coeff 0,?_,?_,?_⟩
  · intro i
    rw [← hu i,← congrFun hcfirst i]
    change polynomialVector o (multiplication e v (c i))=_
    rw [← attachedPolynomialFamily_multiplication]
    apply Finset.sum_congr rfl
    intro a ha
    rw [zero_form_eq_C,rename_C,mul_comm,MvPolynomial.C_mul']
  · intro a
    have h := congrArg (fun q : J → Forms K n d => (q a).val) hcsecond
    change ((-∑ i,fun a => constantMul (Q i) (c i a)) a).val = (B a).val at h
    rw [← h]
    simp only [Pi.neg_apply,Finset.sum_apply,Submodule.coe_neg,Submodule.coe_sum,constantMul_val]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [zero_form_eq_C,mul_comm,MvPolynomial.C_mul']
    simp
  · rw [← ha,← hca,map_zero]

end Froberg
