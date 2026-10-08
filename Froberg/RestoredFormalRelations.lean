import Froberg.EvenFormalRelations
import Froberg.EvenRestorationSpace
import Froberg.ParityWeights

/-! The checked natural-weight restoration statement gives the exact
formal-relation equality for the intrinsic projected endpoint complex. -/
noncomputable section
set_option maxHeartbeats 1400000
namespace Froberg
open Module MvPolynomial
variable {K : Type} [Field K] {n d r : ℕ}
variable {Z : Type*} [AddCommGroup Z] [Module K Z]

def restorationForms (w : Fin n → ℕ)
    (g : Fin r → evenRestorationSpace (K := K) w d) : Fin r → Forms K n d :=
  fun i => ⟨(g i).val,(g i).property.1⟩

theorem restorationForms_even (w : Fin n → ℕ)
    (g : Fin r → evenRestorationSpace (K := K) w d) (i : Fin r) :
    (restorationForms w g i).val.IsWeightedHomogeneous (fun x => (w x : ZMod 2)) 0 := by
  apply (parity_homogeneous_iff w (g i).val 0 (by omega)).mpr
  exact (mem_weightedParitySpace_iff w 0 (g i).val).mp (g i).property.2

theorem restored_projected_formal_relations
    (htwo : (2 : K)≠0) (w : Fin n → ℕ)
    (g : Fin r → evenRestorationSpace (K := K) w d)
    (hi : LinearIndependent K (restorationForms w g))
    (pi : Forms K n (2*d) →ₗ[K] Z)
    (hpi : ∀ z,pi z=0 → parityForm (fun x => (w x : ZMod 2)) 1 z=0)
    (hpositive : ∀ z,pi z=0 → positiveWeightProjection w d z.val=0)
    (hodd : ∀ a : (endpointMultiplication (restorationForms w g)).ker,
      (∀ i,(a.val i).val.IsWeightedHomogeneous (fun x => (w x : ZMod 2)) 1) →
      a.val∈oppositeKoszulSpace (restorationForms w g) (fun _ => 0))
    (degree : Fin r → ℕ) (Q A : Submodule K (Forms K n d))
    (hQ : Q≤Submodule.span K (Set.range (restorationForms w g)))
    (hlabel : ∀ i,degree i=0 → restorationForms w g i∈Q)
    (hscalar : ∀ f : Forms K n d,f.val.IsWeightedHomogeneous w 0 → f∈A)
    (hreduce : ∀ c : Fin r → evenRestorationSpace (K := K) w d,
      PolynomialRestoration.row (evenRestorationSpace w d).subtype
        (positiveWeightProjection w d) g c=0 →
      ∃ (M : Fin r → Fin r → K) (z : retainedScalarCoefficients (K := K) w d degree),
        c-coefficientBoundary g M=z.val) :
    (pi.comp formalPolynomialMultiplication).ker ⊓
        formalMixed (Submodule.span K (Set.range (restorationForms w g)))=
      (pi.comp formalPolynomialMultiplication).ker ⊓ formalProducts Q A := by
  classical
  apply projected_formal_relations_of_even_reduction htwo (fun x => (w x : ZMod 2))
    (fun _ => 0) (restorationForms w g) hi (restorationForms_even w g) pi hpi
    (by
      intro a ha
      apply hodd a
      intro i
      convert ha i using 1 <;> norm_num) Q A hQ
  intro c hc
  let c' : Fin r → evenRestorationSpace (K := K) w d := fun i =>
    ⟨(c.val i).val,(c.val i).property,by
      apply (mem_weightedParitySpace_iff w 0 (c.val i).val).mpr
      apply (parity_homogeneous_iff w (c.val i).val 0 (by omega)).mp
      convert hc i using 1 <;> norm_num⟩
  have hc' : PolynomialRestoration.row (evenRestorationSpace w d).subtype
      (positiveWeightProjection w d) g c'=0 := by
    have hh := hpositive (endpointMultiplication (restorationForms w g) c.val) c.property
    change positiveWeightProjection w d (∑ i,(g i).val*(c.val i).val)=0
    have heq : (endpointMultiplication (restorationForms w g) c.val).val=
        ∑ i,(g i).val*(c.val i).val := by
      simp only [endpointMultiplication,LinearMap.sum_apply,LinearMap.comp_apply,
        LinearMap.proj_apply,Submodule.coe_sum]
      rfl
    rw [heq] at hh
    exact hh
  obtain ⟨M,z,hz⟩ := hreduce c' hc'
  let z' : Fin r → Forms K n d := fun i => ⟨(z.val i).val,(z.val i).property.1⟩
  refine ⟨M,z',?_,?_,?_⟩
  · apply boundary_reduction_of_injective_map (Forms K n d).subtype Subtype.val_injective
    funext i
    have hh := congrArg Subtype.val (congrFun hz i)
    simpa only [Pi.sub_apply,Submodule.coe_sub,coefficientBoundary,Submodule.coe_sum,
      Submodule.coe_smul,matrixBoundary,matrixCombination,c',z',restorationForms,
      Submodule.subtype_apply] using hh
  · intro i
    by_cases hdeg : degree i=0
    · exact Or.inr (hlabel i hdeg)
    · left
      apply Subtype.ext
      change (z.val i).val=0
      exact congrArg (fun a : evenRestorationSpace (K := K) w d => a.val) (z.property.1 i (by omega))
  · intro i
    exact hscalar (z' i) (z.property.2 i)

end Froberg
