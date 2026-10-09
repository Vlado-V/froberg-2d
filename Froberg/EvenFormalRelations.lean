module

public import Froberg.CycleReductionFormal
public import Froberg.ParityComplex
public import Froberg.ProjectedHomologyCoefficients

@[expose] public section

/-! Odd exactness and explicit reduction of even cycles give the complete
projected formal-relation equality used in the hyperplane replacement. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg
variable {K : Type} [Field K] {n d r : ℕ}
variable {Z : Type*} [AddCommGroup Z] [Module K Z]

theorem projected_formal_relations_of_even_reduction
    (w : Fin n → ZMod 2) (e : Fin r → ZMod 2)
    (q : Fin r → Forms K n d) (hi : LinearIndependent K q)
    (hq : ∀ i,(q i).val.IsWeightedHomogeneous w (e i))
    (pi : Forms K n (2*d) →ₗ[K] Z)
    (hpi : ∀ z,pi z=0 → parityForm w 1 z=0)
    (hodd : ∀ a : (endpointMultiplication q).ker,
      (∀ i,(a.val i).val.IsWeightedHomogeneous w (1-e i)) →
      a.val∈oppositeKoszulSpace q e)
    (Q A : Submodule K (Forms K n d)) (hQ : Q≤Submodule.span K (Set.range q))
    (hreduce : ∀ c : (projectedEndpointMultiplication pi q).ker,
      (∀ i,(c.val i).val.IsWeightedHomogeneous w (0-e i)) →
      ∃ (M : Fin r → Fin r → K) (z : Fin r → Forms K n d),
        c.val-coefficientBoundary q M=z ∧ (∀ i,z i=0 ∨ q i∈Q) ∧ (∀ i,z i∈A)) :
    (pi.comp formalPolynomialMultiplication).ker ⊓ formalMixed (Submodule.span K (Set.range q))=
      (pi.comp formalPolynomialMultiplication).ker ⊓ formalProducts Q A := by
  apply le_antisymm
  · rintro x ⟨hx,hm⟩
    rw [← range_formalCoefficientMap q] at hm
    obtain ⟨c,rfl⟩ := hm
    have hc : projectedEndpointMultiplication pi q c=0 := by
      change pi (endpointMultiplication q c)=0
      rw [← formalPolynomialMultiplication_comp q]
      exact hx
    let cycle : (projectedEndpointMultiplication pi q).ker := ⟨c,hc⟩
    obtain ⟨v,hv,hclass⟩ := exists_even_projected_cycle_representative w e q hq pi hpi hodd
      (kernelClass (projectedEndpointMultiplication pi q) (koszulSpace q) cycle)
    have hf := congrArg (projectedFormalRepresentative pi q hi) hclass
    simp only [projectedFormalRepresentative_mk] at hf
    obtain ⟨M,z,hz,hzQ,hzA⟩ := hreduce v hv
    refine ⟨hx,?_⟩
    change formalCoefficientMap q cycle.val∈formalProducts Q A
    rw [← hf,formalCoefficientMap_eq_of_boundary_reduction q v.val z M hz]
    exact formalCoefficientMap_mem_products q z Q A hzQ hzA
  · apply inf_le_inf_left
    apply Submodule.span_le.mpr
    rintro _ ⟨a,b,ha,hb,rfl⟩
    exact symProd_mem_formalMixed _ (hQ ha) b

end Froberg
