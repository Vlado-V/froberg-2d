module

public import Froberg.FormalHomology
public import Froberg.MatrixKoszul

@[expose] public section

/-! Literal coefficient reduction implies the precise equality of formal
relation spaces needed by the hyperplane replacement. The target map is
arbitrary, so the same result applies after deleting pure scalar targets. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg
variable {K : Type} [Field K]
variable {V Z A : Type*} [AddCommGroup V] [Module K V]
  [AddCommGroup Z] [Module K Z]
variable {r : ℕ}

def coefficientBoundary (q : Fin r → V) (M : Fin r → Fin r → K) : Fin r → V :=
  fun i => (∑ j,M i j • q j)-(∑ j,M j i • q j)

theorem formalCoefficientMap_boundary (q : Fin r → V) (M : Fin r → Fin r → K) :
    formalCoefficientMap (K := K) q (coefficientBoundary q M)=0 := by
  have hs (i : Fin r) (c : Fin r → K) :
      symProd (q i) (∑ j,c j • q j)=∑ j,c j • symProd (K := K) (q i) (q j) := by
    rw [symProd_comm]
    change (symProdLeft (q i)) (∑ j,c j • q j)=_
    simp only [map_sum,map_smul,symProdLeft]
    congr 1
    funext j
    rw [symProd_comm]
    rfl
  simp only [formalCoefficientMap_apply,coefficientBoundary,symProd_sub_right,hs,
    Finset.sum_sub_distrib]
  apply sub_eq_zero.mpr
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [symProd_comm]

theorem formalCoefficientMap_eq_of_boundary_reduction
    (q c z : Fin r → V) (M : Fin r → Fin r → K)
    (hz : c-coefficientBoundary q M=z) :
    formalCoefficientMap (K := K) q c=formalCoefficientMap (K := K) q z := by
  rw [← hz,map_sub,formalCoefficientMap_boundary,sub_zero]

theorem formalCoefficientMap_mem_products (q z : Fin r → V)
    (Q A : Submodule K V) (hQ : ∀ i,z i=0 ∨ q i∈Q) (hA : ∀ i,z i∈A) :
    formalCoefficientMap (K := K) q z∈formalProducts Q A := by
  rw [formalCoefficientMap_apply]
  apply Submodule.sum_mem
  intro i _
  rcases hQ i with hz|hq
  · rw [hz,symProd_zero_right]
    exact Submodule.zero_mem _
  · exact Submodule.subset_span ⟨q i,z i,hq,hA i,rfl⟩

theorem formal_relations_of_cycle_reduction
    (mu : SymmetricSquare K V →ₗ[K] Z) (q : Fin r → V)
    (Q A : Submodule K V) (hQ : Q≤Submodule.span K (Set.range q))
    (hreduce : ∀ c : Fin r → V,mu (formalCoefficientMap (K := K) q c)=0 →
      ∃ (M : Fin r → Fin r → K) (z : Fin r → V),
        c-coefficientBoundary q M=z ∧ (∀ i,z i=0 ∨ q i∈Q) ∧ (∀ i,z i∈A)) :
    mu.ker ⊓ formalMixed (Submodule.span K (Set.range q))=
      mu.ker ⊓ formalProducts Q A := by
  apply le_antisymm
  · rintro x ⟨hx,hm⟩
    rw [← range_formalCoefficientMap (K := K) q] at hm
    obtain ⟨c,rfl⟩ := hm
    obtain ⟨M,z,hz,hzQ,hzA⟩ := hreduce c hx
    refine ⟨hx,?_⟩
    rw [formalCoefficientMap_eq_of_boundary_reduction q c z M hz]
    exact formalCoefficientMap_mem_products q z Q A hzQ hzA
  · apply inf_le_inf_left
    apply Submodule.span_le.mpr
    rintro _ ⟨a,b,ha,hb,rfl⟩
    exact symProd_mem_formalMixed _ (hQ ha) b

section PolynomialReduction
variable [CommRing A] [Algebra K A]

theorem coefficientBoundary_map (j : V →ₗ[K] A)
    (q : Fin r → V) (M : Fin r → Fin r → K) (i : Fin r) :
    j (coefficientBoundary q M i)=matrixBoundary (fun k => j (q k)) M i := by
  simp only [coefficientBoundary,matrixBoundary,matrixCombination,Pi.sub_apply,
    map_sub,map_sum,map_smul]

theorem boundary_reduction_of_injective_map (j : V →ₗ[K] A)
    (hj : Function.Injective j) (q c z : Fin r → V) (M : Fin r → Fin r → K)
    (h : (fun i => j (c i))-matrixBoundary (fun i => j (q i)) M=(fun i => j (z i))) :
    c-coefficientBoundary q M=z := by
  funext i
  apply hj
  rw [Pi.sub_apply,map_sub,coefficientBoundary_map]
  exact congrFun h i

end PolynomialReduction
end Froberg
