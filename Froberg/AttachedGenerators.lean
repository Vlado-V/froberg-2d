import Froberg.AttachedAmbientGrowth
import Froberg.VectorMultiplicationCoordinates

/-! Actual homogeneous generators of an attached presentation. -/
noncomputable section
namespace Froberg.AttachedMultiplication
open Module MvPolynomial
open Quartic
variable {K L I J : Type*} [Field K] [Field L] [Algebra K L]
  [Fintype I] [Fintype J] {n s d : ℕ}

def generator (e : I → Fin n →₀ ℕ) (v : I → J → K) (he : ∀ i,(e i).degree=s)
    (i : I) : J → Forms K n s :=
  fun j => ⟨monomial (e i) (v i j),isHomogeneous_monomial _ (he i)⟩

lemma generator_mem (e : I → Fin n →₀ ℕ) (v : I → J → K)
    (he : ∀ i,(e i).degree=s) (i : I) : generator e v he i ∈ relationSpace (d := 0) e v he := by
  classical
  let one : Forms K n 0 := ⟨1,isHomogeneous_one _ _⟩
  refine ⟨Pi.single i one,?_⟩
  funext j
  apply Subtype.ext
  simp [homogeneousMultiplication_val,multiplication,Pi.single_apply,generator,one,apply_ite]

lemma relationSpace_zero_eq_span (e : I → Fin n →₀ ℕ) (v : I → J → K)
    (he : ∀ i,(e i).degree=s) :
    relationSpace (d := 0) e v he=Submodule.span K (Set.range (generator e v he)) := by
  classical
  apply le_antisymm
  · rintro _ ⟨a,rfl⟩
    have hc (i : I) : ∃ c : K,(a i).val=C c :=
      ⟨(a i).val.coeff 0,totalDegree_eq_zero_iff_eq_C.mp
        ((totalDegree_zero_iff_isHomogeneous (Fin n)).mpr (a i).property)⟩
    choose c hc using hc
    have heq : homogeneousMultiplication e v he a=∑ i,c i • generator e v he i := by
      funext j
      apply Subtype.ext
      simp only [homogeneousMultiplication_val,multiplication_apply,hc,Finset.sum_apply,
        Pi.smul_apply,Submodule.coe_sum,Submodule.coe_smul,generator]
      apply Finset.sum_congr rfl
      intro i _
      rw [smul_eq_C_mul,mul_comm]
    rw [heq]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,rfl⟩))
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact generator_mem e v he i

lemma tupleMap_generator (e : I → Fin n →₀ ℕ) (v : I → J → K)
    (he : ∀ i,(e i).degree=s) :
    BilinearImage.tupleMap (vectorMultiply (d := d)) (generator e v he)=homogeneousMultiplication e v he := by
  apply LinearMap.ext
  intro a
  funext j
  apply Subtype.ext
  simp only [BilinearImage.tupleMap_apply,Finset.sum_apply,Submodule.coe_sum,vectorMultiply_val,
    homogeneousMultiplication_val,multiplication_apply,generator]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

lemma generator_independent (e : I → Fin n →₀ ℕ) (v : I → J → K)
    (he : ∀ i,(e i).degree=s) (hi : Function.Injective (multiplication (d := 0) e v))
    (hn : 0 < n) : LinearIndependent K (generator e v he) := by
  apply linearIndependent_iff_card_eq_finrank_span.mpr
  change Fintype.card I=finrank K (Submodule.span K (Set.range (generator e v he)))
  rw [← relationSpace_zero_eq_span]
  change Fintype.card I=finrank K (LinearMap.range (homogeneousMultiplication (d := 0) e v he))
  rw [LinearMap.finrank_range_of_inj (homogeneousMultiplication_injective e v he hi)]
  simp [Module.finrank_pi_fintype,finrank_forms K n 0 hn]

lemma map_generator {h : ℕ} (e : I → Fin n →₀ ℕ) (v : I → Fin h → K)
    (he : ∀ i,(e i).degree=s) (i : I) :
    VectorMultiplicationCoordinates.mapRows (L := L) (generator e v he i)=
      generator e (fun i j => algebraMap K L (v i j)) he i := by
  funext j
  apply Subtype.ext
  exact MvPolynomial.map_monomial _ _ _

end Froberg.AttachedMultiplication
