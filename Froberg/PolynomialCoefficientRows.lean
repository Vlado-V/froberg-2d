import Froberg.PolynomialRowRelations
import Froberg.PureScalarCoordinates
import Froberg.CoefficientRowFromPairs
import Froberg.EvenCoefficientElimination

/-! The exact finite polynomial row yields the literal coefficient-row rule
used to eliminate homogeneous syzygies. -/
noncomputable section
set_option maxHeartbeats 1200000
namespace Froberg
open Module MvPolynomial AttachedMultiplication
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} [Fintype σ] {n d R s r : ℕ}

/-- No coordinate or matrix exactness premise remains after the actual
polynomial row kernel and its independent product columns have been supplied. -/
theorem polynomial_coefficient_row_exact
    {W : Type*} [AddCommGroup W] [Module K W]
    (hRs : R+s=d) (j : Fin r → ℕ)
    (o : Fin (finrank K (homogeneousSubmodule σ K R)) → MvPolynomial σ K)
    (ho : LinearIndependent K o) (hdeg : ∀ i,(o i).IsHomogeneous R)
    (e : {i : Fin r // j i=R} → Fin n →₀ ℕ)
    (v : {i : Fin r // j i=R} → Fin (finrank K (homogeneousSubmodule σ K R)) → K)
    (he : ∀ i,(e i).degree=s) (Q : Fin r → Forms K n d)
    (E : Fin r → MvPolynomial (σ ⊕ Fin n) K)
    (hE : ∀ i : {i : Fin r // j i=R},E i.val=attachedPolynomialFamily o e v i)
    (P : W →ₗ[K] MvPolynomial (σ ⊕ Fin n) K)
    (hker : (addRow (polynomialIntermediateRow o e v he Q) P).ker=
      ((LinearMap.inl K
        ((Fin r → Fin (finrank K (homogeneousSubmodule σ K R)) → Forms K n s) ×
          ({i : Fin r // j i=R} → Forms K n d)) W).comp (intermediateKoszul e v he Q)).range)
    (hpairs : LinearIndependent K
      (fun p : {p : Sym2 (Fin r) // positiveDegreePair j R p} => pairProducts E p.val))
    (hproducts : ∀ p : {p : Sym2 (Fin r) // positiveDegreePair j R p},pairProducts E p.val∈P.range) :
    CoefficientRowExact
      (coefficientComponentSpace (Sum.elim (fun _ : σ => 1) (fun _ : Fin n => 0)) d)
      (fun i => rename Sum.inr (Q i).val) E j R := by
  classical
  apply coefficientRowExact_of_independent_products _ _ _ _ _ hpairs
  intro u b p hu hb hp hrel
  have hu' : ∀ i,u i∈biformImage (homogeneousSubmodule σ K R) (Forms K n s) := by
    intro i
    apply mem_biformImage_of_homogeneous
    · rw [hRs]
      exact (hu i).1
    · exact (hu i).2
  have hb' : ∀ i,∃ f : Forms K n d,rename Sum.inr f.val=b i := by
    intro i
    exact homogeneous_output_zero_exists (hb i).1 (hb i).2
  choose f hf using hb'
  have hp' : p∈P.range := (Submodule.span_le.mpr (by rintro _ ⟨a,rfl⟩; exact hproducts a)) hp
  have hsum : (∑ a : {i : Fin r // j i=R},
      attachedPolynomialFamily o e v a*rename Sum.inr (f a.val).val)=
      ∑ i,if j i=R then E i*b i else 0 := by
    apply Fintype.sum_of_injective Subtype.val Subtype.val_injective
    · intro i hi
      have hji : j i≠R := fun h => hi ⟨⟨i,h⟩,rfl⟩
      simp only [hji,ite_false]
    · intro a
      rw [← hE a,hf a.val,if_pos a.property]
  have hrel' : (∑ i,rename Sum.inr (Q i).val*u i)+
      (∑ a : {i : Fin r // j i=R},attachedPolynomialFamily o e v a*rename Sum.inr (f a.val).val)+p=0 := by
    rw [hsum]
    exact hrel
  obtain ⟨C,hCu,hCb,hpzero⟩ := polynomial_row_relation_constants o ho hdeg e v he Q P hker
    u hu' (fun a => f a.val) p hp' hrel'
  let C' : Fin r → Fin r → K := fun i k => if h : j k=R then C i ⟨k,h⟩ else 0
  refine ⟨C',?_,?_,?_,hpzero⟩
  · intro i k hk
    simp only [C',dif_neg hk]
  · intro i
    rw [hCu i]
    unfold matrixCombination
    apply Fintype.sum_of_injective Subtype.val Subtype.val_injective
    · intro k hk
      have hjk : j k≠R := fun h => hk ⟨⟨k,h⟩,rfl⟩
      simp only [C',dif_neg hjk,zero_smul]
    · intro a
      simp only [C',dif_pos a.property]
      rw [hE a]
  · intro k hk
    rw [← hf k,hCb ⟨k,hk⟩]
    simp only [map_neg,map_sum,map_smul,C',dif_pos hk]

end Froberg
