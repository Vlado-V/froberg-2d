import Froberg.IntrinsicBiformRow
import Froberg.PureScalarCoordinates
import Froberg.CoefficientRowFromPairs
import Froberg.EvenCoefficientElimination

/-! Intrinsic exact row kernels imply the literal coefficient equations used
by the polynomial elimination, without any sparse form assumption. -/
noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial
variable {K : Type} [Field K] [Infinite K]
variable {σ I J W : Type*} [Fintype σ] [Fintype I] [Fintype J]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
variable {n d R s : ℕ}

theorem intrinsic_row_relation_constants
    (Q : I → Forms K n d) (E : J → FullBiform K σ n R s)
    (P : W →ₗ[K] MvPolynomial (σ ⊕ Fin n) K)
    (hker : (bilinearKoszulRow (fullBiformScalarProduct (σ := σ) (n := n) (R := R) (s := s) (d := d)) Q E P).ker=
      (bilinearKoszulConstants (K := K) (W := W) Q E).range)
    (u : I → MvPolynomial (σ ⊕ Fin n) K) (hu : ∀ i,u i∈FullBiform K σ n R s)
    (b : J → Forms K n d) (p : MvPolynomial (σ ⊕ Fin n) K) (hp : p∈P.range)
    (hrel : (∑ i,rename Sum.inr (Q i).val*u i)+
      (∑ j,(E j).val*rename Sum.inr (b j).val)+p=0) :
    ∃ C : I → J → K,
      (∀ i,u i=∑ j,C i j • (E j).val) ∧
      (∀ j,(b j).val= -∑ i,C i j • (Q i).val) ∧ p=0 := by
  obtain ⟨z,rfl⟩ := hp
  let x : ((I → FullBiform K σ n R s) × (J → Forms K n d)) × W :=
    ((fun i => ⟨u i,hu i⟩,b),z)
  have hx : x∈(bilinearKoszulRow (fullBiformScalarProduct (σ := σ) (n := n) (R := R) (s := s) (d := d)) Q E P).ker := by
    apply LinearMap.mem_ker.mpr
    simpa only [bilinearKoszulRow,LinearMap.coe_mk,AddHom.coe_mk,x,
      fullBiformScalarProduct_apply,mul_comm] using hrel
  rw [hker] at hx
  obtain ⟨C,hC⟩ := hx
  refine ⟨C,?_,?_,?_⟩
  · intro i
    have hi := congrArg (fun y : ((I → FullBiform K σ n R s) × (J → Forms K n d)) × W => (y.1.1 i).val) hC
    change (∑ j,C i j • E j).val=u i at hi
    simpa only [Submodule.coe_sum,Submodule.coe_smul] using hi.symm
  · intro j
    have hj := congrArg (fun y : ((I → FullBiform K σ n R s) × (J → Forms K n d)) × W => (y.1.2 j).val) hC
    change (-∑ i,C i j • Q i).val=(b j).val at hj
    simpa only [Submodule.coe_neg,Submodule.coe_sum,Submodule.coe_smul] using hj.symm
  · have hz := congrArg (fun y : ((I → FullBiform K σ n R s) × (J → Forms K n d)) × W => y.2) hC
    change 0=z at hz
    rw [←hz,map_zero]

/-- Exactness of the full intrinsic row is exactly the coefficient-row rule
needed by the increasing-degree induction. -/
theorem intrinsic_polynomial_coefficient_row_exact
    (hRs : R+s=d) (j : I → ℕ) (Q : I → Forms K n d)
    (E : I → MvPolynomial (σ ⊕ Fin n) K)
    (Erow : {i : I // j i=R} → FullBiform K σ n R s)
    (hE : ∀ i : {i : I // j i=R},E i.val=(Erow i).val)
    (P : W →ₗ[K] MvPolynomial (σ ⊕ Fin n) K)
    (hker : (bilinearKoszulRow (fullBiformScalarProduct (σ := σ) (n := n) (R := R) (s := s) (d := d)) Q Erow P).ker=
      (bilinearKoszulConstants (K := K) (W := W) Q Erow).range)
    (hpairs : LinearIndependent K
      (fun p : {p : Sym2 I // positiveDegreePair j R p} => pairProducts E p.val))
    (hproducts : ∀ p : {p : Sym2 I // positiveDegreePair j R p},pairProducts E p.val∈P.range) :
    CoefficientRowExact
      (coefficientComponentSpace (Sum.elim (fun _ : σ => 1) (fun _ : Fin n => 0)) d)
      (fun i => rename Sum.inr (Q i).val) E j R := by
  classical
  apply coefficientRowExact_of_independent_products _ _ _ _ _ hpairs
  intro u b p hu hb hp hrel
  have hu' : ∀ i,u i∈FullBiform K σ n R s := by
    intro i
    apply mem_biformImage_of_homogeneous
    · rw [hRs]
      exact (hu i).1
    · exact (hu i).2
  have hb' : ∀ i,∃ f : Forms K n d,rename Sum.inr f.val=b i :=
    fun i => homogeneous_output_zero_exists (hb i).1 (hb i).2
  choose f hf using hb'
  have hp' : p∈P.range := (Submodule.span_le.mpr (by rintro _ ⟨a,rfl⟩; exact hproducts a)) hp
  have hsum : (∑ a : {i : I // j i=R},
      (Erow a).val*rename Sum.inr (f a.val).val)=∑ i,if j i=R then E i*b i else 0 := by
    apply Fintype.sum_of_injective Subtype.val Subtype.val_injective
    · intro i hi
      have hji : j i≠R := fun h => hi ⟨⟨i,h⟩,rfl⟩
      simp only [hji,ite_false]
    · intro a
      rw [←hE a,hf a.val,if_pos a.property]
  obtain ⟨C,hCu,hCb,hpzero⟩ := intrinsic_row_relation_constants Q Erow P hker u hu'
    (fun a => f a.val) p hp' (by rw [hsum]; exact hrel)
  let C' : I → I → K := fun i k => if h : j k=R then C i ⟨k,h⟩ else 0
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
    rw [←hf k,hCb ⟨k,hk⟩]
    simp only [map_neg,map_sum,map_smul,C',dif_pos hk]

end Froberg
