module

public import Froberg.LinearSyzygies
public import Froberg.FiniteSubspaceProjection

@[expose] public section

/-! The detected quadratic output spaces retain exactly their classical
one-dimensional overlaps after a projection injective on each pair space. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module
variable {K T : Type*} [Field K] [AddCommGroup T] [Module K T] {n : ℕ}

/-- The pair-output space has its precise dimension 2n−1. -/
theorem linear_pair_output_finrank (hn : 0 < n)
    (q : Fin 2 → Forms K n 1) (hq : LinearIndependent K q) :
    finrank K (endpointMultiplication q).range = 2*n-1 := by
  have hr := LinearMap.finrank_range_add_finrank_ker (endpointMultiplication q)
  have hk : finrank K (endpointMultiplication q).ker=1 := by
    rw [linear_endpoint_kernel hn q hq]
    exact (finrank_span_eq_card (koszulVector_linearIndependent q hq)).trans (by
      rw [card_generatorPair]
      decide)
  rw [hk,Module.finrank_pi_fintype,finrank_forms K n 1 hn] at hr
  simp only [Nat.add_sub_cancel,Nat.choose_one_right,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,smul_eq_mul] at hr
  omega

/-- Detection cannot introduce an additional relation between two linear
output columns when their whole pair space embeds in the quotient. -/
theorem detected_linear_pair_relation (hn : 0 < n)
    (q : Fin 2 → Forms K n 1) (hq : LinearIndependent K q)
    (L : Forms K n 2 →ₗ[K] T)
    (hL : Function.Injective (L.comp (endpointMultiplication q).range.subtype))
    (x y : Forms K n 1) (hxy : L (mulForm (q 0) x)+L (mulForm (q 1) y)=0) :
    ∃ t : K, x=t • q 1 ∧ y=(-t) • q 0 := by
  classical
  let a : Fin 2 → Forms K n 1 := ![x,y]
  have ha : endpointMultiplication q a=mulForm (q 0) x+mulForm (q 1) y := by
    simp only [endpointMultiplication,LinearMap.sum_apply,LinearMap.add_apply,
      LinearMap.comp_apply,LinearMap.proj_apply,Fin.sum_univ_two,a,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
  have hz : (⟨endpointMultiplication q a,LinearMap.mem_range_self _ a⟩ : (endpointMultiplication q).range)=0 := by
    apply hL
    change L (endpointMultiplication q a)=L 0
    rw [ha,map_add,hxy,map_zero]
  have hp : mulForm (q 0) x+mulForm (q 1) y=0 := by
    rw [← ha]
    exact congrArg Subtype.val hz
  have he : mulForm (q 0) x=mulForm (q 1) (-y) := by
    rw [map_neg]
    exact eq_neg_of_add_eq_zero_left hp
  obtain ⟨t,ht,hy⟩ := independent_linear_product_overlap hn q hq x (-y) he
  refine ⟨t,ht,?_⟩
  have hh := congrArg Neg.neg hy
  calc
    y = -(t • q 0) := by simpa only [neg_neg] using hh
    _ = (-t) • q 0 := (neg_smul t (q 0)).symm

end Froberg
