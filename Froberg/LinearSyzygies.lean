module

public import Froberg.LinearEndpoint

@[expose] public section

/-! Exact linear-coefficient syzygies of independent linear forms. This is
the private-power overlap calculation used in the degree-two row of B.4. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module
variable {K : Type*} [Field K] {n r : ℕ}

theorem linear_homology_eq_zero (hn : 0 < n) (q : Fin r → Forms K n 1)
    (hq : LinearIndependent K q) : finrank K (EndpointHomology q) = 0 := by
  have hr : r ≤ n := by
    have h := (Submodule.span K (Set.range q)).finrank_le
    rw [finrank_span_eq_card hq,Fintype.card_fin,finrank_forms K n 1 hn] at h
    simpa using h
  have he := endpoint_euler_identity hn q hq
  rw [endpoint_quotient_linear hn q hq,euler_linear hr] at he
  simp only [expectedEndpoint,euler_linear hr,Int.toNat_natCast] at he
  omega

/-- There are exactly the constant alternating relations, over every field. -/
theorem linear_endpoint_kernel (hn : 0 < n) (q : Fin r → Forms K n 1)
    (hq : LinearIndependent K q) : (endpointMultiplication q).ker = koszulSpace q := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq (kernel_contains_koszul q)
  have hd := homology_add_pairs q hq
  rw [linear_homology_eq_zero hn q hq,zero_add] at hd
  rw [← hd]
  exact (finrank_span_eq_card (koszulVector_linearIndependent q hq)).trans card_generatorPair

/-- Two independent linear factors have only their common scalar product
as an overlap of their spaces of quadratic multiples. -/
theorem independent_linear_product_overlap (hn : 0 < n)
    (q : Fin 2 → Forms K n 1) (hq : LinearIndependent K q)
    (a b : Forms K n 1) (hprod : mulForm (q 0) a = mulForm (q 1) b) :
    ∃ c : K, a = c • q 1 ∧ b = c • q 0 := by
  classical
  let v : Fin 2 → Forms K n 1 := ![a,-b]
  have hv : v ∈ (endpointMultiplication q).ker := by
    change endpointMultiplication q v = 0
    simp only [endpointMultiplication,LinearMap.sum_apply,LinearMap.add_apply,LinearMap.comp_apply,
      LinearMap.proj_apply,Fin.sum_univ_two,v,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_fin_one,map_neg]
    simpa only [sub_eq_add_neg] using sub_eq_zero.mpr hprod
  rw [linear_endpoint_kernel hn q hq] at hv
  let p : GeneratorPair 2 := ⟨(0,1),by decide⟩
  have hp : ∀ x : GeneratorPair 2, x=p := by
    intro x
    fin_cases x <;> rfl
  have hspan : koszulSpace q = Submodule.span K {koszulVector q p} := by
    unfold koszulSpace
    congr 1
    ext x
    constructor
    · rintro ⟨i,rfl⟩
      rw [hp i]
      exact Set.mem_singleton _
    · intro hx
      exact ⟨p,Set.mem_singleton_iff.mp hx |>.symm⟩
  rw [hspan] at hv
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hv
  refine ⟨c,?_,?_⟩
  · have h := congrFun hc 0
    simpa [v,koszulVector,p] using h.symm
  · have h := congrFun hc 1
    have hh : -(c • q 0) = -b := by simpa [v,koszulVector,p] using h
    exact (neg_inj.mp hh).symm

end Froberg
