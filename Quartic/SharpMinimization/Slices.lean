import Quartic.SharpMinimization.Concavity

/-! Explicit triangles covering each fixed-sum slice of the ordered simplex. -/
namespace Quartic.SharpMinimization
noncomputable section

def edgePoint (w s : ℝ) : Fin 6 → Layers :=
  ![![s,0,0], ![s/2,s/2,0], ![s/3,s/3,s/3],
    ![w,s-w,0], ![w,(s-w)/2,(s-w)/2], ![w,w,s-2*w]]

def EdgeFeasible (w s : ℝ) (e : Fin 6) : Prop :=
  (SharpCertificate.edgeLeft e:ℝ)*w ≤ s ∧ s ≤ (SharpCertificate.edgeRight e:ℝ)*w

theorem edgePoint_mem {w s : ℝ} {e : Fin 6} (hw : 0 ≤ w) (he : EdgeFeasible w s e) :
    edgePoint w s e ∈ layerBox w := by
  fin_cases e <;> norm_num [EdgeFeasible,SharpCertificate.edgeLeft,SharpCertificate.edgeRight] at he
  all_goals constructor <;> intro k <;> fin_cases k <;> norm_num [edgePoint] <;> linarith

theorem edgePoint_sum (w s : ℝ) (e : Fin 6) :
    edgePoint w s e 0+edgePoint w s e 1+edgePoint w s e 2=s := by
  fin_cases e <;> norm_num [edgePoint] <;> ring

/-- A slice point is an explicit convex combination of three feasible prefix
edges. The six edges are indexed exactly as in `SharpCertificate`. -/
theorem slice_triangle (w s n₁ n₂ n₃ : ℝ) (hw : 0 ≤ w)
    (hn : 0 ≤ n₃ ∧ n₃ ≤ n₂ ∧ n₂ ≤ n₁ ∧ n₁ ≤ w)
    (hs : n₁+n₂+n₃=s) :
    ∃v : Fin 3 → ℝ, ∃e : Fin 3 → Fin 6,
      (∀j,0 ≤ v j) ∧ (∑j,v j=1) ∧ (∀j,EdgeFeasible w s (e j)) ∧
      (∑j,v j • edgePoint w s (e j)=![n₁,n₂,n₃]) := by
  have hn₁ : 0 ≤ n₁ := hn.1.trans (hn.2.1.trans hn.2.2.1)
  have hn₂ : 0 ≤ n₂ := hn.1.trans hn.2.1
  have hs0 : 0 ≤ s := by linarith
  have hs3 : s ≤ 3*w := by linarith [hn.2.1,hn.2.2.1,hn.2.2.2]
  by_cases hzero : s=0
  · have h₁ : n₁=0 := by linarith
    have h₂ : n₂=0 := by linarith
    have h₃ : n₃=0 := by linarith
    subst s n₁ n₂ n₃
    refine ⟨![1,0,0],![0,0,0],?_,?_,?_,?_⟩
    · intro j; fin_cases j <;> norm_num
    · norm_num [Fin.sum_univ_succ]
    · intro j; fin_cases j <;> simpa [EdgeFeasible,SharpCertificate.edgeLeft,SharpCertificate.edgeRight] using hw
    · ext j; fin_cases j <;> norm_num [Fin.sum_univ_succ,edgePoint]
  have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hzero)
  by_cases hlow : s ≤ w
  · let v : Fin 3 → ℝ := ![(n₁-n₂)/s,2*(n₂-n₃)/s,3*n₃/s]
    let e : Fin 3 → Fin 6 := ![0,1,2]
    refine ⟨v,e,?_,?_,?_,?_⟩
    · intro j; fin_cases j <;> dsimp [v]
      · exact div_nonneg (sub_nonneg.mpr hn.2.2.1) hspos.le
      · exact div_nonneg (by nlinarith [hn.2.1]) hspos.le
      · exact div_nonneg (by nlinarith [hn.1]) (by positivity)
    · norm_num [v,Fin.sum_univ_succ]
      field_simp
      linarith
    · intro j; fin_cases j <;> norm_num [e,EdgeFeasible,SharpCertificate.edgeLeft,SharpCertificate.edgeRight] <;> constructor <;> linarith
    · ext j; fin_cases j <;> norm_num [v,e,Fin.sum_univ_succ,edgePoint]
      all_goals field_simp
      all_goals ring
  by_cases hfull : s=3*w
  · have h₁ : n₁=w := by linarith [hn.2.1,hn.2.2.1,hn.2.2.2]
    have h₂ : n₂=w := by linarith [hn.2.1,hn.2.2.1,hn.2.2.2]
    have h₃ : n₃=w := by linarith [hn.2.1,hn.2.2.1,hn.2.2.2]
    subst n₁ n₂ n₃ s
    refine ⟨![1,0,0],![5,5,5],?_,?_,?_,?_⟩
    · intro j; fin_cases j <;> norm_num
    · norm_num [Fin.sum_univ_succ]
    · intro j; fin_cases j <;> norm_num [EdgeFeasible,SharpCertificate.edgeLeft,SharpCertificate.edgeRight] <;> linarith
    · ext j
      fin_cases j <;> norm_num [Fin.sum_univ_succ,edgePoint]
      ring
  have hrpos : 0 < 3*w-s := sub_pos.mpr (lt_of_le_of_ne hs3 hfull)
  by_cases hhigh : 2*w ≤ s
  · let v : Fin 3 → ℝ := ![(n₂-n₃)/(3*w-s),2*(n₁-n₂)/(3*w-s),3*(w-n₁)/(3*w-s)]
    let e : Fin 3 → Fin 6 := ![5,4,2]
    refine ⟨v,e,?_,?_,?_,?_⟩
    · intro j; fin_cases j <;> dsimp [v]
      · exact div_nonneg (sub_nonneg.mpr hn.2.1) hrpos.le
      · exact div_nonneg (by nlinarith [hn.2.2.1]) hrpos.le
      · exact div_nonneg (by nlinarith [hn.2.2.2]) hrpos.le
    · norm_num [v,Fin.sum_univ_succ]
      field_simp
      linarith
    · intro j; fin_cases j <;> norm_num [e,EdgeFeasible,SharpCertificate.edgeLeft,SharpCertificate.edgeRight] <;> constructor <;> linarith
    · ext j; fin_cases j <;> norm_num [v,e,Fin.sum_univ_succ,edgePoint]
      all_goals field_simp
      all_goals rw [←hs]
      all_goals ring
  have hsw : 0 < s-w := by linarith
  have hws : 0 < 2*w-s := by linarith
  have hcutcases := le_total 0 ((s-w)*(n₁-n₂)-(3*w-s)*n₃)
  rcases hcutcases with hcut | hcut
  · let v : Fin 3 → ℝ := ![2*(w-n₁)/(2*w-s),
      ((s-w)*(n₁-n₂)-(3*w-s)*n₃)/((2*w-s)*(s-w)),2*n₃/(s-w)]
    let e : Fin 3 → Fin 6 := ![1,3,4]
    refine ⟨v,e,?_,?_,?_,?_⟩
    · intro j; fin_cases j <;> dsimp [v]
      · exact div_nonneg (by nlinarith [hn.2.2.2]) hws.le
      · exact div_nonneg hcut (mul_pos hws hsw).le
      · exact div_nonneg (by nlinarith [hn.1]) (by positivity)
    · norm_num [v,Fin.sum_univ_succ]
      field_simp
      rw [←hs]
      ring
    · intro j; fin_cases j <;> norm_num [e,EdgeFeasible,SharpCertificate.edgeLeft,SharpCertificate.edgeRight] <;> constructor <;> linarith
    · ext j; fin_cases j <;> norm_num [v,e,Fin.sum_univ_succ,edgePoint]
      all_goals field_simp
      all_goals rw [←hs]
      all_goals ring
  · let v : Fin 3 → ℝ := ![2*(n₂-n₃)/s,
      3*((3*w-s)*n₃-(s-w)*(n₁-n₂))/(s*(3*w-s)),2*(n₁-n₂)/(3*w-s)]
    let e : Fin 3 → Fin 6 := ![1,2,4]
    refine ⟨v,e,?_,?_,?_,?_⟩
    · intro j; fin_cases j <;> dsimp [v]
      · exact div_nonneg (by nlinarith [hn.2.1]) hspos.le
      · exact div_nonneg (by nlinarith only [hcut]) (mul_pos hspos hrpos).le
      · exact div_nonneg (by nlinarith [hn.2.2.1]) hrpos.le
    · norm_num [v,Fin.sum_univ_succ]
      field_simp
      rw [←hs]
      ring
    · intro j; fin_cases j <;> norm_num [e,EdgeFeasible,SharpCertificate.edgeLeft,SharpCertificate.edgeRight] <;> constructor <;> linarith
    · ext j; fin_cases j <;> norm_num [v,e,Fin.sum_univ_succ,edgePoint]
      all_goals field_simp
      all_goals rw [←hs]
      all_goals ring

/-- Every concave numerical function has a no-larger value on one of the six
prefix edges at the same total layer dimension. -/
theorem exists_prefix_edge_le (w s n₁ n₂ n₃ : ℝ) (hw : 0 ≤ w)
    (hn : 0 ≤ n₃ ∧ n₃ ≤ n₂ ∧ n₂ ≤ n₁ ∧ n₁ ≤ w) (hs : n₁+n₂+n₃=s)
    (f : Layers → ℝ) (hf : ConcaveOn ℝ (layerBox w) f) :
    ∃e:Fin 6, EdgeFeasible w s e ∧ f (edgePoint w s e) ≤ f ![n₁,n₂,n₃] := by
  obtain ⟨v,e,hv,hvsum,he,hn'⟩ := slice_triangle w s n₁ n₂ n₃ hw hn hs
  obtain ⟨j,hj⟩ := exists_le_of_combination hf v (fun j => edgePoint w s (e j))
    hv hvsum (fun j => edgePoint_mem hw (he j)) _ hn'
  exact ⟨e j,he j,hj⟩

end
end Quartic.SharpMinimization
