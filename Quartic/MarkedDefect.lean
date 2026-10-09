module

public import Quartic.MarkedDefectGeneral

@[expose] public section

/-! The marked coefficient kernel without exactness of the old family. -/
noncomputable section
namespace Quartic.MarkedDefect
open Module EndpointHomology MarkedCoefficient
variable {K : Type*} [Field K] {n r : ℕ}
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem marked_kernel_old_plus_boundary (q : Fin (r + 1) → Quartic.Forms K n 2)
    (hsquare : Quartic.mulQuadratic (q (Fin.last r)) (q (Fin.last r)) ∉
      LinearMap.range (Quartic.quadraticMultiplication (prefixFamily q)))
    (a : Fin (r + 1) → Quartic.Forms K n 2)
    (ha : Quartic.quadraticMultiplication q a = 0)
    (hcoeff : a (Fin.last r) ∈ Submodule.span K (Set.range q)) :
    ∃ b : (quadraticMultiplication (prefixFamily q)).ker,
      a - extendZero (K := K) b.val ∈ koszulSpace q := by
  classical
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hcoeff
  let z := crossBoundary q (fun i : Fin r => c i.castSucc)
  have hzmem : z ∈ Quartic.koszulSpace q := crossBoundary_mem q _
  have hzcycle : Quartic.quadraticMultiplication q z = 0 :=
    Quartic.kernel_contains_koszul q hzmem
  let b := a + z
  have hbcycle : Quartic.quadraticMultiplication q b = 0 := by
    simp only [b, map_add, ha, hzcycle, zero_add]
  have hblast : b (Fin.last r) = c (Fin.last r) • q (Fin.last r) := by
    have hc' : a (Fin.last r) =
        (∑ i : Fin r, c i.castSucc • q i.castSucc) + c (Fin.last r) • q (Fin.last r) := by
      rw [← hc, Fin.sum_univ_castSucc]
    change a (Fin.last r) + z (Fin.last r) = _
    change a (Fin.last r) + crossBoundary q (fun i : Fin r => c i.castSucc) (Fin.last r) = _
    rw [hc', crossBoundary_last]
    abel
  have hsplit := quadraticMultiplication_split_last q b
  rw [hbcycle, hblast, map_smul] at hsplit
  have hscalar : c (Fin.last r) • Quartic.mulQuadratic (q (Fin.last r)) (q (Fin.last r)) ∈
      LinearMap.range (Quartic.quadraticMultiplication (prefixFamily q)) := by
    refine ⟨-prefixFamily b, ?_⟩
    rw [map_neg]
    exact neg_eq_iff_add_eq_zero.mpr hsplit.symm
  have hc0 : c (Fin.last r) = 0 := by
    by_contra hne
    apply hsquare
    have hin := (LinearMap.range (Quartic.quadraticMultiplication (prefixFamily q))).smul_mem
      (c (Fin.last r))⁻¹ hscalar
    simpa only [smul_smul, inv_mul_cancel₀ hne, one_smul] using hin
  have hblast0 : b (Fin.last r) = 0 := by simpa only [hc0, zero_smul] using hblast
  have hprefix : prefixFamily b ∈
      LinearMap.ker (Quartic.quadraticMultiplication (prefixFamily q)) := by
    change Quartic.quadraticMultiplication (prefixFamily q) (prefixFamily b) = 0
    simpa only [hc0, zero_smul, add_zero] using hsplit.symm
  refine ⟨⟨prefixFamily b,hprefix⟩,?_⟩
  rw [extendZero_prefixFamily b hblast0]
  have heq : a - b = -z := by dsimp [b]; abel
  rw [heq]
  exact (koszulSpace q).neg_mem hzmem

/-- Precisely the old homology is lost when the marked coefficient is read. -/
theorem marked_kernel_eq_old_range (q : Fin (r+1) → Forms K n 2)
    (hsquare : mulQuadratic (q (Fin.last r)) (q (Fin.last r)) ∉
      (quadraticMultiplication (prefixFamily q)).range) :
    (markedCoefficientMap q).ker = (homologyExtension q).range := by
  apply MarkedDefectGeneral.coefficient_kernel_range
    (quadraticMultiplication (prefixFamily q)) (quadraticMultiplication q)
    (extendZero (K := K)) (multiplication_comp_extendZero q)
    (koszulSpace (prefixFamily q)) (koszulSpace q)
    (old_boundaries_map_to_boundaries q) (LinearMap.proj (Fin.last r))
    (Submodule.span K (Set.range q)) (boundary_coefficient_mem_span q (Fin.last r))
  · intro x
    simpa only [LinearMap.proj_apply,extendZero_last] using
      (Submodule.span K (Set.range q)).zero_mem
  · intro a ha hc
    obtain ⟨b,hb⟩ := marked_kernel_old_plus_boundary q hsquare a ha hc
    exact ⟨b.val,b.property,hb⟩

/-- The rank formula includes both child defects, with no exact-child hypothesis. -/
theorem marked_rank_add_old (q : Fin (r+1) → Forms K n 2)
    (hq : LinearIndependent K q)
    (hsquare : mulQuadratic (q (Fin.last r)) (q (Fin.last r)) ∉
      (quadraticMultiplication (prefixFamily q)).range) :
    finrank K (markedCoefficientMap (K := K) q).range +
      finrank K (QuarticHomology (prefixFamily q)) = finrank K (QuarticHomology q) := by
  have he := (markedCoefficientMap (K := K) q).finrank_range_add_finrank_ker
  rw [marked_kernel_eq_old_range q hsquare,
    LinearMap.finrank_range_of_inj (homologyExtension_injective q hq)] at he
  exact he

end Quartic.MarkedDefect
