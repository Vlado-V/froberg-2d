/-
Copyright (c) 2026 Vlado Vojdanovski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vlado Vojdanovski
-/
module

public import Quartic.MarkedDefect

/-!
# Reading the marked coefficient before quotienting by the marked generator

Reading modulo the old generators, rather than all generators, identifies the
kernel with the old homology in every characteristic. It requires no surviving
square and retains the one coefficient direction discarded by the usual reader.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000

namespace Quartic.RefinedMarkedCoefficient

open Module EndpointHomology MarkedCoefficient

variable {K : Type*} [Field K] {n r : ℕ}

/-- The last coefficient of a Koszul boundary belongs to the old generator span. -/
theorem boundary_coefficient_mem_old_span (q : Fin (r + 1) → Forms K n 2) :
    boundarySpan (K := K) q ≤
      (Submodule.span K (Set.range (prefixFamily q))).comap (LinearMap.proj (Fin.last r)) := by
  classical
  apply Submodule.span_le.mpr
  rintro _ ⟨p, rfl⟩
  change koszulVector q p (Fin.last r) ∈ Submodule.span K (Set.range (prefixFamily q))
  have hi : p.val.1.val < r := by
    have hp := p.property
    have hj := p.val.2.isLt
    omega
  have hne : Fin.last r ≠ p.val.1 := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_last] at hv
    omega
  unfold koszulVector
  simp only [hne, ↓reduceIte, zero_sub]
  apply Submodule.neg_mem
  split_ifs with h
  · apply Submodule.subset_span
    refine ⟨⟨p.val.1.val, hi⟩, ?_⟩
    change q _ = q _
    congr 1
  · exact Submodule.zero_mem _

/-- Reducing a cycle whose last coefficient is old uses only cross boundaries. -/
theorem reduce_cycle (q : Fin (r + 1) → Forms K n 2)
    (a : Fin (r + 1) → Forms K n 2)
    (ha : quadraticMultiplication q a = 0)
    (hc : a (Fin.last r) ∈ Submodule.span K (Set.range (prefixFamily q))) :
    ∃ b : (quadraticMultiplication (prefixFamily q)).ker,
      a - extendZero (K := K) b.val ∈ koszulSpace q := by
  classical
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hc
  let z := crossBoundary q c
  have hzmem : z ∈ koszulSpace q := crossBoundary_mem q c
  have hzcycle : quadraticMultiplication q z = 0 := kernel_contains_koszul q hzmem
  let b := a + z
  have hbcycle : quadraticMultiplication q b = 0 := by
    simp only [b, map_add, ha, hzcycle, zero_add]
  have hblast : b (Fin.last r) = 0 := by
    change a (Fin.last r) + crossBoundary q c (Fin.last r) = 0
    rw [crossBoundary_last, ← hc]
    simp only [prefixFamily, add_neg_cancel]
  have hsplit := quadraticMultiplication_split_last q b
  rw [hbcycle, hblast, map_zero, add_zero] at hsplit
  refine ⟨⟨prefixFamily b, hsplit.symm⟩, ?_⟩
  rw [extendZero_prefixFamily b hblast]
  have heq : a - b = -z := by dsimp [b]; abel
  rw [heq]
  exact (koszulSpace q).neg_mem hzmem

/-- The refined reader takes values modulo the old, rather than full, span. -/
def reader (q : Fin (r + 1) → Forms K n 2) :
    QuarticHomology q →ₗ[K] (Forms K n 2 ⧸ Submodule.span K (Set.range (prefixFamily q))) :=
  quotientCoefficient (quadraticMultiplication q) (LinearMap.proj (Fin.last r))
    (koszulSpace q) (Submodule.span K (Set.range (prefixFamily q)))
    (boundary_coefficient_mem_old_span q)

/-- Its kernel is exactly old homology, even when the marked square vanishes. -/
theorem kernel_eq_old_range (q : Fin (r + 1) → Forms K n 2) :
    (reader q).ker = (homologyExtension q).range := by
  apply MarkedDefectGeneral.coefficient_kernel_range
    (quadraticMultiplication (prefixFamily q)) (quadraticMultiplication q)
    (extendZero (K := K)) (multiplication_comp_extendZero q)
    (koszulSpace (prefixFamily q)) (koszulSpace q)
    (old_boundaries_map_to_boundaries q) (LinearMap.proj (Fin.last r))
    (Submodule.span K (Set.range (prefixFamily q))) (boundary_coefficient_mem_old_span q)
  · intro x
    simpa only [LinearMap.proj_apply, extendZero_last] using
      (Submodule.span K (Set.range (prefixFamily q))).zero_mem
  · intro a ha hc
    obtain ⟨b, hb⟩ := reduce_cycle q a ha hc
    exact ⟨b.val, b.property, hb⟩

/-- The rank formula now has no hypothesis about the characteristic or squares. -/
theorem rank_add_old (q : Fin (r + 1) → Forms K n 2)
    (hq : LinearIndependent K q) :
    finrank K (reader q).range + finrank K (QuarticHomology (prefixFamily q)) =
      finrank K (QuarticHomology q) := by
  have he := (reader q).finrank_range_add_finrank_ker
  rw [kernel_eq_old_range q,
    LinearMap.finrank_range_of_inj (homologyExtension_injective q hq)] at he
  exact he

private theorem rank_le_comp_rank_add_kernel
    {V W U : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    [AddCommGroup U] [Module K U] (f : V →ₗ[K] W) (g : W →ₗ[K] U) :
    finrank K f.range ≤ finrank K (g.comp f).range + finrank K g.ker := by
  let restricted := g.domRestrict f.range
  let inclusion : restricted.ker →ₗ[K] g.ker :=
    { toFun := fun x => ⟨x.val.val, x.property⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective inclusion := by
    intro a b h
    have he : a.val.val = b.val.val := congrArg (fun x : g.ker => x.val) h
    apply Subtype.ext
    apply Subtype.ext
    exact he
  have hk := LinearMap.finrank_le_finrank_of_injective hinj
  have hn := restricted.finrank_range_add_finrank_ker
  have hr : restricted.range = (g.comp f).range := by
    change (g.comp f.range.subtype).range = _
    rw [LinearMap.range_comp, Submodule.range_subtype, LinearMap.range_comp]
  rw [hr] at hn
  omega

theorem old_span_le_full_span (q : Fin (r + 1) → Forms K n 2) :
    Submodule.span K (Set.range (prefixFamily q)) ≤ Submodule.span K (Set.range q) := by
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  exact ⟨i.castSucc, rfl⟩

/-- The quotient map that forgets the one marked-generator direction. -/
def forget (q : Fin (r + 1) → Forms K n 2) :
    (Forms K n 2 ⧸ Submodule.span K (Set.range (prefixFamily q))) →ₗ[K]
      (Forms K n 2 ⧸ Submodule.span K (Set.range q)) :=
  Submodule.factor (old_span_le_full_span q)

private theorem coefficient_factor
    {V W U : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [AddCommGroup U] [Module K U]
    (f : V →ₗ[K] W) (e : V →ₗ[K] U) (B : Submodule K V)
    (C D : Submodule K U) (hC : B ≤ C.comap e) (hCD : C ≤ D)
    (hD : B ≤ D.comap e) :
    (Submodule.factor hCD).comp (quotientCoefficient f e B C hC) =
      quotientCoefficient f e B D hD := by
  apply LinearMap.ext
  intro x
  obtain ⟨a, rfl⟩ := (kernelBoundary f B).mkQ_surjective x
  simp only [LinearMap.comp_apply, quotientCoefficient_mk, Submodule.factor_mk]

/-- Forgetting the marked coefficient direction recovers the usual reader. -/
theorem factor_reader (q : Fin (r + 1) → Forms K n 2) :
    (forget q).comp (reader q) =
      markedCoefficientMap q := by
  unfold forget reader markedCoefficientMap
  exact coefficient_factor (quadraticMultiplication q) (LinearMap.proj (Fin.last r))
    (koszulSpace q) _ _ (boundary_coefficient_mem_old_span q) (old_span_le_full_span q)
    (boundary_coefficient_mem_span q (Fin.last r))

/-- Exactly one coefficient direction is forgotten when the marked generator is added. -/
theorem factor_kernel_finrank (q : Fin (r + 1) → Forms K n 2)
    (hq : LinearIndependent K q) :
    finrank K (forget q).ker = 1 := by
  have hfull : finrank K (Submodule.span K (Set.range q)) = r + 1 := by
    rw [finrank_span_eq_card hq, Fintype.card_fin]
  have hold : finrank K (Submodule.span K (Set.range (prefixFamily q))) = r := by
    have hpre : LinearIndependent K (prefixFamily q) := hq.comp _ (Fin.castSucc_injective r)
    rw [finrank_span_eq_card hpre, Fintype.card_fin]
  have hn := (forget q).finrank_range_add_finrank_ker
  have hs : Function.Surjective (forget q) :=
    Submodule.factor_surjective (old_span_le_full_span q)
  rw [LinearMap.range_eq_top.mpr hs, finrank_top] at hn
  have ho := (Submodule.span K (Set.range (prefixFamily q))).finrank_quotient_add_finrank
  have hf := (Submodule.span K (Set.range q)).finrank_quotient_add_finrank
  rw [hold] at ho
  rw [hfull] at hf
  omega

/-- Without a surviving square, the usual reader loses at most one additional dimension. -/
theorem ordinary_kernel_le_old_add_one (q : Fin (r + 1) → Forms K n 2)
    (hq : LinearIndependent K q) :
    finrank K (markedCoefficientMap q).ker ≤
      finrank K (QuarticHomology (prefixFamily q)) + 1 := by
  have h := rank_le_comp_rank_add_kernel (reader q)
    (forget q)
  rw [factor_reader, factor_kernel_finrank q hq] at h
  have hr := rank_add_old q hq
  have hn := (markedCoefficientMap q).finrank_range_add_finrank_ker
  change finrank K (markedCoefficientMap q).range + finrank K (markedCoefficientMap q).ker =
    finrank K (QuarticHomology q) at hn
  change finrank K (reader q).range ≤ finrank K (markedCoefficientMap q).range + 1 at h
  omega

/-- Old homology remains in the kernel of the ordinary coefficient reader. -/
theorem old_range_le_ordinary_kernel (q : Fin (r + 1) → Forms K n 2) :
    (homologyExtension q).range ≤ (markedCoefficientMap q).ker := by
  intro x hx
  rw [← kernel_eq_old_range q] at hx
  change reader q x = 0 at hx
  change markedCoefficientMap q x = 0
  have he := LinearMap.congr_fun (factor_reader q) x
  simpa only [LinearMap.comp_apply, hx, map_zero] using he.symm

theorem old_le_ordinary_kernel (q : Fin (r + 1) → Forms K n 2)
    (hq : LinearIndependent K q) :
    finrank K (QuarticHomology (prefixFamily q)) ≤ finrank K (markedCoefficientMap q).ker := by
  have h := Submodule.finrank_mono (old_range_le_ordinary_kernel q)
  rw [LinearMap.finrank_range_of_inj (homologyExtension_injective q hq)] at h
  exact h

end Quartic.RefinedMarkedCoefficient
