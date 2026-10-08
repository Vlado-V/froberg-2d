import Quartic.EndpointHomology
import Quartic.Squares

/-!
# Injection from quartic homology through a marked coefficient

This is the algebraic marked-generator argument in `transfer.tex`. The old
family is exact in degree four, and the square of the new generator survives
the old quartic quotient. Reading the new coefficient modulo all generators
then gives an injective linear map on the actual first Koszul homology.
-/

namespace Quartic.MarkedCoefficient

noncomputable section

open Quartic.EndpointHomology

section GeneralQuotient

variable {K V U W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup U] [Module K U]
  [AddCommGroup W] [Module K W]

abbrev CoefficientQuotient (C : Submodule K U) := U ⧸ C

def coefficientOnCycles (f : V →ₗ[K] W) (e : V →ₗ[K] U) (C : Submodule K U) :
    f.ker →ₗ[K] CoefficientQuotient C :=
  C.mkQ.comp (e.comp f.ker.subtype)

theorem boundaries_in_coefficient_kernel (f : V →ₗ[K] W) (e : V →ₗ[K] U)
    (B : Submodule K V) (C : Submodule K U) (hB : B ≤ C.comap e) :
    Quartic.kernelBoundary f B ≤ LinearMap.ker (coefficientOnCycles f e C) := by
  intro a ha
  change C.mkQ (e a.val) = 0
  exact (Submodule.Quotient.mk_eq_zero C).mpr (hB ha)

def quotientCoefficient (f : V →ₗ[K] W) (e : V →ₗ[K] U)
    (B : Submodule K V) (C : Submodule K U) (hB : B ≤ C.comap e) :
    Quartic.KernelModulo f B →ₗ[K] CoefficientQuotient C :=
  (Quartic.kernelBoundary f B).liftQ (coefficientOnCycles f e C)
    (boundaries_in_coefficient_kernel f e B C hB)

@[simp] theorem quotientCoefficient_mk (f : V →ₗ[K] W) (e : V →ₗ[K] U)
    (B : Submodule K V) (C : Submodule K U) (hB : B ≤ C.comap e) (a : f.ker) :
    quotientCoefficient f e B C hB ((Quartic.kernelBoundary f B).mkQ a) =
      C.mkQ (e a.val) := rfl

theorem quotientCoefficient_injective (f : V →ₗ[K] W) (e : V →ₗ[K] U)
    (B : Submodule K V) (C : Submodule K U) (hB : B ≤ C.comap e)
    (hker : ∀ a, f a = 0 → e a ∈ C → a ∈ B) :
    Function.Injective (quotientCoefficient f e B C hB) := by
  apply LinearMap.ker_eq_bot.mp
  apply Submodule.ker_liftQ_eq_bot
  intro a ha
  change a.val ∈ B
  apply hker a.val a.property
  change C.mkQ (e a.val) = 0 at ha
  exact (Submodule.Quotient.mk_eq_zero C).mp ha

end GeneralQuotient

section Coordinates

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {r : ℕ}

theorem boundary_coefficient_mem_span (q : Fin r → V) (i : Fin r) :
    boundarySpan (K := K) q ≤
      (Submodule.span K (Set.range q)).comap (LinearMap.proj i) := by
  classical
  apply Submodule.span_le.mpr
  rintro _ ⟨p, rfl⟩
  change Quartic.koszulVector q p i ∈ Submodule.span K (Set.range q)
  unfold Quartic.koszulVector
  apply Submodule.sub_mem
  · split_ifs
    · exact Submodule.subset_span ⟨p.val.2, rfl⟩
    · exact Submodule.zero_mem _
  · split_ifs
    · exact Submodule.subset_span ⟨p.val.1, rfl⟩
    · exact Submodule.zero_mem _

def markedPair (i : Fin r) : Quartic.GeneratorPair (r + 1) :=
  ⟨(i.castSucc, Fin.last r), Fin.castSucc_lt_last i⟩

/-- A linear combination of boundaries involving the marked last generator. -/
def crossBoundary (q : Fin (r + 1) → V) (c : Fin r → K) : Fin (r + 1) → V :=
  ∑ i, c i • Quartic.koszulVector q (markedPair i)

theorem crossBoundary_mem (q : Fin (r + 1) → V) (c : Fin r → K) :
    crossBoundary q c ∈ boundarySpan (K := K) q := by
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨markedPair i, rfl⟩

theorem crossBoundary_last (q : Fin (r + 1) → V) (c : Fin r → K) :
    crossBoundary q c (Fin.last r) = -(∑ i, c i • q i.castSucc) := by
  simp [crossBoundary, Quartic.koszulVector, markedPair, Finset.sum_neg_distrib]

end Coordinates

section Marked

variable {K : Type*} [Field K] {n r : ℕ}

theorem quadraticMultiplication_split_last (q : Fin (r + 1) → Quartic.Forms K n 2)
    (a : Fin (r + 1) → Quartic.Forms K n 2) :
    Quartic.quadraticMultiplication q a =
      Quartic.quadraticMultiplication (prefixFamily q) (prefixFamily a) +
      Quartic.mulQuadratic (q (Fin.last r)) (a (Fin.last r)) := by
  simp [Quartic.quadraticMultiplication, Fin.sum_univ_castSucc, prefixFamily]

/-- A cycle whose last coefficient vanishes modulo all generators is a boundary,
provided the old complex is exact and the new square survives the old image. -/
theorem marked_kernel_is_boundary (q : Fin (r + 1) → Quartic.Forms K n 2)
    (hold : LinearMap.ker (Quartic.quadraticMultiplication (prefixFamily q)) ≤
      Quartic.koszulSpace (prefixFamily q))
    (hsquare : Quartic.mulQuadratic (q (Fin.last r)) (q (Fin.last r)) ∉
      LinearMap.range (Quartic.quadraticMultiplication (prefixFamily q)))
    (a : Fin (r + 1) → Quartic.Forms K n 2)
    (ha : Quartic.quadraticMultiplication q a = 0)
    (hcoeff : a (Fin.last r) ∈ Submodule.span K (Set.range q)) :
    a ∈ Quartic.koszulSpace q := by
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
  have hbmem : b ∈ Quartic.koszulSpace q := by
    have h := extendZero_mem_boundarySpan q (hold hprefix)
    rwa [extendZero_prefixFamily b hblast0] at h
  have h := (Quartic.koszulSpace q).sub_mem hbmem hzmem
  simpa only [b, add_sub_cancel_right] using h

/-- Reading the last quadratic coefficient modulo the full generator space. -/
def markedCoefficientMap (q : Fin (r + 1) → Quartic.Forms K n 2) :=
  quotientCoefficient (Quartic.quadraticMultiplication q) (LinearMap.proj (Fin.last r))
    (Quartic.koszulSpace q) (Submodule.span K (Set.range q))
    (boundary_coefficient_mem_span q (Fin.last r))

theorem markedCoefficientMap_injective (q : Fin (r + 1) → Quartic.Forms K n 2)
    (hold : LinearMap.ker (Quartic.quadraticMultiplication (prefixFamily q)) ≤
      Quartic.koszulSpace (prefixFamily q))
    (hsquare : Quartic.mulQuadratic (q (Fin.last r)) (q (Fin.last r)) ∉
      LinearMap.range (Quartic.quadraticMultiplication (prefixFamily q))) :
    Function.Injective (markedCoefficientMap q) := by
  apply quotientCoefficient_injective
  intro a ha hc
  exact marked_kernel_is_boundary q hold hsquare a ha hc

/-- The same injection with the surviving-square hypothesis stated in the
intrinsic old quartic product subspace, as in the manuscript. -/
theorem markedCoefficientMap_injective_of_square_survives
    (q : Fin (r + 1) → Quartic.Forms K n 2)
    (hold : LinearMap.ker (Quartic.quadraticMultiplication (prefixFamily q)) ≤
      Quartic.koszulSpace (prefixFamily q))
    (hsquare : Quartic.mulQuadratic (q (Fin.last r)) (q (Fin.last r)) ∉
      Quartic.quarticProducts K n (Submodule.span K
        (Set.range (fun i => ((prefixFamily q) i).val)))) :
    Function.Injective (markedCoefficientMap q) := by
  apply markedCoefficientMap_injective q hold
  rwa [Quartic.range_quadraticMultiplication]

end Marked

end

end Quartic.MarkedCoefficient
