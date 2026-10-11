/-
Copyright (c) 2026 Vlado Vojdanovski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vlado Vojdanovski
-/
module

public import Quartic.CorrectionSpace
public import Quartic.SplitBlock22MiddleHomology
public import Quartic.ExtendedAugmentedGeneric
public import Quartic.MovingMiddleCorrectionOmega
public import Mathlib.LinearAlgebra.Quotient.Pi

/-!
# Extended moving middle correction coefficients

This proves the coefficient injection and dimension identity from `tr:Tdimension`
for the actual middle multiplication map. The discarded coefficient space is
`(span g)^c`; its product image is the actual symmetric-product range and its
kernel consists exactly of mixed Koszul boundaries. Actual parameterized augmented
injectivity makes pure and marked traces independent and disjoint from those
products, so the correction quotient injects into `(Mixed / span g)^c`.

The marked motion is the direction `ωu-v`. The marked coefficient subspace
of the child quadratic quotient is explicit. Identifying its dimension with
the old-child defect is a separate input, not an assumption hidden in the
coefficient injection.
-/

@[expose] public section

noncomputable section
namespace Quartic.ExtendedMovingCorrection
open Module HomologyCoordinates AugmentedMiddle AugmentedGeneric
open ExtendedAugmentedGeneric MovingMiddleCorrectionOmega

variable {K : Type*} [Field K]
variable (ω : K)

section Traces
variable {S A : Type*} [AddCommGroup S] [Module K S]
  [AddCommGroup A] [Module K A]

set_option maxHeartbeats 2000000 in -- Preserve the budget during this port.
def traceMap (r : Fin 4 → A) (U : Submodule K A) :
    (U × (Fin 4 → K)) →ₗ[K] A × A :=
  ((ω • U.subtype).prod (-U.subtype)).coprod (ExtendedPureTrace.trace ω r)

set_option maxHeartbeats 2000000 in -- Preserve the budget during this port.
@[simp] theorem traceMap_apply (r : Fin 4 → A) (U : Submodule K A)
    (a : U) (ξ : (Fin 4 → K)) :
    traceMap ω r U (a,ξ) = (ω • a.val + (ExtendedPureTrace.trace ω r ξ).1, -a.val + (ExtendedPureTrace.trace ω r ξ).2) := rfl

set_option maxHeartbeats 2000000 in -- Preserve the budget during this port.
theorem augmented_decomposition (F : S →ₗ[K] A × A) (r : Fin 4 → A)
    (U : Submodule K A) (b : S) (a : U) (ξ : (Fin 4 → K)) :
    augmented ω F r (b,a.val,ξ) = F b + traceMap ω r U (a,ξ) := by
  apply Prod.ext <;> simp [ExtendedAugmentedGeneric.augmented_apply, sub_eq_add_neg, add_assoc]

set_option maxHeartbeats 2000000 in -- Preserve the budget during this port.
theorem product_injective (F : S →ₗ[K] A × A) (r : Fin 4 → A)
    (ha : Function.Injective (augmented ω F r)) : Function.Injective F := by
  intro b b' h
  have he : augmented ω F r (b,0,0) = augmented ω F r (b',0,0) := by
    simp only [ExtendedAugmentedGeneric.augmented_apply, smul_zero, map_zero, Prod.fst_zero,
      Prod.snd_zero, add_zero, sub_zero]
    exact Prod.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
  exact congrArg Prod.fst (ha he)

set_option maxHeartbeats 2000000 in -- Preserve the budget during this port.
theorem traceMap_injective (F : S →ₗ[K] A × A) (r : Fin 4 → A)
    (ha : Function.Injective (augmented ω F r)) (U : Submodule K A) :
    Function.Injective (traceMap ω r U) := by
  rintro ⟨a,ξ⟩ ⟨b,η⟩ h
  have he : augmented ω F r (0,a.val,ξ) = augmented ω F r (0,b.val,η) := by
    rw [augmented_decomposition ω F r U, augmented_decomposition ω F r U, h]
  have hz := congrArg Prod.snd (ha he)
  apply Prod.ext
  · exact Subtype.ext (congrArg Prod.fst hz)
  · exact congrArg (fun p : A × (Fin 4 → K) => p.2) hz

set_option maxHeartbeats 2000000 in -- Preserve the budget during this port.
theorem product_disjoint_trace (F : S →ₗ[K] A × A) (r : Fin 4 → A)
    (ha : Function.Injective (augmented ω F r)) (U : Submodule K A) :
    Disjoint F.range (traceMap ω r U).range := by
  apply Submodule.disjoint_def.mpr
  rintro z ⟨b,hb⟩ ⟨⟨a,ξ⟩,ht⟩
  have he : augmented ω F r (b,0,0) = augmented ω F r (0,a.val,ξ) := by
    rw [augmented_decomposition ω F r U]
    simpa only [ExtendedAugmentedGeneric.augmented_apply, map_zero, smul_zero, Prod.fst_zero,
      Prod.snd_zero,
      add_zero, sub_zero, zero_add, Prod.mk.eta] using hb.trans ht.symm
  have hb0 : b = 0 := congrArg Prod.fst (ha he)
  simpa only [hb0, map_zero] using hb.symm

set_option maxHeartbeats 2000000 in -- Preserve the budget during this port.
theorem traceMap_finrank [FiniteDimensional K A]
    (F : S →ₗ[K] A × A) (r : Fin 4 → A)
    (ha : Function.Injective (augmented ω F r)) (U : Submodule K A) :
    finrank K (traceMap ω r U).range = finrank K U + 4 := by
  rw [LinearMap.finrank_range_of_inj (traceMap_injective ω F r ha U), Module.finrank_prod]
  congr 1
  simp
end Traces

section Actual
variable {m c q : ℕ}

set_option maxHeartbeats 2000000 in -- Preserve the budget during this port.
/-- The actual marked and pure trace subspace, with the marked child subspace explicit. -/
def traceSpace (h : Fin q → Forms K m 2) (r : Fin 4 → Forms K m 2)
    (markedU : Submodule K (Forms K m 2 ⧸ Submodule.span K (Set.range h))) :
    Submodule K ((Forms K m 2 ⧸ Submodule.span K (Set.range h)) ×
      (Forms K m 2 ⧸ Submodule.span K (Set.range h))) :=
  (traceMap ω (fun i => (Submodule.span K (Set.range h)).mkQ (r i)) markedU).range

set_option maxHeartbeats 2000000 in -- Preserve the budget during this port.
/-- No quotient-rank assumption: the actual parameterized augmented map supplies trace
independence. -/
theorem traceSpace_finrank (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (r : Fin 4 → Forms K m 2)
    (ha : Function.Injective (quotientAugmented ω (productMap g) h r))
    (markedU : Submodule K (Forms K m 2 ⧸ Submodule.span K (Set.range h))) :
    finrank K (traceSpace ω h r markedU) = finrank K markedU + 4 :=
  traceMap_finrank ω (quotientProduct g _) _ ha markedU

set_option maxHeartbeats 2000000 in -- Preserve the budget during this port.
theorem discarded_image_disjoint_trace (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (r : Fin 4 → Forms K m 2)
    (ha : Function.Injective (quotientAugmented ω (productMap g) h r))
    (markedU : Submodule K (Forms K m 2 ⧸ Submodule.span K (Set.range h))) :
    Disjoint ((discarded g).map (MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h))))
      (traceSpace ω h r markedU) := by
  rw [discarded_quotient_image]
  exact product_disjoint_trace ω (quotientProduct g _) _ ha markedU

set_option maxHeartbeats 2000000 in -- Preserve the budget during this port.
/-- The only correction coefficients discarded modulo the mixed generators are boundaries. -/
theorem discarded_inter_correction (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (r : Fin 4 → Forms K m 2)
    (hg : LinearIndependent K g)
    (ha : Function.Injective (quotientAugmented ω (productMap g) h r))
    (markedU : Submodule K (Forms K m 2 ⧸ Submodule.span K (Set.range h))) :
    discarded g ⊓ (traceSpace ω h r markedU).comap
      (MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h))) =
        SplitBlock22.mixedKoszulSpace g :=
  CorrectionSpace.intersection_eq_boundaries _ _ _ _
    (discarded_image_disjoint_trace ω g h r ha markedU)
    (discarded_inter_kernel g _ hg (product_injective ω (quotientProduct g _) _ ha))

set_option maxHeartbeats 2000000 in -- Preserve the budget during this port.
/-- The actual correction space, modulo the actual alternating mixed boundaries. -/
abbrev Correction (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (r : Fin 4 → Forms K m 2)
    (markedU : Submodule K (Forms K m 2 ⧸ Submodule.span K (Set.range h))) :=
  CorrectionSpace.Correction
    (MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h)))
    (SplitBlock22.mixedKoszulSpace g) (traceSpace ω h r markedU)

set_option maxHeartbeats 2000000 in -- Preserve the budget during this port.
/-- Coordinatewise coefficient reduction modulo the actual mixed generator space. -/
def coefficientProjection (g : Fin c → MiddleCoordinates.Mixed K m) :
    (Fin c → MiddleCoordinates.Mixed K m) →ₗ[K]
      (Fin c → MiddleCoordinates.Mixed K m ⧸ Submodule.span K (Set.range g)) where
  toFun a i := (Submodule.span K (Set.range g)).mkQ (a i)
  map_add' a b := by ext i; exact map_add _ _ _
  map_smul' s a := by
    ext i
    exact (Submodule.span K (Set.range g)).mkQ.map_smul s (a i)

set_option maxHeartbeats 2000000 in -- Preserve the budget during this port.
@[simp] theorem coefficientProjection_apply (g : Fin c → MiddleCoordinates.Mixed K m)
    (a : Fin c → MiddleCoordinates.Mixed K m) (i : Fin c) :
    coefficientProjection g a i = (Submodule.span K (Set.range g)).mkQ (a i) := rfl

set_option maxHeartbeats 2000000 in -- Preserve the budget during this port.
def coefficientQuotientEquiv (g : Fin c → MiddleCoordinates.Mixed K m) :
    ((Fin c → MiddleCoordinates.Mixed K m) ⧸ discarded g) ≃ₗ[K]
      (Fin c → MiddleCoordinates.Mixed K m ⧸ Submodule.span K (Set.range g)) :=
  Submodule.quotientPi (fun _ : Fin c => Submodule.span K (Set.range g))

set_option maxHeartbeats 2000000 in -- Preserve the budget during this port.
@[simp] theorem coefficientQuotientEquiv_mk (g : Fin c → MiddleCoordinates.Mixed K m)
    (a : Fin c → MiddleCoordinates.Mixed K m) :
    coefficientQuotientEquiv g ((discarded g).mkQ a) = coefficientProjection g a := rfl

set_option maxHeartbeats 2000000 in -- Preserve the budget during this port.
/-- Actual coefficient map on the correction quotient. -/
def coefficientMap (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (r : Fin 4 → Forms K m 2)
    (markedU : Submodule K (Forms K m 2 ⧸ Submodule.span K (Set.range h))) :
    Correction ω g h r markedU →ₗ[K]
      (Fin c → MiddleCoordinates.Mixed K m ⧸ Submodule.span K (Set.range g)) :=
  (coefficientQuotientEquiv g).toLinearMap.comp
    (CorrectionSpace.correctionCoefficientMap _ _ _ _ (boundary_le_discarded g))

set_option maxHeartbeats 2000000 in -- Preserve the budget during this port.
@[simp] theorem coefficientMap_mk (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (r : Fin 4 → Forms K m 2)
    (markedU : Submodule K (Forms K m 2 ⧸ Submodule.span K (Set.range h)))
    (a : (traceSpace ω h r markedU).comap
      (MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h)))) :
    coefficientMap ω g h r markedU (Submodule.Quotient.mk a) = coefficientProjection g a.val := rfl

set_option maxHeartbeats 2000000 in -- Preserve the budget during this port.
/-- Actual coefficient injection, derived from parameterized augmented injectivity. -/
theorem coefficientMap_injective (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (r : Fin 4 → Forms K m 2)
    (hg : LinearIndependent K g)
    (ha : Function.Injective (quotientAugmented ω (productMap g) h r))
    (markedU : Submodule K (Forms K m 2 ⧸ Submodule.span K (Set.range h))) :
    Function.Injective (coefficientMap ω g h r markedU) :=
  (coefficientQuotientEquiv g).injective.comp
    (CorrectionSpace.correctionCoefficientMap_injective _ _ _ _
      (boundary_le_discarded g) (discarded_inter_correction ω g h r hg ha markedU))

set_option maxHeartbeats 2000000 in -- Preserve the budget during this port.
/-- The actual projected coefficient image, defined before quotienting any boundaries. -/
def coefficientImage (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (r : Fin 4 → Forms K m 2)
    (markedU : Submodule K (Forms K m 2 ⧸ Submodule.span K (Set.range h))) :
    Submodule K (Fin c → MiddleCoordinates.Mixed K m ⧸ Submodule.span K (Set.range g)) :=
  ((traceSpace ω h r markedU).comap
    (MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h)))).map (coefficientProjection
      g)

set_option maxHeartbeats 2000000 in -- Preserve the budget during this port.
theorem coefficientImage_eq_range (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (r : Fin 4 → Forms K m 2)
    (markedU : Submodule K (Forms K m 2 ⧸ Submodule.span K (Set.range h))) :
    coefficientImage ω g h r markedU = (coefficientMap ω g h r markedU).range := by
  apply le_antisymm
  · rintro z ⟨a, ha, rfl⟩
    exact ⟨Submodule.Quotient.mk ⟨a, ha⟩, coefficientMap_mk ω g h r markedU ⟨a, ha⟩⟩
  · rintro z ⟨a, rfl⟩
    refine Submodule.Quotient.induction_on _ a ?_
    intro a
    exact ⟨a.val, a.property, (coefficientMap_mk ω g h r markedU a).symm⟩

set_option maxHeartbeats 2000000 in -- Preserve the budget during this port.
/-- Dimension of the actual correction space, with the marked coefficient dimension explicit. -/
theorem correction_finrank (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (r : Fin 4 → Forms K m 2)
    (ha : Function.Injective (quotientAugmented ω (productMap g) h r))
    (hs : Function.Surjective
      (MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h))))
    (markedU : Submodule K (Forms K m 2 ⧸ Submodule.span K (Set.range h))) :
    finrank K (Correction ω g h r markedU) =
      finrank K (SplitBlock22.MiddleHomology g h) + 4 + finrank K markedU := by
  rw [CorrectionSpace.finrank_correction _ _ _
    (SplitBlock22.mixedKoszulSpace_le_quotient_kernel g _) hs]
  rw [traceSpace_finrank ω g h r ha markedU]
  change finrank K (SplitBlock22.MiddleHomology g h) + (finrank K markedU + 4) = _
  omega

set_option maxHeartbeats 2000000 in -- Preserve the budget during this port.
/-- The actual coordinate-quotient coefficient image has the required transfer dimension. -/
theorem coefficientImage_finrank (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (r : Fin 4 → Forms K m 2)
    (hg : LinearIndependent K g) (hh : LinearIndependent K h)
    (ha : Function.Injective (quotientAugmented ω (productMap g) h r))
    (hs : Function.Surjective
      (MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h))))
    (markedU : Submodule K (Forms K m 2 ⧸ Submodule.span K (Set.range h))) :
    (finrank K (coefficientImage ω g h r markedU) : ℤ) =
      Counts.H m q c + 4 + finrank K markedU := by
  rw [coefficientImage_eq_range,
    LinearMap.finrank_range_of_inj (coefficientMap_injective ω g h r hg ha markedU),
    correction_finrank ω g h r ha hs markedU,
    ← (SplitBlock22.homologyEquiv g h hh).finrank_eq]
  push_cast
  rw [SplitBlock22.homology_finrank_eq_H g h hg hh hs]

set_option maxHeartbeats 2000000 in -- Preserve the budget during this port.
/-- Numerical form after separately identifying the marked child coefficient dimension. -/
theorem coefficientImage_finrank_of_marked (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (r : Fin 4 → Forms K m 2)
    (hg : LinearIndependent K g) (hh : LinearIndependent K h)
    (ha : Function.Injective (quotientAugmented ω (productMap g) h r))
    (hs : Function.Surjective
      (MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h))))
    (markedU : Submodule K (Forms K m 2 ⧸ Submodule.span K (Set.range h)))
    (δ : ℕ) (hmarked : finrank K markedU = δ) :
    (finrank K (coefficientImage ω g h r markedU) : ℤ) = Counts.H m q c + 4 + δ := by
  rw [coefficientImage_finrank ω g h r hg hh ha hs markedU, hmarked]

end Actual
end Quartic.ExtendedMovingCorrection
