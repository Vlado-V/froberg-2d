module

public import Quartic.Homology

@[expose] public section

/-!
# The moving correction space

For a surjective map `F` and a target subspace `U`, this module constructs
`F⁻¹(U) / B`, where `B` is a boundary subspace in the kernel. It proves the
dimension identity used in `tr:Tdimension`, and the induced injection into a
coefficient quotient when the only discarded vectors in the preimage are
boundaries. All statements retain their linear-algebra hypotheses explicitly.
-/

namespace Quartic.CorrectionSpace

noncomputable section

variable {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- Boundaries viewed inside the inverse image of the moving target subspace. -/
def preimageBoundary (F : V →ₗ[K] W) (B : Submodule K V) (U : Submodule K W) :
    Submodule K (U.comap F) :=
  B.comap (U.comap F).subtype

/-- The actual quotient of the correction preimage by its boundaries. -/
abbrev Correction (F : V →ₗ[K] W) (B : Submodule K V) (U : Submodule K W) :=
  (U.comap F) ⧸ preimageBoundary F B U

/-- Multiplication restricted to the correction preimage. -/
def preimageMap (F : V →ₗ[K] W) (U : Submodule K W) : (U.comap F) →ₗ[K] U where
  toFun a := ⟨F a.val, a.property⟩
  map_add' _ _ := Subtype.ext (F.map_add _ _)
  map_smul' _ _ := Subtype.ext (F.map_smul _ _)

@[simp] theorem preimageMap_apply (F : V →ₗ[K] W) (U : Submodule K W)
    (a : U.comap F) : (preimageMap F U a).val = F a.val := rfl

theorem ker_le_preimage (F : V →ₗ[K] W) (U : Submodule K W) :
    F.ker ≤ U.comap F := by
  intro a ha
  change F a ∈ U
  rw [show F a = 0 from ha]
  exact U.zero_mem

theorem preimageMap_surjective (F : V →ₗ[K] W) (U : Submodule K W)
    (hF : Function.Surjective F) : Function.Surjective (preimageMap F U) := by
  intro u
  obtain ⟨v, hv⟩ := hF u.val
  refine ⟨⟨v, ?_⟩, Subtype.ext hv⟩
  change F v ∈ U
  simpa only [hv] using u.property

theorem preimageMap_ker (F : V →ₗ[K] W) (U : Submodule K W) :
    (preimageMap F U).ker = F.ker.comap (U.comap F).subtype := by
  ext a
  change (preimageMap F U a = 0) ↔ F a.val = 0
  exact Subtype.ext_iff

theorem boundary_le_preimageMap_ker (F : V →ₗ[K] W)
    (B : Submodule K V) (U : Submodule K W) (hB : B ≤ F.ker) :
    preimageBoundary F B U ≤ (preimageMap F U).ker := by
  rw [preimageMap_ker]
  exact Submodule.comap_mono hB

/-- The correction quotient maps to the target subspace. -/
def correctionProjection (F : V →ₗ[K] W) (B : Submodule K V) (U : Submodule K W)
    (hB : B ≤ F.ker) : Correction F B U →ₗ[K] U :=
  (preimageBoundary F B U).liftQ (preimageMap F U)
    (boundary_le_preimageMap_ker F B U hB)

@[simp] theorem correctionProjection_mk (F : V →ₗ[K] W)
    (B : Submodule K V) (U : Submodule K W) (hB : B ≤ F.ker) (a : U.comap F) :
    correctionProjection F B U hB ((preimageBoundary F B U).mkQ a) =
      preimageMap F U a := rfl

theorem correctionProjection_surjective (F : V →ₗ[K] W)
    (B : Submodule K V) (U : Submodule K W) (hB : B ≤ F.ker)
    (hF : Function.Surjective F) :
    Function.Surjective (correctionProjection F B U hB) := by
  intro u
  obtain ⟨a, ha⟩ := preimageMap_surjective F U hF u
  exact ⟨(preimageBoundary F B U).mkQ a, ha⟩

section Dimension

variable [FiniteDimensional K V]

theorem finrank_preimage (F : V →ₗ[K] W) (U : Submodule K W)
    (hF : Function.Surjective F) :
    Module.finrank K (U.comap F) = Module.finrank K F.ker + Module.finrank K U := by
  have h := (preimageMap F U).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (preimageMap_surjective F U hF),
    finrank_top, preimageMap_ker,
    (Submodule.comapSubtypeEquivOfLe (ker_le_preimage F U)).finrank_eq] at h
  omega

/-- The dimension formula for the moving correction space. -/
theorem finrank_correction (F : V →ₗ[K] W) (B : Submodule K V)
    (U : Submodule K W) (hB : B ≤ F.ker) (hF : Function.Surjective F) :
    Module.finrank K (Correction F B U) =
      Module.finrank K (Quartic.KernelModulo F B) + Module.finrank K U := by
  have hpre := (preimageBoundary F B U).finrank_quotient_add_finrank
  have hker := Quartic.finrank_kernelModulo_add F B
  have hdim := finrank_preimage F U hF
  have hbpre : Module.finrank K (preimageBoundary F B U) = Module.finrank K B :=
    (Submodule.comapSubtypeEquivOfLe (hB.trans (ker_le_preimage F U))).finrank_eq
  have hbker : Module.finrank K (Quartic.kernelBoundary F B) = Module.finrank K B :=
    (Submodule.comapSubtypeEquivOfLe hB).finrank_eq
  rw [hbpre] at hpre
  rw [hbker] at hker
  change Module.finrank K (Correction F B U) + Module.finrank K B =
    Module.finrank K (U.comap F) at hpre
  omega

end Dimension

/-- Projection to the coefficient quotient before passing to boundaries. -/
def preimageCoefficientMap (F : V →ₗ[K] W) (U : Submodule K W)
    (E : Submodule K V) : (U.comap F) →ₗ[K] V ⧸ E :=
  E.mkQ.comp (U.comap F).subtype

theorem boundary_le_coefficient_ker (F : V →ₗ[K] W) (B : Submodule K V)
    (U : Submodule K W) (E : Submodule K V) (hBE : B ≤ E) :
    preimageBoundary F B U ≤ (preimageCoefficientMap F U E).ker := by
  intro a ha
  change E.mkQ a.val = 0
  exact (Submodule.Quotient.mk_eq_zero E).mpr (hBE ha)

/-- The induced coefficient map from the correction quotient. -/
def correctionCoefficientMap (F : V →ₗ[K] W) (B : Submodule K V)
    (U : Submodule K W) (E : Submodule K V) (hBE : B ≤ E) :
    Correction F B U →ₗ[K] V ⧸ E :=
  (preimageBoundary F B U).liftQ (preimageCoefficientMap F U E)
    (boundary_le_coefficient_ker F B U E hBE)

@[simp] theorem correctionCoefficientMap_mk (F : V →ₗ[K] W) (B : Submodule K V)
    (U : Submodule K W) (E : Submodule K V) (hBE : B ≤ E) (a : U.comap F) :
    correctionCoefficientMap F B U E hBE ((preimageBoundary F B U).mkQ a) =
      E.mkQ a.val := rfl

/-- Only boundaries are lost in the coefficient quotient, so the induced map
is injective. This is the abstract projection argument following `tr:Tdimension`. -/
theorem correctionCoefficientMap_injective (F : V →ₗ[K] W) (B : Submodule K V)
    (U : Submodule K W) (E : Submodule K V) (hBE : B ≤ E)
    (hinter : E ⊓ U.comap F = B) :
    Function.Injective (correctionCoefficientMap F B U E hBE) := by
  apply LinearMap.ker_eq_bot.mp
  apply Submodule.ker_liftQ_eq_bot
  intro a ha
  change a.val ∈ B
  rw [← hinter]
  refine ⟨?_, a.property⟩
  change E.mkQ a.val = 0 at ha
  exact (Submodule.Quotient.mk_eq_zero E).mp ha

/-- Disjoint product images and exactness on the discarded coefficient space
supply the required intersection identity. -/
theorem intersection_eq_boundaries (F : V →ₗ[K] W) (B : Submodule K V)
    (U : Submodule K W) (E : Submodule K V)
    (hdisjoint : Disjoint (E.map F) U) (hker : E ⊓ F.ker = B) :
    E ⊓ U.comap F = B := by
  rw [← hker]
  apply le_antisymm
  · intro a ha
    refine ⟨ha.1, ?_⟩
    change F a = 0
    exact (Submodule.disjoint_def.mp hdisjoint) (F a) ⟨a, ha.1, rfl⟩ ha.2
  · exact inf_le_inf_left E (ker_le_preimage F U)

/-- The correction space injects into the coefficient quotient under the
product-disjointness and discarded-space exactness hypotheses. -/
theorem correctionCoefficientMap_injective_of_disjoint (F : V →ₗ[K] W)
    (B : Submodule K V) (U : Submodule K W) (E : Submodule K V)
    (hBE : B ≤ E) (hdisjoint : Disjoint (E.map F) U) (hker : E ⊓ F.ker = B) :
    Function.Injective (correctionCoefficientMap F B U E hBE) :=
  correctionCoefficientMap_injective F B U E hBE
    (intersection_eq_boundaries F B U E hdisjoint hker)

end

end Quartic.CorrectionSpace
