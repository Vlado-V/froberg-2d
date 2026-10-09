module

public import Quartic.ExtraTraceOmega
public import Quartic.MarkedSquareGenericOmega

@[expose] public section

/-! The actual middle correction space with one retained target column.
This is the coefficient injection and dimension calculation for D.13. -/
noncomputable section
namespace Quartic.ExtraCorrectionOmega
open Module HomologyCoordinates AugmentedGenericOmega MovingMiddleCorrectionOmega
variable {K : Type*} [Field K] {m c q : ℕ}
variable (ω : K)
set_option maxHeartbeats 1600000

abbrev ChildQuotient (h : Fin q → Forms K m 2) :=
  Forms K m 2 ⧸ Submodule.span K (Set.range h)

def extraSpace (h : Fin q → Forms K m 2) (r : Fin 4 → Forms K m 2)
    (z : ChildQuotient h × ChildQuotient h) (U : Submodule K (ChildQuotient h)) :=
  (ExtraTraceOmega.extraTrace ω z
    (fun i => (Submodule.span K (Set.range h)).mkQ (r i)) U).range

def augmented (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (r : Fin 4 → Forms K m 2)
    (z : ChildQuotient h × ChildQuotient h) :=
  AugmentedGenericOmega.augmented ω
    (ExtraTraceOmega.withColumn (quotientProduct g (Submodule.span K (Set.range h))) z)
    (fun i => (Submodule.span K (Set.range h)).mkQ (r i))

theorem extraSpace_finrank (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (r : Fin 4 → Forms K m 2)
    (z : ChildQuotient h × ChildQuotient h)
    (ha : Function.Injective (augmented ω g h r z)) (U : Submodule K (ChildQuotient h)) :
    finrank K (extraSpace ω h r z U) = finrank K U + 4 :=
  ExtraTraceOmega.extraTrace_finrank ω (quotientProduct g _) z _ ha U

theorem discarded_image_disjoint (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (r : Fin 4 → Forms K m 2)
    (z : ChildQuotient h × ChildQuotient h)
    (ha : Function.Injective (augmented ω g h r z)) (U : Submodule K (ChildQuotient h)) :
    Disjoint ((discarded g).map
      (MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h))))
      (extraSpace ω h r z U) := by
  rw [discarded_quotient_image]
  exact ExtraTraceOmega.product_disjoint_extraTrace ω (quotientProduct g _) z _ ha U

theorem discarded_inter_correction (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (r : Fin 4 → Forms K m 2)
    (z : ChildQuotient h × ChildQuotient h) (hg : LinearIndependent K g)
    (ha : Function.Injective (augmented ω g h r z)) (U : Submodule K (ChildQuotient h)) :
    discarded g ⊓ (extraSpace ω h r z U).comap
      (MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h))) =
        SplitBlock22.mixedKoszulSpace g :=
  CorrectionSpace.intersection_eq_boundaries _ _ _ _
    (discarded_image_disjoint ω g h r z ha U)
    (discarded_inter_kernel g _ hg
      (ExtraTraceOmega.product_injective ω (quotientProduct g _) z _ ha))

abbrev Correction (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (r : Fin 4 → Forms K m 2)
    (z : ChildQuotient h × ChildQuotient h) (U : Submodule K (ChildQuotient h)) :=
  CorrectionSpace.Correction
    (MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h)))
    (SplitBlock22.mixedKoszulSpace g) (extraSpace ω h r z U)

def coefficientMap (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (r : Fin 4 → Forms K m 2)
    (z : ChildQuotient h × ChildQuotient h) (U : Submodule K (ChildQuotient h)) :
    Correction ω g h r z U →ₗ[K]
      (Fin c → MiddleCoordinates.Mixed K m ⧸ Submodule.span K (Set.range g)) :=
  (coefficientQuotientEquiv g).toLinearMap.comp
    (CorrectionSpace.correctionCoefficientMap _ _ _ _ (boundary_le_discarded g))

@[simp] theorem coefficientMap_mk (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (r : Fin 4 → Forms K m 2)
    (z : ChildQuotient h × ChildQuotient h) (U : Submodule K (ChildQuotient h))
    (a : (extraSpace ω h r z U).comap
      (MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h)))) :
    coefficientMap ω g h r z U (Submodule.Quotient.mk a) = coefficientProjection g a.val := rfl

theorem coefficientMap_injective (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (r : Fin 4 → Forms K m 2)
    (z : ChildQuotient h × ChildQuotient h) (hg : LinearIndependent K g)
    (ha : Function.Injective (augmented ω g h r z)) (U : Submodule K (ChildQuotient h)) :
    Function.Injective (coefficientMap ω g h r z U) :=
  (coefficientQuotientEquiv g).injective.comp
    (CorrectionSpace.correctionCoefficientMap_injective _ _ _ _
      (boundary_le_discarded g) (discarded_inter_correction ω g h r z hg ha U))

theorem correction_finrank (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (r : Fin 4 → Forms K m 2)
    (z : ChildQuotient h × ChildQuotient h)
    (ha : Function.Injective (augmented ω g h r z))
    (hs : Function.Surjective (MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h))))
    (U : Submodule K (ChildQuotient h)) :
    finrank K (Correction ω g h r z U) =
      finrank K (SplitBlock22.MiddleHomology g h) + 4 + finrank K U := by
  rw [CorrectionSpace.finrank_correction _ _ _
    (SplitBlock22.mixedKoszulSpace_le_quotient_kernel g _) hs]
  rw [extraSpace_finrank ω g h r z ha U]
  change finrank K (SplitBlock22.MiddleHomology g h) + (finrank K U + 4) = _
  omega

def coefficientImage (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (r : Fin 4 → Forms K m 2)
    (z : ChildQuotient h × ChildQuotient h) (U : Submodule K (ChildQuotient h)) :=
  ((extraSpace ω h r z U).comap
    (MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h)))).map (coefficientProjection g)

theorem coefficientImage_eq_range (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (r : Fin 4 → Forms K m 2)
    (z : ChildQuotient h × ChildQuotient h) (U : Submodule K (ChildQuotient h)) :
    coefficientImage ω g h r z U = (coefficientMap ω g h r z U).range := by
  apply le_antisymm
  · rintro y ⟨a, ha, rfl⟩
    exact ⟨Submodule.Quotient.mk ⟨a, ha⟩, coefficientMap_mk ω g h r z U ⟨a, ha⟩⟩
  · rintro y ⟨a, rfl⟩
    refine Submodule.Quotient.induction_on _ a ?_
    intro a
    exact ⟨a.val, a.property, (coefficientMap_mk ω g h r z U a).symm⟩

theorem coefficientImage_finrank (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (r : Fin 4 → Forms K m 2)
    (z : ChildQuotient h × ChildQuotient h)
    (hg : LinearIndependent K g) (hh : LinearIndependent K h)
    (ha : Function.Injective (augmented ω g h r z))
    (hs : Function.Surjective (MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h))))
    (U : Submodule K (ChildQuotient h)) :
    (finrank K (coefficientImage ω g h r z U) : ℤ) = Counts.H m q c + 4 + finrank K U := by
  rw [coefficientImage_eq_range,
    LinearMap.finrank_range_of_inj (coefficientMap_injective ω g h r z hg ha U),
    correction_finrank ω g h r z ha hs U,
    ← (SplitBlock22.homologyEquiv g h hh).finrank_eq]
  push_cast
  rw [SplitBlock22.homology_finrank_eq_H g h hg hh hs]

/-- The actual quotient class of the retained mixed square. -/
def squareClass (h : Fin q → Forms K m 2) (ζ : MiddleCoordinates.Mixed K m) :
    ChildQuotient h × ChildQuotient h :=
  ((Submodule.span K (Set.range h)).mkQ.prodMap
    (Submodule.span K (Set.range h)).mkQ) (MiddleCoordinates.projectedProduct ζ ζ)

/-- The D.12 open is exactly the augmented hypothesis of this correction space. -/
theorem augmented_square_eq (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (r : Fin 4 → Forms K m 2)
    (ζ : MiddleCoordinates.Mixed K m) :
    augmented ω g h r (squareClass h ζ) =
      AugmentedGenericOmega.quotientAugmented ω
        (MarkedSquareGenericOmega.productWithSquare g ζ) h r := by
  apply LinearMap.ext
  rintro ⟨⟨b,t⟩,a,ξ⟩
  apply Prod.ext <;>
    simp [augmented, squareClass, AugmentedGenericOmega.quotientAugmented,
      AugmentedGenericOmega.augmented, ExtraTraceOmega.withColumn,
      MarkedSquareGenericOmega.productWithSquare, quotientProduct]

end Quartic.ExtraCorrectionOmega
