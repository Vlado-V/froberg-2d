import Quartic.CorrectionSpace
import Quartic.SplitBlock22MiddleHomology
import Quartic.AugmentedGeneric
import Mathlib.LinearAlgebra.Quotient.Pi

/-!
# Actual moving middle correction coefficients

This proves the coefficient injection and dimension identity from `tr:Tdimension`
for the actual middle multiplication map. The discarded coefficient space is
`(span g)^c`; its product image is the actual symmetric-product range and its
kernel consists exactly of mixed Koszul boundaries. Actual augmented
injectivity makes pure and marked traces independent and disjoint from those
products, so the correction quotient injects into `(Mixed / span g)^c`.

The marked motion is the fixed direction `u-v`. The marked coefficient subspace
of the child quadratic quotient is explicit. Identifying its dimension with
the old-child defect is a separate input, not an assumption hidden in the
coefficient injection.
-/
noncomputable section
namespace Quartic.MovingMiddleCorrection
open Module HomologyCoordinates AugmentedMiddle AugmentedGeneric
set_option maxHeartbeats 2000000
variable {K : Type*} [Field K]

section Traces
variable {S A : Type*} [AddCommGroup S] [Module K S]
  [AddCommGroup A] [Module K A]

def traceMap (r : Fin 4 → A) (U : Submodule K A) :
    (U × BlockHomology K) →ₗ[K] A × A :=
  (U.subtype.prod (-U.subtype)).coprod (pureTrace r)

@[simp] theorem traceMap_apply (r : Fin 4 → A) (U : Submodule K A)
    (a : U) (ξ : BlockHomology K) :
    traceMap r U (a,ξ) = (a.val + (pureTrace r ξ).1, -a.val + (pureTrace r ξ).2) := rfl

theorem augmented_decomposition (F : S →ₗ[K] A × A) (r : Fin 4 → A)
    (U : Submodule K A) (b : S) (a : U) (ξ : BlockHomology K) :
    augmented F r (b,a.val,ξ) = F b + traceMap r U (a,ξ) := by
  apply Prod.ext <;> simp [augmented_apply, sub_eq_add_neg, add_assoc]

theorem product_injective (F : S →ₗ[K] A × A) (r : Fin 4 → A)
    (ha : Function.Injective (augmented F r)) : Function.Injective F := by
  intro b b' h
  have he : augmented F r (b,0,0) = augmented F r (b',0,0) := by
    simp only [augmented_apply, map_zero, Prod.fst_zero, Prod.snd_zero, add_zero, sub_zero]
    exact Prod.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
  exact congrArg Prod.fst (ha he)

theorem traceMap_injective (F : S →ₗ[K] A × A) (r : Fin 4 → A)
    (ha : Function.Injective (augmented F r)) (U : Submodule K A) :
    Function.Injective (traceMap r U) := by
  rintro ⟨a,ξ⟩ ⟨b,η⟩ h
  have he : augmented F r (0,a.val,ξ) = augmented F r (0,b.val,η) := by
    rw [augmented_decomposition F r U, augmented_decomposition F r U, h]
  have hz := congrArg Prod.snd (ha he)
  apply Prod.ext
  · exact Subtype.ext (congrArg Prod.fst hz)
  · exact congrArg (fun p : A × BlockHomology K => p.2) hz

theorem product_disjoint_trace (F : S →ₗ[K] A × A) (r : Fin 4 → A)
    (ha : Function.Injective (augmented F r)) (U : Submodule K A) :
    Disjoint F.range (traceMap r U).range := by
  apply Submodule.disjoint_def.mpr
  rintro z ⟨b,hb⟩ ⟨⟨a,ξ⟩,ht⟩
  have he : augmented F r (b,0,0) = augmented F r (0,a.val,ξ) := by
    rw [augmented_decomposition F r U]
    simpa only [augmented_apply, map_zero, Prod.fst_zero, Prod.snd_zero,
      add_zero, sub_zero, zero_add, Prod.mk.eta] using hb.trans ht.symm
  have hb0 : b = 0 := congrArg Prod.fst (ha he)
  simpa only [hb0, map_zero] using hb.symm

theorem traceMap_finrank [FiniteDimensional K A]
    (F : S →ₗ[K] A × A) (r : Fin 4 → A)
    (ha : Function.Injective (augmented F r)) (U : Submodule K A) :
    finrank K (traceMap r U).range = finrank K U + 3 := by
  rw [LinearMap.finrank_range_of_inj (traceMap_injective F r ha U), Module.finrank_prod]
  congr 1
  exact ((HomologyCoordinates.homologyEquiv (K := K)).finrank_eq).symm.trans (by simp)
end Traces

section Actual
variable {m c q : ℕ}

def discarded (g : Fin c → MiddleCoordinates.Mixed K m) :
    Submodule K (Fin c → MiddleCoordinates.Mixed K m) :=
  Submodule.pi Set.univ (fun _ => Submodule.span K (Set.range g))

@[simp] theorem mem_discarded (g : Fin c → MiddleCoordinates.Mixed K m)
    (a : Fin c → MiddleCoordinates.Mixed K m) :
    a ∈ discarded g ↔ ∀ i, a i ∈ Submodule.span K (Set.range g) := by
  simp [discarded, Submodule.mem_pi]

def discardedEquiv (g : Fin c → MiddleCoordinates.Mixed K m) :
    discarded g ≃ₗ[K] (Fin c → Submodule.span K (Set.range g)) where
  toFun a i := ⟨a.val i, (mem_discarded g a.val).mp a.property i⟩
  invFun a := ⟨fun i => (a i).val, (mem_discarded g _).mpr (fun i => (a i).property)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

set_option backward.isDefEq.respectTransparency false in
theorem discarded_finrank (g : Fin c → MiddleCoordinates.Mixed K m)
    (hg : LinearIndependent K g) : finrank K (discarded g) = c*c := by
  rw [(discardedEquiv g).finrank_eq]
  let : Module.Free K (Submodule.span K (Set.range g)) := Module.Free.of_basis (Module.Basis.span hg)
  rw [Module.finrank_pi_fintype]
  simp [finrank_span_eq_card hg]

theorem boundary_le_discarded (g : Fin c → MiddleCoordinates.Mixed K m) :
    SplitBlock22.mixedKoszulSpace g ≤ discarded g := by
  apply Submodule.span_le.mpr
  rintro _ ⟨p,rfl⟩
  apply (mem_discarded g _).mpr
  intro i
  change (if i = p.val.1 then g p.val.2 else 0) -
    (if i = p.val.2 then g p.val.1 else 0) ∈ Submodule.span K (Set.range g)
  apply Submodule.sub_mem
  · split_ifs <;> first | exact Submodule.subset_span ⟨_,rfl⟩ | exact Submodule.zero_mem _
  · split_ifs <;> first | exact Submodule.subset_span ⟨_,rfl⟩ | exact Submodule.zero_mem _

theorem multiplication_single (g : Fin c → MiddleCoordinates.Mixed K m)
    (i : Fin c) (a : MiddleCoordinates.Mixed K m) :
    MiddleCoordinates.multiplication g (Pi.single i a) = MiddleCoordinates.projectedProduct (g i) a := by
  classical
  simp only [MiddleCoordinates.multiplication, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, Pi.single_apply]
  have he (j : Fin c) : MiddleCoordinates.projectedProduct (g j) (if j = i then a else 0) =
      if j = i then MiddleCoordinates.projectedProduct (g i) a else 0 := by
    split_ifs with h <;> simp_all
  simp_rw [he]
  simp

theorem discarded_image (g : Fin c → MiddleCoordinates.Mixed K m) :
    (discarded g).map (MiddleCoordinates.multiplication g) = (productMap g).range := by
  classical
  apply le_antisymm
  · rintro z ⟨a,ha,rfl⟩
    simp only [MiddleCoordinates.multiplication, LinearMap.sum_apply,
      LinearMap.comp_apply, LinearMap.proj_apply]
    change (∑ i, MiddleCoordinates.projectedProduct (g i) (a i)) ∈ (productMap g).range
    apply Submodule.sum_mem
    intro i _
    have he : Submodule.span K (Set.range g) ≤
        (productMap g).range.comap (MiddleCoordinates.projectedProduct (g i)) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨j,rfl⟩
      exact ⟨quadraticMonomial i j, productMap_monomial g i j⟩
    exact he ((mem_discarded g a).mp ha i)
  · rintro z ⟨b,rfl⟩
    have he : (⊤ : Submodule K (Forms K c 2)) ≤
        ((discarded g).map (MiddleCoordinates.multiplication g)).comap (productMap g) := by
      rw [← quadraticMonomial_span]
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨i,j⟩,rfl⟩
      refine ⟨Pi.single i (g j), (mem_discarded g _).mpr ?_, ?_⟩
      · intro k
        simp only [Pi.single_apply]
        split_ifs <;> first | exact Submodule.subset_span ⟨_,rfl⟩ | exact Submodule.zero_mem _
      · rw [multiplication_single, productMap_monomial]
    exact he (Submodule.mem_top)

def quotientProduct (g : Fin c → MiddleCoordinates.Mixed K m)
    (Q : Submodule K (Forms K m 2)) : Forms K c 2 →ₗ[K] (Forms K m 2 ⧸ Q) × (Forms K m 2 ⧸ Q) :=
  (Q.mkQ.prodMap Q.mkQ).comp (productMap g)

theorem discarded_quotient_image (g : Fin c → MiddleCoordinates.Mixed K m)
    (Q : Submodule K (Forms K m 2)) :
    (discarded g).map (MiddleCoordinates.quotientMap g Q) = (quotientProduct g Q).range := by
  rw [MiddleCoordinates.quotientMap, Submodule.map_comp, discarded_image,
    quotientProduct, LinearMap.range_comp]


/-- Rank-nullity on a coefficient subspace, retaining its actual intersection kernel. -/
theorem finrank_map_add_inf_ker {V W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V]
    (F : V →ₗ[K] W) (D : Submodule K V) :
    finrank K (D.map F) + finrank K ↥(D ⊓ F.ker) = finrank K D := by
  have hr := (F.domRestrict D).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at hr
  have he : F.ker.comap D.subtype = (D ⊓ F.ker).comap D.subtype := by
    ext a
    change F a.val = 0 ↔ a.val ∈ D ∧ F a.val = 0
    exact ⟨fun h => ⟨a.property, h⟩, And.right⟩
  rw [he, (Submodule.comapSubtypeEquivOfLe
    (show D ⊓ F.ker ≤ D from inf_le_left)).finrank_eq] at hr
  exact hr

private theorem symmetric_alternating_count (c : ℕ) :
    (c+1).choose 2 + c.choose 2 = c*c := by
  have h₁ := Nat.choose_succ_succ c 1
  have h₂ := Nat.add_one_mul_choose_eq c 1
  simp only [Nat.choose_one_right] at h₁ h₂
  nlinarith

/-- Exactness on coefficients entirely contained in the mixed generator space. -/
theorem discarded_inter_kernel (g : Fin c → MiddleCoordinates.Mixed K m)
    (Q : Submodule K (Forms K m 2)) (hg : LinearIndependent K g)
    (hinj : Function.Injective (quotientProduct g Q)) :
    discarded g ⊓ (MiddleCoordinates.quotientMap g Q).ker =
      SplitBlock22.mixedKoszulSpace g := by
  have hle : SplitBlock22.mixedKoszulSpace g ≤
      discarded g ⊓ (MiddleCoordinates.quotientMap g Q).ker :=
    le_inf (boundary_le_discarded g)
      (SplitBlock22.mixedKoszulSpace_le_quotient_kernel g Q)
  apply (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  have hr := finrank_map_add_inf_ker (MiddleCoordinates.quotientMap g Q) (discarded g)
  rw [discarded_quotient_image, LinearMap.finrank_range_of_inj hinj,
    finrank_quadrics, discarded_finrank g hg] at hr
  have hb : finrank K (SplitBlock22.mixedKoszulSpace g) = c.choose 2 :=
    (finrank_span_eq_card (koszulVector_linearIndependent g hg)).trans card_generatorPair
  rw [hb]
  have hc := symmetric_alternating_count c
  omega


/-- The actual marked and pure trace subspace, with the marked child subspace explicit. -/
def traceSpace (h : Fin q → Forms K m 2) (r : Fin 4 → Forms K m 2)
    (markedU : Submodule K (Forms K m 2 ⧸ Submodule.span K (Set.range h))) :
    Submodule K ((Forms K m 2 ⧸ Submodule.span K (Set.range h)) ×
      (Forms K m 2 ⧸ Submodule.span K (Set.range h))) :=
  (traceMap (fun i => (Submodule.span K (Set.range h)).mkQ (r i)) markedU).range

/-- No quotient-rank assumption: the actual augmented map supplies trace independence. -/
theorem traceSpace_finrank (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (r : Fin 4 → Forms K m 2)
    (ha : Function.Injective (quotientAugmented (productMap g) h r))
    (markedU : Submodule K (Forms K m 2 ⧸ Submodule.span K (Set.range h))) :
    finrank K (traceSpace h r markedU) = finrank K markedU + 3 :=
  traceMap_finrank (quotientProduct g _) _ ha markedU

theorem discarded_image_disjoint_trace (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (r : Fin 4 → Forms K m 2)
    (ha : Function.Injective (quotientAugmented (productMap g) h r))
    (markedU : Submodule K (Forms K m 2 ⧸ Submodule.span K (Set.range h))) :
    Disjoint ((discarded g).map (MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h))))
      (traceSpace h r markedU) := by
  rw [discarded_quotient_image]
  exact product_disjoint_trace (quotientProduct g _) _ ha markedU

/-- The only correction coefficients discarded modulo the mixed generators are boundaries. -/
theorem discarded_inter_correction (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (r : Fin 4 → Forms K m 2)
    (hg : LinearIndependent K g)
    (ha : Function.Injective (quotientAugmented (productMap g) h r))
    (markedU : Submodule K (Forms K m 2 ⧸ Submodule.span K (Set.range h))) :
    discarded g ⊓ (traceSpace h r markedU).comap
      (MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h))) =
        SplitBlock22.mixedKoszulSpace g :=
  CorrectionSpace.intersection_eq_boundaries _ _ _ _
    (discarded_image_disjoint_trace g h r ha markedU)
    (discarded_inter_kernel g _ hg (product_injective (quotientProduct g _) _ ha))

/-- The actual correction space, modulo the actual alternating mixed boundaries. -/
abbrev Correction (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (r : Fin 4 → Forms K m 2)
    (markedU : Submodule K (Forms K m 2 ⧸ Submodule.span K (Set.range h))) :=
  CorrectionSpace.Correction
    (MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h)))
    (SplitBlock22.mixedKoszulSpace g) (traceSpace h r markedU)

/-- Coordinatewise coefficient reduction modulo the actual mixed generator space. -/
def coefficientProjection (g : Fin c → MiddleCoordinates.Mixed K m) :
    (Fin c → MiddleCoordinates.Mixed K m) →ₗ[K]
      (Fin c → MiddleCoordinates.Mixed K m ⧸ Submodule.span K (Set.range g)) where
  toFun a i := (Submodule.span K (Set.range g)).mkQ (a i)
  map_add' a b := by ext i; exact map_add _ _ _
  map_smul' s a := by
    ext i
    exact (Submodule.span K (Set.range g)).mkQ.map_smul s (a i)

@[simp] theorem coefficientProjection_apply (g : Fin c → MiddleCoordinates.Mixed K m)
    (a : Fin c → MiddleCoordinates.Mixed K m) (i : Fin c) :
    coefficientProjection g a i = (Submodule.span K (Set.range g)).mkQ (a i) := rfl

def coefficientQuotientEquiv (g : Fin c → MiddleCoordinates.Mixed K m) :
    ((Fin c → MiddleCoordinates.Mixed K m) ⧸ discarded g) ≃ₗ[K]
      (Fin c → MiddleCoordinates.Mixed K m ⧸ Submodule.span K (Set.range g)) :=
  Submodule.quotientPi (fun _ : Fin c => Submodule.span K (Set.range g))

@[simp] theorem coefficientQuotientEquiv_mk (g : Fin c → MiddleCoordinates.Mixed K m)
    (a : Fin c → MiddleCoordinates.Mixed K m) :
    coefficientQuotientEquiv g ((discarded g).mkQ a) = coefficientProjection g a := rfl

/-- Actual coefficient map on the correction quotient. -/
def coefficientMap (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (r : Fin 4 → Forms K m 2)
    (markedU : Submodule K (Forms K m 2 ⧸ Submodule.span K (Set.range h))) :
    Correction g h r markedU →ₗ[K]
      (Fin c → MiddleCoordinates.Mixed K m ⧸ Submodule.span K (Set.range g)) :=
  (coefficientQuotientEquiv g).toLinearMap.comp
    (CorrectionSpace.correctionCoefficientMap _ _ _ _ (boundary_le_discarded g))

@[simp] theorem coefficientMap_mk (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (r : Fin 4 → Forms K m 2)
    (markedU : Submodule K (Forms K m 2 ⧸ Submodule.span K (Set.range h)))
    (a : (traceSpace h r markedU).comap
      (MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h)))) :
    coefficientMap g h r markedU (Submodule.Quotient.mk a) = coefficientProjection g a.val := rfl

/-- Actual coefficient injection, derived from augmented injectivity. -/
theorem coefficientMap_injective (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (r : Fin 4 → Forms K m 2)
    (hg : LinearIndependent K g)
    (ha : Function.Injective (quotientAugmented (productMap g) h r))
    (markedU : Submodule K (Forms K m 2 ⧸ Submodule.span K (Set.range h))) :
    Function.Injective (coefficientMap g h r markedU) :=
  (coefficientQuotientEquiv g).injective.comp
    (CorrectionSpace.correctionCoefficientMap_injective _ _ _ _
      (boundary_le_discarded g) (discarded_inter_correction g h r hg ha markedU))

/-- The actual projected coefficient image, defined before quotienting any boundaries. -/
def coefficientImage (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (r : Fin 4 → Forms K m 2)
    (markedU : Submodule K (Forms K m 2 ⧸ Submodule.span K (Set.range h))) :
    Submodule K (Fin c → MiddleCoordinates.Mixed K m ⧸ Submodule.span K (Set.range g)) :=
  ((traceSpace h r markedU).comap
    (MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h)))).map (coefficientProjection g)

theorem coefficientImage_eq_range (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (r : Fin 4 → Forms K m 2)
    (markedU : Submodule K (Forms K m 2 ⧸ Submodule.span K (Set.range h))) :
    coefficientImage g h r markedU = (coefficientMap g h r markedU).range := by
  apply le_antisymm
  · rintro z ⟨a, ha, rfl⟩
    exact ⟨Submodule.Quotient.mk ⟨a, ha⟩, coefficientMap_mk g h r markedU ⟨a, ha⟩⟩
  · rintro z ⟨a, rfl⟩
    refine Submodule.Quotient.induction_on _ a ?_
    intro a
    exact ⟨a.val, a.property, (coefficientMap_mk g h r markedU a).symm⟩

/-- Dimension of the actual correction space, with the marked coefficient dimension explicit. -/
theorem correction_finrank (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (r : Fin 4 → Forms K m 2)
    (ha : Function.Injective (quotientAugmented (productMap g) h r))
    (hs : Function.Surjective
      (MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h))))
    (markedU : Submodule K (Forms K m 2 ⧸ Submodule.span K (Set.range h))) :
    finrank K (Correction g h r markedU) =
      finrank K (SplitBlock22.MiddleHomology g h) + 3 + finrank K markedU := by
  rw [CorrectionSpace.finrank_correction _ _ _
    (SplitBlock22.mixedKoszulSpace_le_quotient_kernel g _) hs]
  rw [traceSpace_finrank g h r ha markedU]
  change finrank K (SplitBlock22.MiddleHomology g h) + (finrank K markedU + 3) = _
  omega

/-- The actual coordinate-quotient coefficient image has the required transfer dimension. -/
theorem coefficientImage_finrank (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (r : Fin 4 → Forms K m 2)
    (hg : LinearIndependent K g) (hh : LinearIndependent K h)
    (ha : Function.Injective (quotientAugmented (productMap g) h r))
    (hs : Function.Surjective
      (MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h))))
    (markedU : Submodule K (Forms K m 2 ⧸ Submodule.span K (Set.range h))) :
    (finrank K (coefficientImage g h r markedU) : ℤ) =
      Counts.H m q c + 3 + finrank K markedU := by
  rw [coefficientImage_eq_range,
    LinearMap.finrank_range_of_inj (coefficientMap_injective g h r hg ha markedU),
    correction_finrank g h r ha hs markedU,
    ← (SplitBlock22.homologyEquiv g h hh).finrank_eq]
  push_cast
  rw [SplitBlock22.homology_finrank_eq_H g h hg hh hs]


/-- Numerical form after separately identifying the marked child coefficient dimension. -/
theorem coefficientImage_finrank_of_marked (g : Fin c → MiddleCoordinates.Mixed K m)
    (h : Fin q → Forms K m 2) (r : Fin 4 → Forms K m 2)
    (hg : LinearIndependent K g) (hh : LinearIndependent K h)
    (ha : Function.Injective (quotientAugmented (productMap g) h r))
    (hs : Function.Surjective
      (MiddleCoordinates.quotientMap g (Submodule.span K (Set.range h))))
    (markedU : Submodule K (Forms K m 2 ⧸ Submodule.span K (Set.range h)))
    (δ : ℕ) (hmarked : finrank K markedU = δ) :
    (finrank K (coefficientImage g h r markedU) : ℤ) = Counts.H m q c + 3 + δ := by
  rw [coefficientImage_finrank g h r hg hh ha hs markedU, hmarked]

end Actual
end Quartic.MovingMiddleCorrection
