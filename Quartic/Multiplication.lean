import Quartic.Koszul
import Quartic.Generic
import Quartic.QuotientModel

/-!
# Multiplication matrices and the actual quartic quotient

The image of an ordered quadratic multiplication map is the intrinsic product
subspace. Consequently the independent Koszul relations give a lower bound on
the degree-four quotient dimension for every independent family of quadrics.
-/

noncomputable section

namespace Quartic

open Module

variable {K : Type*} [Field K] {n r : ℕ}

/-- Multiplication in ambient polynomial coordinates. -/
theorem quadraticMultiplication_val (q : Fin r → Forms K n 2)
    (a : Fin r → Forms K n 2) :
    (quadraticMultiplication q a).val = ∑ i, (q i).val * (a i).val := by
  simp [quadraticMultiplication, mulQuadratic]

/-- The range in the polynomial ring is precisely the submodule of quadratic products. -/
theorem range_ambient_quadraticMultiplication (q : Fin r → Forms K n 2) :
    LinearMap.range ((Forms K n 4).subtype.comp (quadraticMultiplication q)) =
      Submodule.span K (Set.range (fun i => (q i).val)) * Forms K n 2 := by
  apply le_antisymm
  · rintro p ⟨a, rfl⟩
    change (quadraticMultiplication q a).val ∈ _
    rw [quadraticMultiplication_val]
    apply Submodule.sum_mem
    intro i _
    exact Submodule.mul_mem_mul (Submodule.subset_span ⟨i, rfl⟩) (a i).property
  · apply Submodule.mul_le.mpr
    intro f hf a ha
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hf
    refine ⟨fun i => c i • (⟨a, ha⟩ : Forms K n 2), ?_⟩
    change (quadraticMultiplication q (fun i => c i • (⟨a, ha⟩ : Forms K n 2))).val = _
    simp [quadraticMultiplication_val, Finset.sum_mul]

/-- The coordinate multiplication map and the intrinsic quartic product subspace agree. -/
theorem range_quadraticMultiplication (q : Fin r → Forms K n 2) :
    LinearMap.range (quadraticMultiplication q) =
      quarticProducts K n (Submodule.span K (Set.range (fun i => (q i).val))) := by
  have h := congrArg (fun P : Submodule K (Poly K n) => P.comap (Forms K n 4).subtype)
    (range_ambient_quadraticMultiplication q)
  rw [LinearMap.range_comp,
    Submodule.comap_map_eq_of_injective (Submodule.injective_subtype _)] at h
  exact h

/-- The quotient dimension is the codimension of the multiplication image. -/
theorem quartic_quotient_add_rank (q : Fin r → Forms K n 2) :
    finrank K (QuarticQuotient K n
      (Submodule.span K (Set.range (fun i => (q i).val)))) +
      finrank K (LinearMap.range (quadraticMultiplication q)) = (n + 3).choose 4 := by
  rw [range_quadraticMultiplication q]
  exact ((quarticProducts K n
    (Submodule.span K (Set.range (fun i => (q i).val)))).finrank_quotient_add_finrank).trans
      (finrank_quartics K n)

/-- Every independent quadratic family satisfies the expected lower bound.
Attaining equality is the additional, nontrivial generic assertion. -/
theorem quartic_quotient_lower_bound (q : Fin r → Forms K n 2)
    (hq : LinearIndependent K q) :
    expectedDimension n r ≤ finrank K (QuarticQuotient K n
      (Submodule.span K (Set.range (fun i => (q i).val)))) := by
  have hr := quartic_rank_add_pairs_le q hq
  have hd := quartic_quotient_add_rank q
  unfold expectedDimension
  zify at hr hd
  omega

/-- Any quadratic subspace has an ordered independent basis in the homogeneous space. -/
theorem quadratic_subspace_has_basis (Q : Submodule K (Poly K n))
    (hQ : Q ≤ Forms K n 2) :
    ∃ q : Fin (finrank K Q) → Forms K n 2,
      LinearIndependent K q ∧
        Submodule.span K (Set.range (fun i => (q i).val)) = Q := by
  let f : Q →ₗ[K] Forms K n 2 := Submodule.inclusion hQ
  have hf : Function.Injective f := Submodule.inclusion_injective hQ
  let : Module.Finite K Q := Module.Finite.of_injective f hf
  refine ⟨f ∘ Module.finBasis K Q,
    (Module.finBasis K Q).linearIndependent.map' f (LinearMap.ker_eq_bot.mpr hf), ?_⟩
  change Submodule.span K (Set.range (Q.subtype ∘ Module.finBasis K Q)) = Q
  rw [Set.range_comp, ← Submodule.map_span, (Module.finBasis K Q).span_eq,
    Submodule.map_top, Submodule.range_subtype]

/-- An intrinsic lower bound for every subspace of homogeneous quadrics. -/
theorem quadratic_subspace_quotient_lower_bound (Q : Submodule K (Poly K n))
    (hQ : Q ≤ Forms K n 2) :
    expectedDimension n (finrank K Q) ≤ finrank K (QuarticQuotient K n Q) := by
  obtain ⟨q, hq, hspan⟩ := quadratic_subspace_has_basis Q hQ
  have h := quartic_quotient_lower_bound q hq
  rw [hspan] at h
  exact h

/-- Expressing a prescribed quotient dimension as an equivalent matrix-rank condition. -/
theorem quartic_quotient_dimension_iff_rank (q : Fin r → Forms K n 2)
    (d : ℕ) (hd : d ≤ (n + 3).choose 4) :
    finrank K (QuarticQuotient K n
      (Submodule.span K (Set.range (fun i => (q i).val)))) = d ↔
      finrank K (LinearMap.range (quadraticMultiplication q)) = (n + 3).choose 4 - d := by
  have h := quartic_quotient_add_rank q
  omega

/-- The same lower bound directly on the coefficient arrays used in `GenericQuartic`. -/
theorem coefficient_quotient_lower_bound (a : CoefficientIndex n r → K)
    (ha : LinearIndependent K (fun i => (coefficientQuadrics K n r a i).val)) :
    expectedDimension n r ≤
      finrank K (QuarticQuotient K n (coefficientSpace K n r a)) := by
  exact quartic_quotient_lower_bound (coefficientQuadrics K n r a)
    (LinearIndependent.of_comp (Forms K n 2).subtype ha)

/-- The bound also holds for the actual homogeneous image in the ring quotient. -/
theorem coefficient_ringQuotient_lower_bound (a : CoefficientIndex n r → K)
    (ha : LinearIndependent K (fun i => (coefficientQuadrics K n r a i).val)) :
    expectedDimension n r ≤
      finrank K (LinearMap.range (quarticToRingQuotient (coefficientSpace K n r a))) := by
  rw [← finrank_quarticQuotient_eq_image _ (coefficientSpace_quadratic K n r a)]
  exact coefficient_quotient_lower_bound a ha

end Quartic
