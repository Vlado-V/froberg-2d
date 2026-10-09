module

public import Froberg.Koszul

@[expose] public section

/-! The actual endpoint complex after a fixed linear projection of its target.
This includes the quotient by the complementary pure-variable target in Section 6. -/
noncomputable section
namespace Froberg
open Module

variable {K W : Type*} [Field K] [AddCommGroup W] [Module K W]
  {n d r : ℕ}

abbrev projectedEndpointMultiplication (π : Forms K n (2 * d) →ₗ[K] W)
    (q : Fin r → Forms K n d) := π.comp (endpointMultiplication q)

abbrev ProjectedEndpointHomology (π : Forms K n (2 * d) →ₗ[K] W)
    (q : Fin r → Forms K n d) :=
  KernelModulo (projectedEndpointMultiplication π q) (koszulSpace q)

theorem koszulSpace_le_projected_ker (π : Forms K n (2 * d) →ₗ[K] W)
    (q : Fin r → Forms K n d) :
    koszulSpace q ≤ (projectedEndpointMultiplication π q).ker := by
  intro x hx
  change π (endpointMultiplication q x) = 0
  rw [kernel_contains_koszul q hx, map_zero]

theorem projected_homology_add_pairs (π : Forms K n (2 * d) →ₗ[K] W)
    (q : Fin r → Forms K n d) (hq : LinearIndependent K q) :
    finrank K (ProjectedEndpointHomology π q) + r.choose 2 =
      finrank K (projectedEndpointMultiplication π q).ker := by
  have h := finrank_kernelModulo_add (projectedEndpointMultiplication π q) (koszulSpace q)
  have hb : finrank K (kernelBoundary (projectedEndpointMultiplication π q) (koszulSpace q)) =
      r.choose 2 := by
    unfold kernelBoundary
    rw [(Submodule.comapSubtypeEquivOfLe (koszulSpace_le_projected_ker π q)).finrank_eq]
    exact (finrank_span_eq_card (koszulVector_linearIndependent q hq)).trans card_generatorPair
  rwa [hb] at h

/-- Restoring the unprojected target can only decrease first homology. -/
theorem homology_le_projected (π : Forms K n (2 * d) →ₗ[K] W)
    (q : Fin r → Forms K n d) (hq : LinearIndependent K q) :
    finrank K (EndpointHomology q) ≤ finrank K (ProjectedEndpointHomology π q) := by
  have hk : (endpointMultiplication q).ker ≤ (projectedEndpointMultiplication π q).ker := by
    intro x hx
    change π (endpointMultiplication q x) = 0
    rw [hx, map_zero]
  have hd := Submodule.finrank_mono hk
  have hbefore := homology_add_pairs q hq
  have hafter := projected_homology_add_pairs π q hq
  omega

/-- If the removed target misses the multiplication image, no cycles change. -/
theorem projected_ker_eq_of_injOn (π : Forms K n (2 * d) →ₗ[K] W)
    (q : Fin r → Forms K n d)
    (hinj : Set.InjOn π (endpointMultiplication q).range) :
    (projectedEndpointMultiplication π q).ker = (endpointMultiplication q).ker := by
  ext x
  change π (endpointMultiplication q x) = 0 ↔ endpointMultiplication q x = 0
  constructor
  · intro h
    apply hinj (LinearMap.mem_range_self _ _) (Submodule.zero_mem _)
    simpa using h
  · intro h
    rw [h, map_zero]

theorem projected_homology_eq_of_injOn (π : Forms K n (2 * d) →ₗ[K] W)
    (q : Fin r → Forms K n d) (hq : LinearIndependent K q)
    (hinj : Set.InjOn π (endpointMultiplication q).range) :
    finrank K (ProjectedEndpointHomology π q) = finrank K (EndpointHomology q) := by
  have hbefore := homology_add_pairs q hq
  have hafter := projected_homology_add_pairs π q hq
  have hk : finrank K (projectedEndpointMultiplication π q).ker =
      finrank K (endpointMultiplication q).ker :=
    congrArg (fun P : Submodule K (Fin r → Forms K n d) => finrank K P)
      (projected_ker_eq_of_injOn π q hinj)
  omega

/-- The projected endpoint Euler formula uses the actual target dimension. -/
theorem projected_endpoint_euler [FiniteDimensional K W]
    (π : Forms K n (2 * d) →ₗ[K] W)
    (q : Fin r → Forms K n d) (hq : LinearIndependent K q) :
    (finrank K (W ⧸ (projectedEndpointMultiplication π q).range) : ℤ) -
      (finrank K (ProjectedEndpointHomology π q) : ℤ) =
        (finrank K W : ℤ) - (finrank K (Fin r → Forms K n d) : ℤ) + r.choose 2 := by
  have hH := projected_homology_add_pairs π q hq
  have hC := (projectedEndpointMultiplication π q).range.finrank_quotient_add_finrank
  have hR := (projectedEndpointMultiplication π q).finrank_range_add_finrank_ker
  omega

end Froberg
