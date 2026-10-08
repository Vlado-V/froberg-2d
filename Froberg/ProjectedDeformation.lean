import Froberg.NormalDeformation
import Froberg.TargetProjection

/-! First normal maps after the fixed target projection used in the transfer
construction. The resulting bound also applies to the original polynomial ideal. -/
noncomputable section
set_option maxHeartbeats 1200000
namespace Froberg
open Module MvPolynomial

variable {K W : Type*} [Field K] [Infinite K]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  {n d r : ℕ}

abbrev ProjectedEndpointCokernel (π : Forms K n (2 * d) →ₗ[K] W)
    (q : Fin r → Forms K n d) := W ⧸ (projectedEndpointMultiplication π q).range

def projectedNormalCycles (π : Forms K n (2 * d) →ₗ[K] W)
    (q p : Fin r → Forms K n d) :
    (projectedEndpointMultiplication π q).ker →ₗ[K] ProjectedEndpointCokernel π q :=
  (projectedEndpointMultiplication π q).range.mkQ.comp
    ((projectedEndpointMultiplication π p).comp (projectedEndpointMultiplication π q).ker.subtype)

theorem incoming_le_ker_projectedNormalCycles (π : Forms K n (2 * d) →ₗ[K] W)
    (q p : Fin r → Forms K n d) :
    kernelBoundary (projectedEndpointMultiplication π q) (koszulSpace q) ≤
      (projectedNormalCycles π q p).ker := by
  have hspan : koszulSpace q ≤
      ((projectedEndpointMultiplication π q).range.mkQ.comp
        (projectedEndpointMultiplication π p)).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨ij, rfl⟩
    change (projectedEndpointMultiplication π q).range.mkQ
      (π (endpointMultiplication p (koszulVector q ij))) = 0
    rw [endpointMultiplication_cross_koszul, map_neg, map_neg]
    have hz : (projectedEndpointMultiplication π q).range.mkQ
        (π (endpointMultiplication q (koszulVector p ij))) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr ⟨koszulVector p ij, rfl⟩
    rw [hz, neg_zero]
  intro a ha
  exact hspan ha

def projectedNormalMap (π : Forms K n (2 * d) →ₗ[K] W)
    (q p : Fin r → Forms K n d) :
    ProjectedEndpointHomology π q →ₗ[K] ProjectedEndpointCokernel π q :=
  descendCycleMap (projectedEndpointMultiplication π q) (koszulSpace q)
    (projectedNormalCycles π q p) (incoming_le_ker_projectedNormalCycles π q p)

theorem range_projectedNormalMap (π : Forms K n (2 * d) →ₗ[K] W)
    (q p : Fin r → Forms K n d) :
    (projectedNormalMap π q p).range = (projectedNormalCycles π q p).range := by
  exact range_descendCycleMap _ _ _ _

theorem projectedEndpointMultiplication_motion (π : Forms K n (2 * d) →ₗ[K] W)
    (q p : Fin r → Forms K n d) (ε : K) :
    projectedEndpointMultiplication π (q + ε • p) =
      projectedEndpointMultiplication π q + ε • projectedEndpointMultiplication π p := by
  simp only [projectedEndpointMultiplication, endpointMultiplication_motion,
    LinearMap.comp_add, LinearMap.comp_smul]

/-- The first-order rank gain for the actual projected polynomial complex. -/
theorem projected_normal_rank_gain_principal_open
    (π : Forms K n (2 * d) →ₗ[K] W) (q p : Fin r → Forms K n d) :
    ∃ D : MvPolynomial (Fin 1) K, eval 0 D ≠ 0 ∧
      ∀ ε : K, ε ≠ 0 → eval (fun _ => ε) D ≠ 0 →
        finrank K (projectedEndpointMultiplication π q).range +
          finrank K (projectedNormalMap π q p).range ≤
            finrank K (projectedEndpointMultiplication π (q + ε • p)).range := by
  let M := projectedEndpointMultiplication π q
  have hM : M.range.mkQ.comp M = 0 := by
    apply LinearMap.ext
    intro a
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨a, rfl⟩
  obtain ⟨D, hD, hprop⟩ := firstResponse_rank_gain_principal_open
    M (projectedEndpointMultiplication π p) M.range.mkQ hM
  refine ⟨D, hD, fun ε hε hDε => ?_⟩
  rw [range_projectedNormalMap, projectedEndpointMultiplication_motion]
  exact hprop ε hε hDε

/-- Projection-compatible version of Lemma C.5, with an unprojected conclusion. -/
theorem exists_projected_normal_homology_drop
    (π : Forms K n (2 * d) →ₗ[K] W) (q p : Fin r → Forms K n d)
    (hq : LinearIndependent K q) :
    ∃ ε : K, ε ≠ 0 ∧ LinearIndependent K (q + ε • p) ∧
      finrank K (EndpointHomology (q + ε • p)) +
          finrank K (projectedNormalMap π q p).range ≤
        finrank K (ProjectedEndpointHomology π q) := by
  classical
  obtain ⟨D, hD, hRank⟩ := projected_normal_rank_gain_principal_open π q p
  obtain ⟨E, hE, hInd⟩ := independent_motion_principal_open q p hq
  have hDE : ∃ a : Fin 1 → K, eval a (D * E) ≠ 0 :=
    ⟨0, by simpa using mul_ne_zero hD hE⟩
  have hX : ∃ a : Fin 1 → K, eval a (X (0 : Fin 1)) ≠ 0 := ⟨fun _ => 1, by simp⟩
  obtain ⟨a, haDE, haX⟩ := principal_opens_intersect hDE hX
  have ha : (fun _ : Fin 1 => a 0) = a := by ext i; fin_cases i; rfl
  have haD : eval (fun _ => a 0) D ≠ 0 := by
    rw [ha]
    exact (mul_ne_zero_iff.mp (by simpa using haDE)).1
  have haE : eval (fun _ => a 0) E ≠ 0 := by
    rw [ha]
    exact (mul_ne_zero_iff.mp (by simpa using haDE)).2
  have hε : a 0 ≠ 0 := by simpa using haX
  have hi := hInd (a 0) haE
  have hrank := hRank (a 0) hε haD
  have hbefore := (projectedEndpointMultiplication π q).finrank_range_add_finrank_ker
  have hafter := (projectedEndpointMultiplication π (q + a 0 • p)).finrank_range_add_finrank_ker
  have hHbefore := projected_homology_add_pairs π q hq
  have hHafter := projected_homology_add_pairs π (q + a 0 • p) hi
  have hproj := homology_le_projected π (q + a 0 • p) hi
  exact ⟨a 0, hε, hi, by omega⟩

end Froberg
