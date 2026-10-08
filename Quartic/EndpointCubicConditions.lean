import Quartic.EndpointBlockConditions
import Quartic.CubicGeneric

/-!
# Cubic independence on the same endpoint block coefficients

The child-quadratic coordinates are a surjective linear projection of the
full mixed/child/motion coefficient space. Pulling back the cubic determinant
open and intersecting it with the block open therefore imposes all these
conditions on one common coefficient point, for every transfer dimension.
-/
noncomputable section
namespace Quartic.EndpointCubicConditions
open Module MvPolynomial UniformEndpoint SimultaneousBlockConditions AugmentedGeneric
open PolynomialBilinearCoordinates
variable {K : Type*} [Field K] {m c q : ℕ}

/-- Read the actual child tuple and express it in its finite basis coordinates. -/
def childCoordinates : (ParameterIndex m c q → K) →ₗ[K]
    (Fin (finrank K (Fin q → Forms K m 2)) → K) :=
  (coordinates K (Fin q → Forms K m 2)).toLinearMap.comp coefficientChild

/-- Every actual child tuple occurs in the full coefficient family. -/
theorem childCoordinates_surjective : Function.Surjective (childCoordinates (K := K) (m := m) (c := c) (q := q)) := by
  intro x
  refine ⟨encode 0 ((coordinates K (Fin q → Forms K m 2)).symm x) 0, ?_⟩
  change coordinates K (Fin q → Forms K m 2)
    (coefficientChild (encode 0 ((coordinates K (Fin q → Forms K m 2)).symm x) 0)) = x
  rw [coefficientChild_encode, LinearEquiv.apply_symm_apply]

/-- Pull the cubic polynomial back to the shared mixed/child/motion coordinates. -/
def childPullback (P : MvPolynomial (Fin (finrank K (Fin q → Forms K m 2))) K) :
    MvPolynomial (ParameterIndex m c q) K :=
  MiddleCoordinates.substituteLinear childCoordinates P

@[simp] theorem eval_childPullback (P : MvPolynomial (Fin (finrank K (Fin q → Forms K m 2))) K)
    (a : ParameterIndex m c q → K) :
    eval a (childPullback P) = eval (coordinates K (Fin q → Forms K m 2) (coefficientChild a)) P :=
  MiddleCoordinates.eval_substituteLinear childCoordinates a P

/-- Every endpoint block open can be intersected with the actual cubic open
without changing any of its mixed coefficients, quadrics, or motions. -/
theorem generic_blocks_and_cubic [Infinite K]
    (hblocks : GenericBlockConditions K m c q) (hm : 3 ≤ m)
    (hq : m*q ≤ (m+2).choose 3) :
    ∃ D : MvPolynomial (ParameterIndex m c q) K,
      (∃ a, eval a D ≠ 0) ∧ ∀ a, eval a D ≠ 0 →
        BlockConditions a ∧ Function.Injective (CubicGeneric.cubicMap (coefficientChild a)) ∧
          finrank K (CubicGeneric.CubicQuotient (coefficientChild a)) = (m+2).choose 3 - m*q := by
  classical
  obtain ⟨B, ⟨b, hb⟩, hB⟩ := hblocks
  obtain ⟨C, ⟨Q, hQ⟩, hC⟩ := CubicGeneric.generic_cubic_independence (K := K) hm hq
  have hB0 : B ≠ 0 := by intro hz; simp [hz] at hb
  have hC0 : childPullback (c := c) C ≠ 0 := by
    intro hz
    have he : eval (encode (0 : Fin c → MiddleCoordinates.Mixed K m) Q 0) (childPullback C) ≠ 0 := by
      simpa only [eval_childPullback, coefficientChild_encode] using hQ
    simp [hz] at he
  obtain ⟨a₀, ha₀⟩ := nonempty_principal_intersection
    (![B, childPullback C] : Fin 2 → MvPolynomial (ParameterIndex m c q) K)
    (by intro i; fin_cases i <;> assumption)
  refine ⟨B * childPullback C, ⟨a₀, ?_⟩, ?_⟩
  · rw [map_mul]
    exact mul_ne_zero (ha₀ 0) (ha₀ 1)
  · intro a ha
    rw [map_mul, mul_ne_zero_iff] at ha
    have hcubic := hC (coefficientChild a) (by simpa only [eval_childPullback] using ha.2)
    exact ⟨hB a ha.1, hcubic.2⟩

/-- Simultaneous actual block conditions and cubic independence at both
canonical endpoints, for every child dimension m≥28. -/
theorem generic_endpoint_blocks_and_cubic [Infinite K] (m : ℕ) (hm : 28 ≤ m)
    (upper : Bool) (h2 : (2 : K) ≠ 0) :
    ∃ D : MvPolynomial (ParameterIndex m (mixedCount m upper) (upperEndpoint m)) K,
      (∃ a, eval a D ≠ 0) ∧ ∀ a, eval a D ≠ 0 →
        BlockConditions a ∧ Function.Injective (CubicGeneric.cubicMap (coefficientChild a)) ∧
          finrank K (CubicGeneric.CubicQuotient (coefficientChild a)) =
            (m+2).choose 3 - m*upperEndpoint m := by
  have hs := EndpointBlockConditions.structural_counts m hm upper
  have hq : m * upperEndpoint m ≤ (m+2).choose 3 := by
    have h := hs.2.2.1
    unfold Counts.b3 at h
    exact_mod_cast h
  exact generic_blocks_and_cubic (EndpointBlockConditions.generic_block_conditions m hm upper h2)
    (by omega) hq

end Quartic.EndpointCubicConditions
