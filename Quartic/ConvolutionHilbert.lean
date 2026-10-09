module

public import Quartic.ConvolutionInverse
public import Quartic.ConvolutionConstantSlot
public import Quartic.Counts

@[expose] public section

/-!
# The actual convolution Hilbert function

The degree-two dual injects into the proved symmetric bivariate factor space.
The source and target dimensions give the opposite bound. Equality yields the
actual inverse-system equivalence and the degree-two Hilbert dimension. The
same dimension identities establish the absence of coefficient syzygies in
degrees zero, one, and two.
-/

namespace Quartic.ConvolutionHilbert

noncomputable section

open Quartic.ConvolutionPresentation Quartic.ConvolutionDual
open Quartic.ConvolutionInverse Quartic.ConvolutionConstantSlot
open Quartic.ConvolutionSymmetric

variable {K : Type*} [Field K] {t : ℕ}

/-- The actual degree-two inverse factor, as a bounded symmetric bivariate polynomial. -/
def quadraticFactorMap (ht : 2 ≤ t) :
    annihilator K t 1 →ₗ[K] symmetricSpace K (t - 1) :=
  ((erase (K := K) (j := 2)).toLinearMap.comp
    (inverseFactorLinear (K := K) (t := t) (j := 1))).codRestrict _ (by
      intro φ
      apply erase_mem_symmetricSpace t ht (inverseFactor φ)
      · intro i
        simpa [Nat.sub_sub] using (inverseFactor_bounds φ).2 i
      · exact inverseFactor_invariant φ swapVariables)

@[simp] theorem quadraticFactorMap_val (ht : 2 ≤ t) (φ : annihilator K t 1) :
    (quadraticFactorMap ht φ).val = erase (inverseFactor φ) := rfl

theorem quadraticFactorMap_injective (ht : 2 ≤ t) :
    Function.Injective (quadraticFactorMap (K := K) ht) := by
  intro φ ψ h
  apply inverseFactor_injective
  apply erase_injective_of_degree_none_zero (inverseFactor φ) (inverseFactor ψ)
  · have hnone := (inverseFactor_bounds φ).1
    omega
  · have hnone := (inverseFactor_bounds ψ).1
    omega
  · exact congrArg Subtype.val h

/-- Canonical duality preserves the dimension of the actual graded cokernel. -/
theorem annihilator_finrank (j : ℕ) :
    Module.finrank K (annihilator K t j) = Module.finrank K (Cokernel K t j) := by
  calc
    Module.finrank K (annihilator K t j) =
        Module.finrank K (Module.Dual K (Cokernel K t j)) :=
      (cokernelDualEquiv K t j).finrank_eq.symm
    _ = Module.finrank K (Cokernel K t j) := Subspace.dual_finrank_eq

theorem cokernel_degreeTwo_upper (ht : 2 ≤ t) :
    Module.finrank K (Cokernel K t 1) ≤ t.choose 2 := by
  have h := LinearMap.finrank_le_finrank_of_injective (quadraticFactorMap_injective (K := K) ht)
  rwa [annihilator_finrank, convolution_factor_finrank t ht] at h

/-- The source-target dimension difference is exactly `choose t 2`. -/
theorem quadratic_euler_count (t : ℕ) :
    3 * (t + 1).choose 2 = (t + 2) * t + t.choose 2 := by
  have h0 := Quartic.Counts.choose_two_scaled t
  have h1 := Quartic.Counts.choose_two_scaled (t + 1)
  push_cast at h1
  have h : (3 : ℤ) * ((t + 1).choose 2 : ℤ) =
      ((t : ℤ) + 2) * (t : ℤ) + (t.choose 2 : ℤ) := by nlinarith
  exact_mod_cast h

/-- The Euler identity also retains the actual linear-coefficient syzygy dimension. -/
theorem cokernel_degreeTwo_euler :
    Module.finrank K (Cokernel K t 1) = t.choose 2 +
      Module.finrank K (LinearMap.ker (presentation (K := K) (t := t) (j := 1))) := by
  have hq := (LinearMap.range (presentation (K := K) (t := t) (j := 1))).finrank_quotient_add_finrank
  have hk := (presentation (K := K) (t := t) (j := 1)).finrank_range_add_finrank_ker
  have hsource : Module.finrank K (Source K t 1) = (t + 2) * t := by
    simp [Source, Module.finrank_pi_fintype, Quartic.finrank_forms]
  have htarget : Module.finrank K (Target K t 2) = 3 * (t + 1).choose 2 := by
    simp [Target, Module.finrank_pi_fintype, Quartic.finrank_forms]
  change Module.finrank K (Cokernel K t 1) +
    Module.finrank K (LinearMap.range (presentation (K := K) (t := t) (j := 1))) =
      Module.finrank K (Target K t 2) at hq
  rw [htarget, quadratic_euler_count] at hq
  rw [hsource] at hk
  omega

/-- The degree-two Hilbert function of the actual three-row convolution module. -/
theorem cokernel_degreeTwo_finrank (ht : 2 ≤ t) :
    Module.finrank K (Cokernel K t 1) = t.choose 2 := by
  have hupper := cokernel_degreeTwo_upper (K := K) ht
  have heuler := cokernel_degreeTwo_euler (K := K) (t := t)
  omega

/-- There are no linear-coefficient syzygies in the actual presentation. -/
theorem presentation_degreeTwo_injective (ht : 2 ≤ t) :
    Function.Injective (presentation (K := K) (t := t) (j := 1)) := by
  apply LinearMap.ker_eq_bot.mp
  apply Submodule.finrank_eq_zero.mp
  have heuler := cokernel_degreeTwo_euler (K := K) (t := t)
  rw [cokernel_degreeTwo_finrank ht] at heuler
  omega

/-- The degree-two actual annihilator is the full symmetric polynomial factor space. -/
def quadraticFactorEquiv (ht : 2 ≤ t) :
    annihilator K t 1 ≃ₗ[K] symmetricSpace K (t - 1) := by
  have hd : Module.finrank K (annihilator K t 1) =
      Module.finrank K (symmetricSpace K (t - 1)) := by
    rw [annihilator_finrank, cokernel_degreeTwo_finrank ht, convolution_factor_finrank t ht]
  refine LinearEquiv.ofBijective (quadraticFactorMap (K := K) ht) ⟨quadraticFactorMap_injective ht, ?_⟩
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  exact (LinearMap.finrank_range_of_inj (quadraticFactorMap_injective ht)).trans hd

/-- The actual degree-two cokernel dual, identified canonically with the bounded
symmetric bivariate polynomial inverse system. -/
def cokernelDualQuadraticEquiv (ht : 2 ≤ t) :
    Module.Dual K (Cokernel K t 1) ≃ₗ[K] symmetricSpace K (t - 1) :=
  (cokernelDualEquiv K t 1).trans (quadraticFactorEquiv ht)

/-- Source and target have the same dimension at coefficient degree two. -/
theorem cubic_source_target_finrank :
    Module.finrank K (Source K t 2) = Module.finrank K (Target K t 3) := by
  have hs : Module.finrank K (Source K t 2) = (t + 2) * (t + 1).choose 2 := by
    simp [Source, Module.finrank_pi_fintype, Quartic.finrank_forms]
  have hd : Module.finrank K (Target K t 3) = 3 * (t + 2).choose 3 := by
    simp [Target, Module.finrank_pi_fintype, Quartic.finrank_forms]
  rw [hs, hd]
  simpa [Nat.add_assoc, mul_comm] using Nat.add_one_mul_choose_eq (t + 1) 2

/-- There are no quadratic-coefficient syzygies: the degree-three map is an isomorphism. -/
theorem presentation_degreeThree_injective :
    Function.Injective (presentation (K := K) (t := t) (j := 2)) :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (cubic_source_target_finrank (K := K) (t := t))).mpr
    (presentation_surjective_of_three_le (by omega))

/-- The complete checked Hilbert function, on the actual graded cokernels. -/
theorem convolution_hilbert (ht : 2 ≤ t) :
    Module.finrank K (DegreeZero K t) = 3 ∧
    Module.finrank K (Cokernel K t 0) = 2 * (t - 1) ∧
    Module.finrank K (Cokernel K t 1) = t.choose 2 ∧
    ∀ j : ℕ, 3 ≤ j + 1 → Module.finrank K (Cokernel K t j) = 0 :=
  ⟨degreeZero_finrank, cokernel_degreeOne_finrank (by omega),
    cokernel_degreeTwo_finrank ht, fun _ hj => cokernel_finrank_eq_zero_of_three_le hj⟩

/-- All three coefficient degrees singled out in `cv:hilbert` have no syzygies. -/
theorem no_coefficient_syzygies (ht : 2 ≤ t) (i : Fin 3) :
    Function.Injective (presentation (K := K) (t := t) (j := i.val)) := by
  fin_cases i
  · exact presentation_degreeOne_injective (by omega)
  · exact presentation_degreeTwo_injective ht
  · exact presentation_degreeThree_injective

end

end Quartic.ConvolutionHilbert
