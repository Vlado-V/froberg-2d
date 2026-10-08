import Froberg.UniversalAction
import Froberg.CentralScalar
import Froberg.GenericFieldDescent
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! # The actual generic endpoint divisibility theorem

The proof constructs the coefficient action and its invariant universal
image.  The determinant-line argument gives its central weight, and
field-extension invariance descends the result to every field of
characteristic zero.
-/

noncomputable section
namespace Froberg
open Matrix Module MvPolynomial

variable {K : Type*} [Field K] [Infinite K] {n d r : ℕ}

theorem central_pair_coefficient_action (ζ : K) (hζ : ζ ≠ 0)
    (hn : ζ ^ n = 1) (hr : (ζ ^ d) ^ r = 1) :
    (universalTargetAction (d := d)).coeff (scalarSL n ζ hn, scalarSL r (ζ ^ d) hr) = 1 := by
  let z := (scalarSL n ζ hn, scalarSL r (ζ ^ d) hr)
  have hz : coefficientPointRepresentation z = (1 : Module.End K (CoefficientIndex n d r → K)) :=
    central_pair_point_representation ζ hζ hn hr
  have hzi (a : CoefficientIndex n d r → K) : coefficientPointRepresentation z⁻¹ a = a := by
    have hh := Representation.self_inv_apply coefficientPointRepresentation z a
    rwa [hz, Module.End.one_apply] at hh
  apply AlgEquiv.ext
  intro P
  apply MvPolynomial.funext
  intro a
  change eval a (representationPullback coefficientPointRepresentation z P) = eval a P
  rw [representationPullback_eval, hzi]

theorem central_pair_target_matrix (ζ : K) (hn : ζ ^ n = 1) (hr : (ζ ^ d) ^ r = 1) :
    (universalTargetAction (d := d)).matrix (scalarSL n ζ hn, scalarSL r (ζ ^ d) hr) =
      (C (ζ ^ (2 * d)) : MvPolynomial (CoefficientIndex n d r) K) • (1 : Matrix (Fin (finrank K (Forms K n (2 * d))))
        (Fin (finrank K (Forms K n (2 * d)))) (MvPolynomial (CoefficientIndex n d r) K)) := by
  classical
  have ht : endpointTargetCoordinates (scalarSL n ζ hn, scalarSL r (ζ ^ d) hr) =
      (ζ ^ (2 * d)) • (1 : Module.End K (Fin (finrank K (Forms K n (2 * d))) → K)) := by
    apply LinearMap.ext
    intro v
    change (Module.finBasis K (Forms K n (2 * d))).equivFun
      (slFormsEquiv (scalarSL n ζ hn) (2 * d)
        ((Module.finBasis K (Forms K n (2 * d))).equivFun.symm v)) = _
    rw [scalarSL_forms, map_smul, LinearEquiv.apply_symm_apply]
    rfl
  change (LinearMap.toMatrix' (endpointTargetCoordinates
    (scalarSL n ζ hn, scalarSL r (ζ ^ d) hr))).map C = _
  rw [ht, map_smul, Module.End.one_eq_id, LinearMap.toMatrix'_id]
  apply Matrix.ext
  intro i j
  by_cases hij : i = j <;> simp [Matrix.smul_apply, Matrix.one_apply, hij]

/-- Over a field containing the required root of unity, the divisor
follows from the actual universal image, with no rank-divisibility premise. -/
theorem genericCokernel_divisibility_of_primitiveRoot (hn : 0 < n)
    (ζ : K) (hζ : IsPrimitiveRoot ζ (Nat.gcd n (d * r))) :
    Nat.gcd n (d * r) ∣ (2 * d) * genericCokernel K n d r := by
  classical
  let R := MvPolynomial (CoefficientIndex n d r) K
  let F := FractionRing R
  let φ : R →+* F := algebraMap R F
  let ι : K →+* F := φ.comp C
  have hg : 0 < Nat.gcd n (d * r) := Nat.gcd_pos_of_pos_left _ hn
  have hz0 : ζ ≠ 0 := hζ.ne_zero hg.ne'
  have hzn : ζ ^ n = 1 := (hζ.pow_eq_one_iff_dvd n).mpr (Nat.gcd_dvd_left _ _)
  have hzr : (ζ ^ d) ^ r = 1 := by
    rw [← pow_mul]
    exact (hζ.pow_eq_one_iff_dvd (d * r)).mpr (Nat.gcd_dvd_right _ _)
  let z := (scalarSL n ζ hzn, scalarSL r (ζ ^ d) hzr)
  let M := (universalMultiplicationMatrix K n d r).map φ
  have hroot : IsPrimitiveRoot (ι ζ) (Nat.gcd n (d * r)) :=
    hζ.map_of_injective ι.injective
  have hmat : ((universalTargetAction (d := d)).matrix z).map φ =
      (ι ζ) ^ (2 * d) • (1 : Matrix (Fin (finrank K (Forms K n (2 * d))))
        (Fin (finrank K (Forms K n (2 * d)))) F) := by
    rw [central_pair_target_matrix]
    apply Matrix.ext
    intro i j
    by_cases hij : i = j <;> simp [Matrix.smul_apply, Matrix.one_apply, ι, φ, hij]
  have himage := invariant_subspace_weight_divisibility (universalTargetAction (d := d))
    (LinearMap.range M.mulVecLin)
    (fun g w hw => universalMultiplication_image_invariant g w hw)
    z (central_pair_coefficient_action ζ hz0 hzn hzr) hroot hmat
  exact genericCokernel_divisibility_of_fraction_rank K n d r F hn himage

/-- The desired divisor of the actual generic cokernel over every
characteristic-zero field. -/
theorem genericCokernel_divisibility [CharZero K] (hn : 0 < n) :
    Nat.gcd n (d * r) ∣ (2 * d) * genericCokernel K n d r := by
  let L := AlgebraicClosure K
  have hg : Nat.gcd n (d * r) ≠ 0 := (Nat.gcd_pos_of_pos_left _ hn).ne'
  letI : NeZero (Nat.gcd n (d * r) : L) := ⟨by exact_mod_cast hg⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L (Nat.gcd n (d * r))
  have h := genericCokernel_divisibility_of_primitiveRoot (K := L) hn ζ hζ
  rwa [← GenericFieldDescent.genericCokernel_baseChange (algebraMap K L) hn] at h

/-- The desired divisor of the actual generic homology defect. -/
theorem genericHomology_divisibility [CharZero K] (hn : 0 < n)
    (hr : r ≤ (n + d - 1).choose d) :
    Nat.gcd n (d * r) ∣ (2 * d) * genericHomology K n d r :=
  genericHomology_divisibility_of_genericCokernel hn hr (genericCokernel_divisibility hn)

end Froberg
