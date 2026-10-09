module

public import Froberg.GenericDimensions
public import Froberg.MatrixRankSpecialization
public import Froberg.EulerDivisibility

@[expose] public section

/-!
# The actual generic multiplication rank over a fraction field

The universal matrix is built from the coefficient-linear multiplication
map in `Generic.lean`.  Its fraction-field rank is identified with the
attained generic cokernel dimension, rather than postulated to be generic.
-/

noncomputable section

namespace Froberg

open Module Matrix

variable (K : Type*) [Field K] (n d r : ℕ)

/-- The actual universal degree-`2d` multiplication matrix. -/
def universalMultiplicationMatrix :
    Matrix (Fin (finrank K (Forms K n (2 * d))))
      (Fin (finrank K (Fin r → Forms K n d)))
      (MvPolynomial (CoefficientIndex n d r) K) := by
  classical
  let bs := Module.finBasis K (Fin r → Forms K n d)
  let bt := Module.finBasis K (Forms K n (2 * d))
  let L := (LinearMap.toMatrix bs bt).toLinearMap.comp
    (coefficientMultiplicationLinear (K := K) (n := n) (d := d) (r := r))
  exact fun i j => polynomialOfLinear ((LinearMap.proj j).comp ((LinearMap.proj i).comp L))

/-- Evaluation recovers the matrix of the actual multiplication map. -/
theorem universalMultiplicationMatrix_eval (a : CoefficientIndex n d r → K) :
    (universalMultiplicationMatrix K n d r).map (MvPolynomial.eval a) =
      LinearMap.toMatrix (Module.finBasis K (Fin r → Forms K n d))
        (Module.finBasis K (Forms K n (2 * d)))
        (endpointMultiplication (coefficientForms K n d r a)) := by
  classical
  ext i j
  change MvPolynomial.eval a (polynomialOfLinear _) = _
  rw [eval_polynomialOfLinear]
  rfl

/-- The evaluated universal matrix has the actual multiplication rank. -/
theorem universalMultiplicationMatrix_rank_eval (a : CoefficientIndex n d r → K) :
    ((universalMultiplicationMatrix K n d r).map (MvPolynomial.eval a)).rank =
      finrank K (LinearMap.range (endpointMultiplication (coefficientForms K n d r a))) := by
  classical
  rw [universalMultiplicationMatrix_eval]
  rw [Matrix.rank_eq_finrank_range_toLin _ (Module.finBasis K (Forms K n (2 * d)))
    (Module.finBasis K (Fin r → Forms K n d)), Matrix.toLin_toMatrix]

variable [Infinite K]

/-- The pointwise minimum defining the generic cokernel equals the
codimension of the universal matrix over the polynomial fraction field. -/
theorem genericCokernel_add_fraction_rank
    (F : Type*) [Field F]
    [Algebra (MvPolynomial (CoefficientIndex n d r) K) F]
    [IsFractionRing (MvPolynomial (CoefficientIndex n d r) K) F]
    (hn : 0 < n) :
    genericCokernel K n d r +
      ((universalMultiplicationMatrix K n d r).map
        (algebraMap (MvPolynomial (CoefficientIndex n d r) K) F)).rank =
      (n + 2 * d - 1).choose (2 * d) := by
  classical
  let M := universalMultiplicationMatrix K n d r
  obtain ⟨a, ha⟩ := exists_specialization_rank_eq_fraction_rank (F := F) M
  obtain ⟨a₀, ha₀⟩ := genericCokernel_attained K n d r
  have hrow (b : CoefficientIndex n d r → K) :
      coefficientCokernel K n d r b + (M.map (MvPolynomial.eval b)).rank =
        (n + 2 * d - 1).choose (2 * d) := by
    rw [show M = universalMultiplicationMatrix K n d r from rfl,
      universalMultiplicationMatrix_rank_eval]
    exact endpoint_quotient_add_rank hn (coefficientForms K n d r b)
  have hb := hrow a
  rw [ha] at hb
  have hb₀ := hrow a₀
  rw [ha₀] at hb₀
  have hmin := genericCokernel_le K n d r a
  have hmax := specialization_rank_le_fraction_rank (F := F) M a₀
  change genericCokernel K n d r + (M.map _).rank = _
  omega

/-- A central-weight divisor of the actual universal image rank gives
the same divisor of the actual generic cokernel dimension. -/
theorem genericCokernel_divisibility_of_fraction_rank
    (F : Type*) [Field F]
    [Algebra (MvPolynomial (CoefficientIndex n d r) K) F]
    [IsFractionRing (MvPolynomial (CoefficientIndex n d r) K) F]
    (hn : 0 < n)
    (himage : Nat.gcd n (d * r) ∣ (2 * d) *
      ((universalMultiplicationMatrix K n d r).map
        (algebraMap (MvPolynomial (CoefficientIndex n d r) K) F)).rank) :
    Nat.gcd n (d * r) ∣ (2 * d) * genericCokernel K n d r := by
  have htotal := (Nat.gcd_dvd_left n (d * r)).trans
    (variables_dvd_degree_mul_monomials n (2 * d))
  have hdim := genericCokernel_add_fraction_rank K n d r F hn
  rw [← hdim, Nat.mul_add] at htotal
  exact (Nat.dvd_add_iff_left himage).mpr htotal

end Froberg
