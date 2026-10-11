/-
Copyright (c) 2026 Vlado Vojdanovski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vlado Vojdanovski
-/
module

public import Quartic.ThreeBlockOmega

/-!
# The correction of the distinguished pure square

The distinguished square has an explicit preimage under the four pure
quadrics. Its fourth coefficient supplies a direction absent from the three
ordinary pure homology classes. After contraction this direction has scalar
`ω * (ω + 1)`, which is nonzero for the admissible pencil parameter in every
characteristic.
-/

@[expose] public section

noncomputable section

namespace Quartic.ExceptionalSquareCorrection

open MvPolynomial ThreeBlock

variable {K : Type*} [CommRing K]

def correction (ω : K) : Fin 4 → ThreeBlock.Poly K :=
  ![-C ((ω + 1) ^ 2) * quadrics 0,
    -C (ω ^ 2) * quadrics 1,
    -quadrics 2,
    C (ω ^ 2) * x ^ 2 + y ^ 2]

/-- An exact source correction for the square of the marked pure direction. -/
theorem square_identity (ω : K) :
    ThreeBlock.relation (correction ω) = (C ω * x ^ 2 - y ^ 2) ^ 2 := by
  simp [correction, ThreeBlock.relation, quadrics, map_add, map_pow]
  ring

/-- The fourth coefficient reduces to these two pure-quotient coordinates. -/
theorem last_reduction (ω : K) :
    ThreeBlock.quadraticReduction (correction ω 3) = ![ω ^ 2, 1] := by
  have hred (a : K) :
      ThreeBlock.quadraticReduction (C a * x ^ 2 + y ^ 2) = ![a, 1] := by
    funext i
    fin_cases i <;>
      norm_num [ThreeBlock.quadraticReduction, coeff_C_mul, x, y, MvPolynomial.X,
        pow_two, monomial_mul_monomial, coeff_monomial, Finsupp.ext_iff,
        Fin.forall_fin_succ]
  exact hred (ω ^ 2)

theorem fourth_contraction (ω : K) :
    ThreeBlockOmega.ell ω (ThreeBlock.quadraticReduction (correction ω 3)) =
      ω * (ω + 1) := by
  rw [last_reduction]
  simp [ThreeBlockOmega.ell]
  ring

theorem ordinary_fourth_coefficient (ω : K) (t : Fin 3 → K) :
    ThreeBlockOmega.scalarCoefficients ω t 3 = 0 := by
  simp [ThreeBlockOmega.scalarCoefficients, ThreeBlock.coefficientMaps, ThreeBlockOmega.ell]

theorem fourth_contraction_ne_zero [NoZeroDivisors K] (ω : K)
    (hω : ω ≠ 0) (hω1 : ω ≠ -1) :
    ThreeBlockOmega.ell ω (ThreeBlock.quadraticReduction (correction ω 3)) ≠ 0 := by
  rw [fourth_contraction]
  apply mul_ne_zero hω
  intro h
  exact hω1 (eq_neg_of_add_eq_zero_left h)

end Quartic.ExceptionalSquareCorrection
