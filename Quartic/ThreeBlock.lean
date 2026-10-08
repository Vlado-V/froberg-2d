import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Explicit identities for the three-variable quadratic block

This file formalizes the polynomial identities and the finite coordinate maps
in `source/three_block.tex`. The generic Grassmannian statements and homology
dimension arguments are not consequences asserted by this file.
-/

noncomputable section

namespace Quartic.ThreeBlock

open MvPolynomial

variable {K : Type*} [CommRing K]

abbrev Poly (K : Type*) [CommRing K] := MvPolynomial (Fin 3) K

def x : Poly K := X 0
def y : Poly K := X 1
def z : Poly K := X 2

def quadrics : Fin 4 → Poly K :=
  ![x * y, x * z, y * z, x ^ 2 + y ^ 2 + z ^ 2]

/-- Polynomial multiplication by the four generators. -/
def relation (a : Fin 4 → Poly K) : Poly K :=
  a 0 * quadrics 0 + a 1 * quadrics 1 + a 2 * quadrics 2 + a 3 * quadrics 3

def cubicCycle₁ : Fin 4 → Poly K := ![z, -y, 0, 0]
def cubicCycle₂ : Fin 4 → Poly K := ![z, 0, -x, 0]

theorem cubicCycle₁_is_cycle : relation (cubicCycle₁ (K := K)) = 0 := by
  simp [relation, cubicCycle₁, quadrics]
  ring

theorem cubicCycle₂_is_cycle : relation (cubicCycle₂ (K := K)) = 0 := by
  simp [relation, cubicCycle₂, quadrics]
  ring

def quarticCycle₁ : Fin 4 → Poly K := ![z ^ 2, -(y * z), 0, 0]
def quarticCycle₂ : Fin 4 → Poly K := ![-(y * z), y ^ 2, 0, 0]
def quarticCycle₃ : Fin 4 → Poly K := ![-(x * z), 0, x ^ 2, 0]

theorem quarticCycle₁_is_cycle : relation (quarticCycle₁ (K := K)) = 0 := by
  simp [relation, quarticCycle₁, quadrics]
  ring

theorem quarticCycle₂_is_cycle : relation (quarticCycle₂ (K := K)) = 0 := by
  simp [relation, quarticCycle₂, quadrics]
  ring

theorem quarticCycle₃_is_cycle : relation (quarticCycle₃ (K := K)) = 0 := by
  simp [relation, quarticCycle₃, quadrics]
  ring

/-- Explicit expressions placing the three pure cubes in the quadratic ideal. -/
theorem x_cube_identity :
    (x : Poly K) ^ 3 = x * quadrics 3 - y * quadrics 0 - z * quadrics 1 := by
  simp [quadrics]
  ring

theorem y_cube_identity :
    (y : Poly K) ^ 3 = y * quadrics 3 - x * quadrics 0 - z * quadrics 2 := by
  simp [quadrics]
  ring

theorem z_cube_identity :
    (z : Poly K) ^ 3 = z * quadrics 3 - x * quadrics 1 - y * quadrics 2 := by
  simp [quadrics]
  ring

def blockIdeal : Ideal (Poly K) := Ideal.span (Set.range quadrics)

theorem quadric_mem_ideal (i : Fin 4) : quadrics (K := K) i ∈ blockIdeal :=
  Ideal.subset_span ⟨i, rfl⟩

theorem x_cube_mem_ideal : (x : Poly K) ^ 3 ∈ blockIdeal := by
  rw [x_cube_identity]
  exact Ideal.sub_mem _ (Ideal.sub_mem _
    (Ideal.mul_mem_left _ _ (quadric_mem_ideal 3))
    (Ideal.mul_mem_left _ _ (quadric_mem_ideal 0)))
    (Ideal.mul_mem_left _ _ (quadric_mem_ideal 1))

theorem y_cube_mem_ideal : (y : Poly K) ^ 3 ∈ blockIdeal := by
  rw [y_cube_identity]
  exact Ideal.sub_mem _ (Ideal.sub_mem _
    (Ideal.mul_mem_left _ _ (quadric_mem_ideal 3))
    (Ideal.mul_mem_left _ _ (quadric_mem_ideal 0)))
    (Ideal.mul_mem_left _ _ (quadric_mem_ideal 2))

theorem z_cube_mem_ideal : (z : Poly K) ^ 3 ∈ blockIdeal := by
  rw [z_cube_identity]
  exact Ideal.sub_mem _ (Ideal.sub_mem _
    (Ideal.mul_mem_left _ _ (quadric_mem_ideal 3))
    (Ideal.mul_mem_left _ _ (quadric_mem_ideal 1)))
    (Ideal.mul_mem_left _ _ (quadric_mem_ideal 2))

/-- The ten monomials of degree three, in lexicographic order. -/
def cubicMonomials : Fin 10 → Poly K :=
  ![x ^ 3, x ^ 2 * y, x ^ 2 * z, x * y ^ 2, x * y * z,
    x * z ^ 2, y ^ 3, y ^ 2 * z, y * z ^ 2, z ^ 3]

/-- Explicit preimages under multiplication by the four quadrics. -/
def cubicPreimages : Fin 10 → Fin 4 → Poly K :=
  ![![-y, -z, 0, x], ![x, 0, 0, 0], ![0, x, 0, 0], ![y, 0, 0, 0],
    ![z, 0, 0, 0], ![0, z, 0, 0], ![-x, 0, -z, y], ![0, 0, y, 0],
    ![0, 0, z, 0], ![0, -x, -y, z]]

theorem cubicPreimages_spec (i : Fin 10) :
    relation (cubicPreimages (K := K) i) = cubicMonomials i := by
  fin_cases i <;> simp [relation, cubicPreimages, cubicMonomials, quadrics] <;> ring

theorem relation_mem_ideal (a : Fin 4 → Poly K) : relation a ∈ blockIdeal := by
  exact Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _
    (Ideal.mul_mem_left _ _ (quadric_mem_ideal 0))
    (Ideal.mul_mem_left _ _ (quadric_mem_ideal 1)))
    (Ideal.mul_mem_left _ _ (quadric_mem_ideal 2)))
    (Ideal.mul_mem_left _ _ (quadric_mem_ideal 3))

theorem cubicMonomials_mem_ideal (i : Fin 10) :
    cubicMonomials (K := K) i ∈ blockIdeal := by
  rw [← cubicPreimages_spec]
  exact relation_mem_ideal _

/-- Coordinates of a linear polynomial in the three variables. -/
def linearForm (a : Fin 3 → K) : Poly K :=
  C (a 0) * x + C (a 1) * y + C (a 2) * z

/-- Exponent vectors for the ten cubic monomials. -/
def cubicExponents : Fin 10 → (Fin 3 →₀ ℕ) :=
  ![Finsupp.single 0 3, Finsupp.single 0 2 + Finsupp.single 1 1,
    Finsupp.single 0 2 + Finsupp.single 2 1,
    Finsupp.single 0 1 + Finsupp.single 1 2,
    Finsupp.single 0 1 + Finsupp.single 1 1 + Finsupp.single 2 1,
    Finsupp.single 0 1 + Finsupp.single 2 2, Finsupp.single 1 3,
    Finsupp.single 1 2 + Finsupp.single 2 1,
    Finsupp.single 1 1 + Finsupp.single 2 2, Finsupp.single 2 3]

/-- The cubic multiplication matrix, on the twelve coefficients of four linear forms. -/
def cubicCoefficientMap (a : Fin 4 → Fin 3 → K) : Fin 10 → K :=
  ![a 3 0, a 0 0 + a 3 1, a 1 0 + a 3 2, a 0 1 + a 3 0,
    a 0 2 + a 1 1 + a 2 0, a 1 2 + a 3 0, a 3 1,
    a 2 1 + a 3 2, a 2 2 + a 3 1, a 3 2]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
/-- The coordinate matrix agrees with multiplication in `MvPolynomial`. -/
theorem cubicCoefficientMap_spec (a : Fin 4 → Fin 3 → K) (j : Fin 10) :
    (relation (fun i => linearForm (a i))).coeff (cubicExponents j) =
      cubicCoefficientMap a j := by
  fin_cases j <;>
    norm_num [relation, linearForm, quadrics, cubicExponents, cubicCoefficientMap,
      x, y, z, MvPolynomial.X, pow_two, add_mul, mul_add, mul_assoc, coeff_C_mul,
      monomial_mul_monomial, coeff_monomial, Finsupp.ext_iff, Fin.forall_fin_succ]

/-- The coordinates of a linear combination of the two cubic relations. -/
def cubicKernelElement (r s : K) : Fin 4 → Fin 3 → K :=
  ![![0, 0, r + s], ![0, -r, 0], ![-s, 0, 0], ![0, 0, 0]]

theorem cubicCoefficientMap_kernel (a : Fin 4 → Fin 3 → K) :
    cubicCoefficientMap a = 0 ↔ ∃ r s, a = cubicKernelElement r s := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    have h3 := congrFun h 3
    have h4 := congrFun h 4
    have h5 := congrFun h 5
    have h6 := congrFun h 6
    have h7 := congrFun h 7
    have h8 := congrFun h 8
    have h9 := congrFun h 9
    simp [cubicCoefficientMap] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
    simp only [h0, h6, h9, add_zero] at h1 h2 h3 h5 h7 h8
    refine ⟨-a 1 1, -a 2 0, ?_⟩
    have hc : a 0 2 = -a 1 1 + -a 2 0 := by
      calc
        a 0 2 = (a 0 2 + a 1 1 + a 2 0) - a 1 1 - a 2 0 := by ring
        _ = -a 1 1 + -a 2 0 := by rw [h4]; ring
    funext i j
    fin_cases i <;> fin_cases j <;>
      simp [cubicKernelElement, h0, h1, h2, h3, h5, h6, h7, h8, h9, hc]
  · rintro ⟨r, s, rfl⟩
    funext j
    fin_cases j <;> simp [cubicCoefficientMap, cubicKernelElement]

theorem cubicKernelElement_injective :
    Function.Injective (fun rs : K × K => cubicKernelElement rs.1 rs.2) := by
  intro a b h
  apply Prod.ext
  · have hr := congrFun (congrFun h 1) 1
    simpa [cubicKernelElement] using hr
  · have hs := congrFun (congrFun h 2) 0
    simpa [cubicKernelElement] using hs

theorem cubicKernelElement_linearForms (r s : K) :
    (fun i => linearForm (cubicKernelElement r s i)) =
      (fun i => C r * cubicCycle₁ i + C s * cubicCycle₂ i) := by
  funext i
  fin_cases i <;>
    simp [linearForm, cubicKernelElement, cubicCycle₁, cubicCycle₂, map_add, map_neg]
  ring

/-- Every cubic relation has exactly the two displayed free parameters. -/
theorem cubicKernel_basis (a : Fin 4 → Fin 3 → K) :
    relation (fun i => linearForm (a i)) = 0 ↔
      ∃ r s, a = cubicKernelElement r s := by
  constructor
  · intro h
    apply (cubicCoefficientMap_kernel a).mp
    funext j
    rw [← cubicCoefficientMap_spec, h]
    simp
  · rintro ⟨r, s, rfl⟩
    simp [relation, linearForm, cubicKernelElement, quadrics, map_add, map_neg]
    ring

/-- These are the four coefficient maps in the manuscript's displayed bases. -/
def coefficientMaps (t : Fin 3 → K) : Fin 4 → Fin 2 → K :=
  ![![-t 0, -t 0], ![0, t 1], ![t 2, 0], ![0, 0]]

/-- The coordinates of the quadratic class modulo the four generators.
On homogeneous quadratics, the mixed monomials vanish and `z² = -x²-y²`. -/
def quadraticReduction (p : Poly K) : Fin 2 → K :=
  ![p.coeff (Finsupp.single 0 2) - p.coeff (Finsupp.single 2 2),
    p.coeff (Finsupp.single 1 2) - p.coeff (Finsupp.single 2 2)]

theorem quadraticReduction_quadric (i : Fin 4) :
    quadraticReduction (quadrics (K := K) i) = 0 := by
  funext j
  fin_cases i <;> fin_cases j <;>
    norm_num [quadraticReduction, quadrics, x, y, z, MvPolynomial.X,
      pow_two, monomial_mul_monomial, coeff_monomial, Finsupp.ext_iff,
      Fin.forall_fin_succ]

/-- A linear combination of the three displayed quartic cycles. -/
def quarticCombination (t : Fin 3 → K) (a : Fin 4) : Poly K :=
  C (t 0) * quarticCycle₁ a + C (t 1) * quarticCycle₂ a + C (t 2) * quarticCycle₃ a

theorem quarticCombination_is_cycle (t : Fin 3 → K) :
    relation (quarticCombination t) = 0 := by
  simp [relation, quarticCombination, quarticCycle₁, quarticCycle₂, quarticCycle₃,
    quadrics]
  ring

/-- The coefficient maps are the actual reductions of the polynomial cycles. -/
theorem quarticCombination_reduction (t : Fin 3 → K) (a : Fin 4) :
    quadraticReduction (quarticCombination t a) = coefficientMaps t a := by
  funext j
  fin_cases a <;> fin_cases j <;>
    norm_num [quadraticReduction, quarticCombination, quarticCycle₁, quarticCycle₂,
      quarticCycle₃, coefficientMaps, coeff_C_mul, x, y, z, MvPolynomial.X,
      pow_two, monomial_mul_monomial, coeff_monomial, Finsupp.ext_iff,
      Fin.forall_fin_succ]

/-- The six elementary Koszul boundaries, with constant coefficients in degree four. -/
def koszulBoundary (b : Fin 6 → K) : Fin 4 → Poly K :=
  ![C (b 0) * quadrics 1 + C (b 1) * quadrics 2 + C (b 2) * quadrics 3,
    -C (b 0) * quadrics 0 + C (b 3) * quadrics 2 + C (b 4) * quadrics 3,
    -C (b 1) * quadrics 0 - C (b 3) * quadrics 1 + C (b 5) * quadrics 3,
    -C (b 2) * quadrics 0 - C (b 4) * quadrics 1 - C (b 5) * quadrics 2]

theorem koszulBoundary_is_cycle (b : Fin 6 → K) :
    relation (koszulBoundary b) = 0 := by
  simp [relation, koszulBoundary]
  ring

theorem koszulBoundary_reduction (b : Fin 6 → K) (a : Fin 4) :
    quadraticReduction (koszulBoundary b a) = 0 := by
  funext j
  fin_cases a <;> fin_cases j <;>
    norm_num [quadraticReduction, koszulBoundary, quadrics, neg_mul, coeff_C_mul,
      x, y, z, MvPolynomial.X, pow_two, monomial_mul_monomial, coeff_monomial,
      Finsupp.ext_iff, Fin.forall_fin_succ]

theorem coefficientMaps_injective : Function.Injective (coefficientMaps (K := K)) := by
  intro t r h
  funext i
  fin_cases i
  · have h0 := congrFun (congrFun h 0) 0
    simpa [coefficientMaps] using h0
  · have h1 := congrFun (congrFun h 1) 1
    simpa [coefficientMaps] using h1
  · have h2 := congrFun (congrFun h 2) 0
    simpa [coefficientMaps] using h2

/-- No nonzero combination of the three quartic cycles is a Koszul boundary. -/
theorem quarticCycles_independent_mod_boundaries (t : Fin 3 → K) (b : Fin 6 → K)
    (h : quarticCombination t = koszulBoundary b) : t = 0 := by
  apply coefficientMaps_injective
  funext a
  rw [← quarticCombination_reduction, h, koszulBoundary_reduction]
  funext j
  fin_cases a <;> fin_cases j <;> simp [coefficientMaps]

def ell (p : Fin 2 → K) : K := p 0 + p 1

def scalarCoefficients (t : Fin 3 → K) : Fin 4 → K :=
  fun a => ell (coefficientMaps t a)

theorem scalarCoefficients_formula (t : Fin 3 → K) :
    scalarCoefficients t = ![-2 * t 0, t 1, t 2, 0] := by
  funext i
  fin_cases i <;> simp [scalarCoefficients, coefficientMaps, ell]
  ring

/-- The first three rows give the determinant stated in the manuscript. -/
theorem scalar_minor_det :
    Matrix.det (!![-2, 0, 0; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K) = -2 := by
  simp [Matrix.det_fin_three]

theorem scalarCoefficients_injective [NoZeroDivisors K]
    (h2 : (2 : K) ≠ 0) : Function.Injective (scalarCoefficients (K := K)) := by
  intro a b h
  rw [scalarCoefficients_formula, scalarCoefficients_formula] at h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2' := congrFun h 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] at h0 h1 h2'
  have ha : a 0 = b 0 := mul_left_cancel₀ (neg_ne_zero.mpr h2) h0
  funext i
  fin_cases i
  · exact ha
  · exact h1
  · exact h2'

theorem ell_marked : ell (![1, -1] : Fin 2 → K) = 0 := by
  simp [ell]

theorem ell_kernel (p : Fin 2 → K) :
    ell p = 0 ↔ ∃ a : K, p = ![a, -a] := by
  constructor
  · intro h
    refine ⟨p 0, ?_⟩
    funext i
    fin_cases i
    · rfl
    · exact eq_neg_of_add_eq_zero_right h
  · rintro ⟨a, rfl⟩
    simp [ell]

/-- The block matrix `D` written as an explicit map on six coordinates. -/
def diagonalMap (a : Fin 6 → K) : Fin 6 → K :=
  ![a 0 - a 2, -a 2, -a 2 + a 3 - a 5,
    a 1 - a 2 - a 5, -a 5, a 4 - a 5]

def diagonalInverse (t : Fin 6 → K) : Fin 6 → K :=
  ![t 0 - t 1, t 3 - t 1 - t 4, -t 1,
    t 2 - t 1 - t 4, t 5 - t 4, -t 4]

theorem diagonal_leftInverse :
    Function.LeftInverse (diagonalInverse (K := K)) diagonalMap := by
  intro a
  funext i
  fin_cases i <;> simp [diagonalMap, diagonalInverse] <;> ring

theorem diagonal_rightInverse :
    Function.RightInverse (diagonalInverse (K := K)) diagonalMap := by
  intro a
  funext i
  fin_cases i <;> simp [diagonalMap, diagonalInverse] <;> ring

theorem diagonalMap_bijective : Function.Bijective (diagonalMap (K := K)) :=
  ⟨diagonal_leftInverse.injective, diagonal_rightInverse.surjective⟩

/-- The two distinct blocks' map, using the row order `(00u,00v,01u,01v,10u,10v,11u,11v)`. -/
def pairMap (a : Fin 12 → K) : Fin 8 → K :=
  ![a 0 - a 2 + a 6 - a 8, -a 2 - a 8,
    a 3 - a 5 - a 8, -a 5 + a 7 - a 8,
    -a 2 + a 9 - a 11, a 1 - a 2 - a 11,
    -a 5 - a 11, a 4 - a 5 + a 10 - a 11]

def pairPreimage (t : Fin 8 → K) : Fin 12 → K :=
  ![t 0 - t 1, t 5, 0, t 2 - t 6 - t 1, t 7 - t 6, -t 6,
    0, t 3 - t 6 - t 1, -t 1, t 4, 0, 0]

theorem pair_rightInverse :
    Function.RightInverse (pairPreimage (K := K)) pairMap := by
  intro a
  funext i
  fin_cases i <;> simp [pairMap, pairPreimage] <;> ring

theorem pairMap_surjective : Function.Surjective (pairMap (K := K)) :=
  pair_rightInverse.surjective

/-- The active-inactive cross map `(a,b,d) ↦ (a-d,-d,-d,b-d)`. -/
def crossMap (a : Fin 3 → K) : Fin 4 → K :=
  ![a 0 - a 2, -a 2, -a 2, a 1 - a 2]

def crossCokernel (t : Fin 4 → K) : K := t 1 - t 2

theorem crossCokernel_vanishes (a : Fin 3 → K) :
    crossCokernel (crossMap a) = 0 := by
  simp [crossCokernel, crossMap]

theorem crossMap_injective : Function.Injective (crossMap (K := K)) := by
  intro a b h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h3 := congrFun h 3
  simp [crossMap] at h0 h1 h3
  funext i
  fin_cases i
  · exact (sub_left_inj).mp (h1 ▸ h0)
  · exact (sub_left_inj).mp (h1 ▸ h3)
  · exact h1

theorem crossMap_range (t : Fin 4 → K) :
    (∃ a, crossMap a = t) ↔ crossCokernel t = 0 := by
  constructor
  · rintro ⟨a, rfl⟩
    exact crossCokernel_vanishes a
  · intro h
    have h12 : t 1 = t 2 := sub_eq_zero.mp h
    refine ⟨![t 0 - t 2, t 3 - t 2, -t 2], ?_⟩
    funext i
    fin_cases i <;> simp [crossMap, h12]

theorem child_repairs_cross :
    crossCokernel (![0, 1, 0, 0] : Fin 4 → K) = 1 := by
  simp [crossCokernel]

/-- Adding the child quadric in the second output coordinate repairs the missing direction. -/
def repairedCrossMap (a : Fin 4 → K) : Fin 4 → K :=
  ![a 0 - a 2, -a 2 + a 3, -a 2, a 1 - a 2]

def repairedCrossInverse (t : Fin 4 → K) : Fin 4 → K :=
  ![t 0 - t 2, t 3 - t 2, -t 2, t 1 - t 2]

theorem repairedCross_leftInverse :
    Function.LeftInverse (repairedCrossInverse (K := K)) repairedCrossMap := by
  intro a
  funext i
  fin_cases i <;> simp [repairedCrossMap, repairedCrossInverse]

theorem repairedCross_rightInverse :
    Function.RightInverse (repairedCrossInverse (K := K)) repairedCrossMap := by
  intro a
  funext i
  fin_cases i <;> simp [repairedCrossMap, repairedCrossInverse]

theorem repairedCrossMap_bijective :
    Function.Bijective (repairedCrossMap (K := K)) :=
  ⟨repairedCross_leftInverse.injective, repairedCross_rightInverse.surjective⟩

end Quartic.ThreeBlock
