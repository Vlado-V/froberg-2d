import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Tactic

/-!
# Diagonal vanishing in the dehomogenized convolution slots

Here `s` is the outer polynomial variable and `z₁,...,zⱼ` are algebraically
independent variables in its coefficient ring. The diagonal equations in
`source/convolution.tex` become evaluation at `s = zᵢ`.

We prove divisibility by the complete product of diagonal factors, uniqueness
of the quotient, and the degree obstruction when there are more diagonals
than the available degree in `s`. The identification with the presentation's
dual module and the homogenization to binary determinant factors are separate
statements and are not asserted here.
-/

noncomputable section

namespace Quartic.ConvolutionDivisibility

open Polynomial

section DistinctRoots

variable {R ι : Type*} [CommRing R] [IsDomain R]

/-- Over a domain, distinct roots contribute distinct linear factors to the product divisor. -/
theorem prod_X_sub_C_dvd_of_eval_zero (a : ι → R) (ha : Function.Injective a)
    (S : Finset ι) (F : Polynomial R) (hF : ∀ i ∈ S, F.eval (a i) = 0) :
    (∏ i ∈ S, (X - C (a i))) ∣ F := by
  classical
  induction S using Finset.induction_on generalizing F with
  | empty => simp
  | @insert i S hi ih =>
      have hiF : X - C (a i) ∣ F := dvd_iff_isRoot.mpr (hF i (Finset.mem_insert_self i S))
      obtain ⟨G, rfl⟩ := hiF
      have hG : ∀ j ∈ S, G.eval (a j) = 0 := by
        intro j hj
        have hjF := hF j (Finset.mem_insert_of_mem hj)
        simp only [eval_mul, eval_sub, eval_X, eval_C] at hjF
        have hji : a j - a i ≠ 0 := by
          apply sub_ne_zero.mpr
          intro heq
          exact hi (ha heq ▸ hj)
        exact (mul_eq_zero.mp hjF).resolve_left hji
      obtain ⟨H, hH⟩ := ih G hG
      refine ⟨H, ?_⟩
      rw [Finset.prod_insert hi, hH, mul_assoc]

end DistinctRoots

section Slots

variable (K : Type*) [CommRing K] [IsDomain K] (j : ℕ)

/-- The dehomogenized `z` slots form the coefficient ring. -/
abbrev SlotRing := MvPolynomial (Fin j) K

/-- The outer variable of this ring is the distinguished slot `s`. -/
abbrev SlotPolynomial := Polynomial (SlotRing K j)

/-- The diagonal divisor `∏ᵢ(s-zᵢ)`. -/
def diagonalProduct : SlotPolynomial K j :=
  ∏ i : Fin j, (Polynomial.X - Polynomial.C (MvPolynomial.X i))

/-- Vanishing after substituting each independent slot `zᵢ` for `s`. -/
def VanishesOnDiagonals (F : SlotPolynomial K j) : Prop :=
  ∀ i : Fin j, F.eval (MvPolynomial.X i) = 0

omit [IsDomain K] in
theorem diagonalProduct_monic : (diagonalProduct K j).Monic :=
  Polynomial.monic_prod_X_sub_C _ _

theorem diagonalProduct_ne_zero : diagonalProduct K j ≠ 0 :=
  (diagonalProduct_monic K j).ne_zero

@[simp] theorem diagonalProduct_natDegree : (diagonalProduct K j).natDegree = j := by
  simp [diagonalProduct]

variable {K j}

/-- Every diagonal vanishing relation has all the diagonal factors. -/
theorem diagonalProduct_dvd (F : SlotPolynomial K j) (hF : VanishesOnDiagonals K j F) :
    diagonalProduct K j ∣ F := by
  apply prod_X_sub_C_dvd_of_eval_zero (MvPolynomial.X : Fin j → SlotRing K j)
    MvPolynomial.X_injective Finset.univ F
  intro i _
  exact hF i

/-- The product divisibility condition is exactly simultaneous diagonal vanishing. -/
theorem vanishes_iff_diagonalProduct_dvd (F : SlotPolynomial K j) :
    VanishesOnDiagonals K j F ↔ diagonalProduct K j ∣ F := by
  constructor
  · exact diagonalProduct_dvd F
  · intro hF i
    have hi : Polynomial.X - Polynomial.C (MvPolynomial.X i) ∣ diagonalProduct K j :=
      Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    exact dvd_iff_isRoot.mp (hi.trans hF)

/-- This is the dehomogenized factorization in the convolution inverse-system argument. -/
theorem existsUnique_diagonal_factor (F : SlotPolynomial K j)
    (hF : VanishesOnDiagonals K j F) :
    ∃! H : SlotPolynomial K j, F = diagonalProduct K j * H := by
  obtain ⟨H, hH⟩ := diagonalProduct_dvd F hF
  refine ⟨H, hH, ?_⟩
  intro H' hH'
  exact mul_left_cancel₀ (diagonalProduct_ne_zero K j) (hH'.symm.trans hH)

/-- Nonzero factorization removes exactly one unit of `s`-degree per diagonal. -/
theorem diagonal_factor_natDegree {F H : SlotPolynomial K j}
    (hF : F ≠ 0) (hfactor : F = diagonalProduct K j * H) :
    H.natDegree + j = F.natDegree := by
  have hH : H ≠ 0 := by
    intro hzero
    apply hF
    simp [hfactor, hzero]
  rw [hfactor, Polynomial.natDegree_mul (diagonalProduct_ne_zero K j) hH,
    diagonalProduct_natDegree]
  exact Nat.add_comm _ _

/-- The quotient has the degree predicted by the slot factorization. -/
theorem diagonal_factor_degree_sub {F H : SlotPolynomial K j}
    (hF : F ≠ 0) (hfactor : F = diagonalProduct K j * H) :
    H.natDegree = F.natDegree - j := by
  have h := diagonal_factor_natDegree hF hfactor
  omega

/-- Permute the coefficient slots, leaving the distinguished outer variable fixed. -/
def permuteSlots (σ : Equiv.Perm (Fin j)) (F : SlotPolynomial K j) : SlotPolynomial K j :=
  F.map (MvPolynomial.rename σ).toRingHom

omit [IsDomain K] in
/-- The full diagonal divisor is invariant under permutations of the slots. -/
theorem permuteSlots_diagonalProduct (σ : Equiv.Perm (Fin j)) :
    permuteSlots σ (diagonalProduct K j) = diagonalProduct K j := by
  simp only [permuteSlots, diagonalProduct, Polynomial.map_prod, Polynomial.map_sub,
    Polynomial.map_X, Polynomial.map_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    MvPolynomial.rename_X]
  exact Equiv.prod_comp σ (fun i : Fin j =>
    (Polynomial.X - Polynomial.C (MvPolynomial.X i) : SlotPolynomial K j))

/-- Symmetry of the original polynomial descends to its unique diagonal quotient. -/
theorem diagonal_factor_invariant {F H : SlotPolynomial K j}
    (hfactor : F = diagonalProduct K j * H) (σ : Equiv.Perm (Fin j))
    (hF : permuteSlots σ F = F) : permuteSlots σ H = H := by
  have h := congrArg (permuteSlots σ) hfactor
  change permuteSlots σ F =
    (diagonalProduct K j * H).map (MvPolynomial.rename σ).toRingHom at h
  rw [Polynomial.map_mul] at h
  change permuteSlots σ F = permuteSlots σ (diagonalProduct K j) * permuteSlots σ H at h
  rw [hF, permuteSlots_diagonalProduct] at h
  exact mul_left_cancel₀ (diagonalProduct_ne_zero K j) (h.symm.trans hfactor)

/-- Too many independent diagonal roots force the slot polynomial to vanish. -/
theorem eq_zero_of_degree_lt_slots (F : SlotPolynomial K j)
    (hF : VanishesOnDiagonals K j F) (hdegree : F.natDegree < j) : F = 0 := by
  apply Polynomial.eq_zero_of_dvd_of_natDegree_lt (diagonalProduct_dvd F hF)
  simpa using hdegree

/-- A bounded distinguished-slot degree cannot accommodate more diagonal factors. -/
theorem eq_zero_of_slot_degree_bound (F : SlotPolynomial K j) {d : ℕ}
    (hF : VanishesOnDiagonals K j F) (hdegree : F.natDegree ≤ d) (hslots : d < j) :
    F = 0 :=
  eq_zero_of_degree_lt_slots F hF (hdegree.trans_lt hslots)

/-- In particular, the degree-two slot appearing in the manuscript vanishes for `j ≥ 3`. -/
theorem quadratic_slot_eq_zero (F : SlotPolynomial K j)
    (hF : VanishesOnDiagonals K j F) (hdegree : F.natDegree ≤ 2) (hslots : 3 ≤ j) :
    F = 0 :=
  eq_zero_of_slot_degree_bound F hF hdegree (by omega)

end Slots

end Quartic.ConvolutionDivisibility
