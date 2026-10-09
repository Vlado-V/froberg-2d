module

public import Quartic.ConvolutionDivisibility

@[expose] public section

/-!
# Separate degree bounds for the convolution diagonal factor

This version uses a single multivariate polynomial ring. The distinguished
variable is `none`, and `some i` is the `i`th symmetric slot. The diagonal
factorization is transferred through the actual polynomial-ring equivalence,
and its degree in every variable is computed. Thus the quotient loses one
degree in each ordinary slot, not just in the distinguished variable.
-/

noncomputable section

namespace Quartic.ConvolutionFactor

open MvPolynomial

variable (K : Type*) [CommRing K] [IsDomain K] (j : ℕ)

abbrev Slots := MvPolynomial (Option (Fin j)) K

def diagonalProduct : Slots K j :=
  ∏ i : Fin j, (X none - X (some i))

/-- Substitute `s = zᵢ`, retaining all ordinary slot variables. -/
def diagonalMap (i : Fin j) : Slots K j →ₐ[K] MvPolynomial (Fin j) K :=
  rename (fun o => o.elim i id)

def VanishesOnDiagonals (F : Slots K j) : Prop :=
  ∀ i, diagonalMap K j i F = 0

omit [IsDomain K] in
@[simp] theorem optionEquiv_diagonalProduct :
    optionEquivLeft K (Fin j) (diagonalProduct K j) =
      ConvolutionDivisibility.diagonalProduct K j := by
  simp [diagonalProduct, ConvolutionDivisibility.diagonalProduct]

omit [IsDomain K] in
/-- Polynomial evaluation is exactly the stated diagonal substitution. -/
theorem eval_optionEquiv (F : Slots K j) (i : Fin j) :
    (optionEquivLeft K (Fin j) F).eval (X i) = diagonalMap K j i F := by
  induction F using MvPolynomial.induction_on with
  | C a => simp [diagonalMap]
  | add p q hp hq => simp_all
  | mul_X p o hp => cases o <;> simp_all [diagonalMap]

variable {K j}

/-- Transfer diagonal factorization from the polynomial coefficient ring. -/
theorem existsUnique_diagonal_factor (F : Slots K j)
    (hF : VanishesOnDiagonals K j F) :
    ∃! H : Slots K j, F = diagonalProduct K j * H := by
  have hn : ConvolutionDivisibility.VanishesOnDiagonals K j
      (optionEquivLeft K (Fin j) F) := by
    intro i
    rw [eval_optionEquiv]
    exact hF i
  obtain ⟨H, hH, huniq⟩ :=
    ConvolutionDivisibility.existsUnique_diagonal_factor _ hn
  refine ⟨(optionEquivLeft K (Fin j)).symm H, ?_, ?_⟩
  · apply (optionEquivLeft K (Fin j)).injective
    simpa using hH
  · intro G hG
    apply (optionEquivLeft K (Fin j)).injective
    simp only [AlgEquiv.apply_symm_apply]
    apply huniq
    simpa using congrArg (optionEquivLeft K (Fin j)) hG

variable (K j)

@[simp] theorem diagonalProduct_ne_zero : diagonalProduct K j ≠ 0 := by
  intro h
  have := congrArg (optionEquivLeft K (Fin j)) h
  exact ConvolutionDivisibility.diagonalProduct_ne_zero K j (by simpa using this)

private theorem factor_degree_none (i : Fin j) :
    (X none - X (some i) : Slots K j).degreeOf none = 1 := by
  rw [sub_eq_add_neg, degreeOf_add_eq_of_degreeOf_lt]
  · simp
  · simp [degreeOf_neg, degreeOf_X]

private theorem factor_degree_some (i k : Fin j) :
    (X none - X (some i) : Slots K j).degreeOf (some k) = if k = i then 1 else 0 := by
  classical
  by_cases h : k = i
  · subst k
    rw [ite_eq_left rfl, sub_eq_add_neg, add_comm, degreeOf_add_eq_of_degreeOf_lt]
    · simp [degreeOf_neg]
    · simp [degreeOf_neg, degreeOf_X]
  · rw [ite_eq_right h]
    apply Nat.eq_zero_of_le_zero
    simpa [degreeOf_X, h] using degreeOf_sub_le (some k)
      (X none : Slots K j) (X (some i))

private theorem factor_ne_zero (i : Fin j) :
    (X none - X (some i) : Slots K j) ≠ 0 := by
  apply ne_zero_of_degreeOf_ne_zero (i := none)
  rw [factor_degree_none]
  exact one_ne_zero

@[simp] theorem diagonalProduct_degree_none :
    (diagonalProduct K j).degreeOf none = j := by
  rw [diagonalProduct, degreeOf_prod_eq _ _ (fun i _ => factor_ne_zero K j i)]
  simp [factor_degree_none]

@[simp] theorem diagonalProduct_degree_some (i : Fin j) :
    (diagonalProduct K j).degreeOf (some i) = 1 := by
  classical
  rw [diagonalProduct, degreeOf_prod_eq _ _ (fun i _ => factor_ne_zero K j i)]
  simp [factor_degree_some]

variable {K j}

/-- Factoring the diagonals removes `j` degrees in the distinguished slot. -/
theorem diagonal_factor_degree_none {F H : Slots K j} (hF : F ≠ 0)
    (hfactor : F = diagonalProduct K j * H) :
    F.degreeOf none = j + H.degreeOf none := by
  have hH : H ≠ 0 := by intro h; simp [h, hfactor] at hF
  rw [hfactor, degreeOf_mul_eq (diagonalProduct_ne_zero K j) hH,
    diagonalProduct_degree_none]

/-- Factoring the diagonals removes one degree in each symmetric slot. -/
theorem diagonal_factor_degree_some {F H : Slots K j} (hF : F ≠ 0)
    (hfactor : F = diagonalProduct K j * H) (i : Fin j) :
    F.degreeOf (some i) = 1 + H.degreeOf (some i) := by
  have hH : H ≠ 0 := by intro h; simp [h, hfactor] at hF
  rw [hfactor, degreeOf_mul_eq (diagonalProduct_ne_zero K j) hH,
    diagonalProduct_degree_some]

/-- The separate degree bounds in the manuscript's inverse-system formula. -/
theorem diagonal_factor_bounds {F H : Slots K j} {s t : ℕ}
    (hfactor : F = diagonalProduct K j * H)
    (hs : F.degreeOf none ≤ s) (ht : ∀ i, F.degreeOf (some i) ≤ t) :
    H.degreeOf none ≤ s - j ∧ ∀ i, H.degreeOf (some i) ≤ t - 1 := by
  by_cases hF : F = 0
  · have hH : H = 0 := (mul_eq_zero.mp (hfactor.symm.trans hF)).resolve_left
      (diagonalProduct_ne_zero K j)
    simp [hH]
  · have hn := diagonal_factor_degree_none hF hfactor
    constructor
    · omega
    · intro i
      have hi := diagonal_factor_degree_some hF hfactor i
      have := ht i
      omega

/-- The quadratic distinguished slot forces zero in degrees at least three. -/
theorem quadratic_slot_eq_zero (F : Slots K j) (hF : VanishesOnDiagonals K j F)
    (hs : F.degreeOf none ≤ 2) (hj : 3 ≤ j) : F = 0 := by
  obtain ⟨H, hH, _⟩ := existsUnique_diagonal_factor F hF
  by_contra hn
  have := diagonal_factor_degree_none hn hH
  omega

/-- Relabel ordinary slots while fixing the distinguished variable. -/
def permuteSlots (σ : Equiv.Perm (Fin j)) : Slots K j →ₐ[K] Slots K j :=
  rename (Option.map σ)

omit [IsDomain K] in
@[simp] theorem permuteSlots_diagonalProduct (σ : Equiv.Perm (Fin j)) :
    permuteSlots σ (diagonalProduct K j) = diagonalProduct K j := by
  simp only [permuteSlots, diagonalProduct, map_prod, map_sub, rename_X,
    Option.map_none, Option.map_some]
  exact Equiv.prod_comp σ (fun i : Fin j => (X none - X (some i) : Slots K j))

/-- Slot symmetry descends to the unique factor. -/
theorem diagonal_factor_invariant {F H : Slots K j}
    (hfactor : F = diagonalProduct K j * H) (σ : Equiv.Perm (Fin j))
    (hF : permuteSlots σ F = F) : permuteSlots σ H = H := by
  have h := congrArg (permuteSlots σ) hfactor
  rw [map_mul, permuteSlots_diagonalProduct, hF] at h
  exact mul_left_cancel₀ (diagonalProduct_ne_zero K j) (h.symm.trans hfactor)

end Quartic.ConvolutionFactor
