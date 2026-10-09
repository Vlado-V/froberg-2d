module

public import Quartic.Homogeneous
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

/-!
# The actual three-row convolution presentation

The coefficient-degree `j` map is from `t+2` homogeneous polynomials of degree
`j` to three homogeneous polynomials of degree `j+1`. Row `d` is the sum of
`y_i` times coefficient `i+d`. Thus each column has exactly the variable
entries specified in `cv:presentation`, including zero outside the variable
range. No Hilbert function is assumed.
-/

namespace Quartic.ConvolutionPresentation

noncomputable section

open MvPolynomial

variable {K : Type*} [Field K] {t j : ℕ}

abbrev Source (K : Type*) [Field K] (t j : ℕ) := Fin (t + 2) → Quartic.Forms K t j
abbrev Target (K : Type*) [Field K] (t j : ℕ) := Fin 3 → Quartic.Forms K t j

/-- The column index is the sum of the row and variable indices. -/
def columnIndex (d : Fin 3) (i : Fin t) : Fin (t + 2) :=
  ⟨i.val + d.val, by omega⟩

/-- Multiplication by a variable with its homogeneous degree recorded. -/
def variableMul (i : Fin t) : Quartic.Forms K t j →ₗ[K] Quartic.Forms K t (j + 1) where
  toFun a := ⟨X i * a.val, by
    change IsHomogeneous (X i * a.val) (j + 1)
    simpa only [Nat.add_comm] using (isHomogeneous_X K i).mul a.property⟩
  map_add' _ _ := Subtype.ext (mul_add _ _ _)
  map_smul' _ _ := Subtype.ext (mul_smul_comm _ _ _)

/-- The actual coefficient-degree `j` convolution multiplication map. -/
def presentation : Source K t j →ₗ[K] Target K t (j + 1) :=
  LinearMap.pi fun d => ∑ i : Fin t, (variableMul i).comp (LinearMap.proj (columnIndex d i))

@[simp] theorem presentation_apply (a : Source K t j) (d : Fin 3) :
    presentation a d = ∑ i : Fin t, variableMul i (a (columnIndex d i)) := by
  simp [presentation]

@[simp] theorem presentation_apply_val (a : Source K t j) (d : Fin 3) :
    (presentation a d).val = ∑ i : Fin t, X i * (a (columnIndex d i)).val := by
  simp [presentation, variableMul]

/-- The defining recurrence in ordinary polynomial coefficients. -/
theorem presentation_coeff (a : Source K t j) (d : Fin 3) (e : Fin t →₀ ℕ) :
    (presentation a d).val.coeff e =
      ∑ i : Fin t, if i ∈ e.support then
        (a (columnIndex d i)).val.coeff (e - Finsupp.single i 1) else 0 := by
  classical
  simp only [presentation_apply_val, coeff_sum, coeff_X_mul']

/-- The actual graded cokernel in positive degree. -/
abbrev Cokernel (K : Type*) [Field K] (t j : ℕ) :=
  Target K t (j + 1) ⧸ LinearMap.range (presentation (K := K) (t := t) (j := j))

/-- The degree-zero piece has no incoming columns. -/
abbrev DegreeZero (K : Type*) [Field K] (t : ℕ) := Target K t 0

/-- A homogeneous monomial with coefficient one. -/
def monomialForm (e : Fin t →₀ ℕ) (he : e.degree = j) : Quartic.Forms K t j :=
  ⟨monomial e 1, isHomogeneous_monomial 1 he⟩

/-- A monomial in one of the three target rows. -/
def rowMonomial (d : Fin 3) (e : Fin t →₀ ℕ) (he : e.degree = j) : Target K t j :=
  Pi.single d (monomialForm e he)

@[simp] theorem monomialForm_val (e : Fin t →₀ ℕ) (he : e.degree = j) :
    (monomialForm (K := K) e he).val = monomial e 1 := rfl

theorem degree_add_single (e : Fin t →₀ ℕ) (he : e.degree = j) (i : Fin t) :
    (e + Finsupp.single i 1).degree = j + 1 := by
  simp [he]

@[simp] theorem variableMul_monomialForm (e : Fin t →₀ ℕ)
    (he : e.degree = j) (i : Fin t) :
    variableMul i (monomialForm (K := K) e he) =
      monomialForm (e + Finsupp.single i 1) (degree_add_single e he i) := by
  apply Subtype.ext
  simp [variableMul, monomialForm, MvPolynomial.X, monomial_mul_monomial, add_comm]

/-- Every column is present already on constant coefficients when `t` is positive. -/
theorem columnIndex_surjective (ht : 1 ≤ t) (k : Fin (t + 2)) :
    ∃ (d : Fin 3) (i : Fin t), columnIndex d i = k := by
  by_cases hk : k.val < t
  · exact ⟨0, ⟨k.val, hk⟩, Fin.ext (by simp [columnIndex])⟩
  · refine ⟨⟨k.val - (t - 1), by omega⟩, ⟨t - 1, by omega⟩, Fin.ext ?_⟩
    dsimp [columnIndex]
    omega

theorem degreeZero_eq_constant (a : Quartic.Forms K t 0) :
    a.val = C (a.val.coeff 0) := by
  exact (homogeneousComponent_eq_self a.property).symm.trans (homogeneousComponent_zero a.val)

/-- Coefficients of the degree-one output recover the constant input entries. -/
theorem presentation_degreeOne_coeff (a : Source K t 0) (d : Fin 3) (i : Fin t) :
    (presentation a d).val.coeff (Finsupp.single i 1) =
      (a (columnIndex d i)).val.coeff 0 := by
  classical
  have hv : (presentation a d).val =
      ∑ l : Fin t, C ((a (columnIndex d l)).val.coeff 0) * X l := by
    rw [presentation_apply_val]
    apply Finset.sum_congr rfl
    intro l _
    exact (congrArg (fun p => X l * p) (degreeZero_eq_constant (a (columnIndex d l)))).trans
      (mul_comm _ _)
  rw [hv]
  simp [coeff_C_mul, coeff_X, Finsupp.single_eq_single_iff]

/-- There are no constant-coefficient syzygies in the actual presentation. -/
theorem presentation_degreeOne_injective (ht : 1 ≤ t) :
    Function.Injective (presentation (K := K) (t := t) (j := 0)) := by
  intro a b hab
  funext k
  obtain ⟨d, i, rfl⟩ := columnIndex_surjective ht k
  have h := congrArg (fun c : Target K t 1 => (c d).val.coeff (Finsupp.single i 1)) hab
  rw [presentation_degreeOne_coeff, presentation_degreeOne_coeff] at h
  apply Subtype.ext
  exact (degreeZero_eq_constant _).trans
    ((congrArg C h).trans (degreeZero_eq_constant _).symm)

/-- The initial graded component consists of the three constant rows. -/
theorem degreeZero_finrank : Module.finrank K (DegreeZero K t) = 3 := by
  simp [DegreeZero, Target, Module.finrank_pi_fintype, Quartic.finrank_forms]

/-- The degree-one Hilbert function follows from the actual injective map. -/
theorem cokernel_degreeOne_finrank (ht : 1 ≤ t) :
    Module.finrank K (Cokernel K t 0) = 2 * (t - 1) := by
  have h := (LinearMap.range (presentation (K := K) (t := t) (j := 0))).finrank_quotient_add_finrank
  rw [LinearMap.finrank_range_of_inj (presentation_degreeOne_injective ht)] at h
  have hs : Module.finrank K (Source K t 0) = t + 2 := by
    simp [Source, Module.finrank_pi_fintype, Quartic.finrank_forms]
  have htarg : Module.finrank K (Target K t 1) = 3 * t := by
    simp [Target, Module.finrank_pi_fintype, Quartic.finrank_forms]
  change Module.finrank K (Cokernel K t 0) + Module.finrank K (Source K t 0) =
    Module.finrank K (Target K t 1) at h
  rw [hs, htarg] at h
  omega

end

end Quartic.ConvolutionPresentation
