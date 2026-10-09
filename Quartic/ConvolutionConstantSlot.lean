module

public import Quartic.ConvolutionFactor
public import Quartic.ConvolutionSymmetric
public import Mathlib.Algebra.MvPolynomial.Variables

@[expose] public section

/-!
# Erasing an absent distinguished variable

A slot polynomial of degree zero in the distinguished variable is faithfully
identified with a polynomial in the ordinary variables. Erasure preserves
ordinary degree bounds and commutes with slot permutations.
-/

namespace Quartic.ConvolutionConstantSlot

noncomputable section

open MvPolynomial Quartic.ConvolutionFactor

variable {K : Type*} [Field K] {j : ℕ}

/-- Set the distinguished variable to zero and retain every ordinary variable. -/
def erase : Slots K j →ₐ[K] MvPolynomial (Fin j) K :=
  MvPolynomial.killCompl (f := @Option.some (Fin j)) (Option.some_injective (Fin j))

@[simp] theorem erase_rename (f : MvPolynomial (Fin j) K) :
    erase (MvPolynomial.rename Option.some f) = f :=
  MvPolynomial.killCompl_rename_app (Option.some_injective (Fin j)) f

@[simp] theorem erase_X_some (i : Fin j) : erase (X (some i) : Slots K j) = X i := by
  simpa using erase_rename (X i : MvPolynomial (Fin j) K)

@[simp] theorem erase_X_none : erase (X none : Slots K j) = 0 := by
  simp [erase, MvPolynomial.killCompl]

/-- A polynomial independent of the distinguished variable is reconstructed
exactly by restoring the ordinary variable names after erasure. -/
theorem rename_erase_of_degree_none_zero (H : Slots K j) (hH : H.degreeOf none = 0) :
    MvPolynomial.rename Option.some (erase H) = H := by
  have hvars : (H.vars : Set (Option (Fin j))) ⊆ Set.range Option.some := by
    intro o ho
    cases o with
    | none => exact False.elim ((MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mp ho) hH)
    | some i => exact ⟨i, rfl⟩
  obtain ⟨f, rfl⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range H Option.some
    (Option.some_injective (Fin j)) hvars
  rw [erase_rename]

/-- Erasure is injective on polynomials independent of the distinguished variable. -/
theorem erase_injective_of_degree_none_zero (H G : Slots K j)
    (hH : H.degreeOf none = 0) (hG : G.degreeOf none = 0) (h : erase H = erase G) : H = G := by
  have h' := congrArg (MvPolynomial.rename (@Option.some (Fin j))) h
  rwa [rename_erase_of_degree_none_zero H hH, rename_erase_of_degree_none_zero G hG] at h'

@[simp] theorem erase_coeff (H : Slots K j) (e : Fin j →₀ ℕ) :
    (erase H).coeff e = H.coeff (e.mapDomain Option.some) :=
  MvPolynomial.coeff_killCompl (Option.some_injective (Fin j))

/-- Erasure cannot increase the degree in an ordinary variable. -/
theorem degreeOf_erase_le (H : Slots K j) (i : Fin j) :
    (erase H).degreeOf i ≤ H.degreeOf (some i) := by
  apply degreeOf_le_iff.mpr
  intro e he
  have hcoeff : (erase H).coeff e ≠ 0 := mem_support_iff.mp he
  rw [erase_coeff] at hcoeff
  have hmem : e.mapDomain Option.some ∈ H.support := mem_support_iff.mpr hcoeff
  have hbound := MvPolynomial.le_degreeOf_of_mem_support (some i) hmem
  simpa only [Finsupp.mapDomain_apply_of_injective (Option.some_injective (Fin j))] using hbound

/-- Erasure commutes with every permutation of the ordinary slots. -/
theorem erase_permuteSlots (σ : Equiv.Perm (Fin j)) (H : Slots K j) :
    erase (permuteSlots σ H) = MvPolynomial.rename σ (erase H) := by
  have h : (erase (K := K) (j := j)).comp (permuteSlots σ) =
      (MvPolynomial.rename σ).comp erase := by
    apply MvPolynomial.algHom_ext
    intro o
    cases o <;> simp [AlgHom.comp_apply, permuteSlots]
  exact congrArg (fun f : Slots K j →ₐ[K] MvPolynomial (Fin j) K => f H) h

/-- The erased degree-two inverse factor belongs to the actual symmetric
bivariate factor space as soon as the proved slot bounds and symmetry hold. -/
theorem erase_mem_symmetricSpace (t : ℕ) (ht : 2 ≤ t) (H : Slots K 2)
    (hdegree : ∀ i : Fin 2, H.degreeOf (some i) ≤ t - 2)
    (hsym : permuteSlots Quartic.ConvolutionSymmetric.swapVariables H = H) :
    erase H ∈ Quartic.ConvolutionSymmetric.symmetricSpace K (t - 1) := by
  apply (Quartic.ConvolutionSymmetric.mem_convolution_factor_iff t ht (erase H)).mpr
  constructor
  · intro i
    exact (degreeOf_erase_le H i).trans (hdegree i)
  · rw [← erase_permuteSlots, hsym]

end

end Quartic.ConvolutionConstantSlot
