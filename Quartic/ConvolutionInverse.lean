module

public import Quartic.ConvolutionSlots
public import Quartic.ConvolutionTuples

@[expose] public section

/-!
# The convolution dual embeds into the diagonal inverse system

Ordered tuple coefficients encode the dual of the actual three-row target
injectively. The presentation-annihilator recurrence implies every diagonal
vanishing equation. The proved factorization therefore applies to the actual
cokernel dual, and proves that the cokernel vanishes in every degree at least
three. No dimension or inverse-system identification is assumed.
-/

noncomputable section
namespace Quartic.ConvolutionInverse
open MvPolynomial ConvolutionPresentation ConvolutionDual ConvolutionTuples
open ConvolutionSlots ConvolutionFactor
variable {K : Type*} [Field K] {t j : ℕ}

/-- The ordered-slot polynomial of an actual target functional. -/
def encode (φ : Module.Dual K (Target K t j)) : Slots K j :=
  ofCoefficients fun a => φ (rowMonomial a.1 (tupleExponent a.2) (tupleExponent_degree a.2))

@[simp] theorem coeff_encode (φ : Module.Dual K (Target K t j))
    (d : Fin 3) (v : Fin j → Fin t) :
    (encode φ).coeff (slotExponent d.val (fun i => (v i).val)) =
      φ (rowMonomial d (tupleExponent v) (tupleExponent_degree v)) :=
  coeff_ofCoefficients _ (d, v)

@[simp] theorem encode_zero : encode (0 : Module.Dual K (Target K t j)) = 0 := by
  simp [encode, ofCoefficients]

/-- All actual row-monomial values can be recovered from the slot polynomial. -/
theorem encode_injective : Function.Injective (encode (K := K) (t := t) (j := j)) := by
  intro φ ψ h
  apply target_linearForm_ext_tuple
  intro d v
  simpa using congrArg (fun p => p.coeff (slotExponent d.val (fun i => (v i).val))) h

/-- The coefficient encoding is linear. -/
def encodeLinear : Module.Dual K (Target K t j) →ₗ[K] Slots K j where
  toFun := encode
  map_add' φ ψ := by
    simp [encode, ofCoefficients, map_add, Finset.sum_add_distrib]
  map_smul' a φ := by
    simp [encode, ofCoefficients, Finset.smul_sum, MvPolynomial.smul_monomial]


/-- Ordered-tuple encoding is symmetric in all ordinary slots. -/
theorem encode_invariant (φ : Module.Dual K (Target K t j))
    (σ : Equiv.Perm (Fin j)) : permuteSlots σ (encode φ) = encode φ := by
  rw [encode, permuteSlots_ofCoefficients]
  congr 1
  funext a
  congr 2
  exact tupleExponent_perm a.2 σ

/-- Actual convolution relations imply vanishing on each diagonal. -/
theorem encode_vanishes (φ : Module.Dual K (Target K t (j + 1)))
    (hφ : φ ∈ annihilator K t j) : VanishesOnDiagonals K (j + 1) (encode φ) := by
  intro slot
  apply ofCoefficients_diagonal_zero
  intro v k
  have h := (mem_annihilator_iff_monomial_recurrence φ).mp hφ k
    (tupleExponent v) (tupleExponent_degree v)
  change (∑ d : Fin 3, ∑ i : Fin t, if columnIndex d i = k then
    φ (rowMonomial d (tupleExponent (slot.insertNth i v))
      (tupleExponent_degree (slot.insertNth i v))) else 0) = 0
  convert h using 1
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro i _
  split_ifs
  · congr 2
    exact (tupleExponent_insertNth slot i v).trans (add_comm _ _)
  · rfl

/-- Unique factorization of the actual convolution dual's encoded polynomial. -/
theorem encode_factorization (φ : Module.Dual K (Target K t (j + 1)))
    (hφ : φ ∈ annihilator K t j) :
    ∃! H : Slots K (j + 1), encode φ = diagonalProduct K (j + 1) * H :=
  existsUnique_diagonal_factor _ (encode_vanishes φ hφ)

/-- The actual inverse factor has the separate degree bounds predicted by the source. -/
theorem encode_factor_bounds (φ : Module.Dual K (Target K t (j + 1)))
    {H : Slots K (j + 1)} (hH : encode φ = diagonalProduct K (j + 1) * H) :
    H.degreeOf none ≤ 2 - (j + 1) ∧
      ∀ i, H.degreeOf (some i) ≤ (t - 1) - 1 :=
  diagonal_factor_bounds hH (ofCoefficients_degree_none _)
    (ofCoefficients_degree_some _)


/-- The unique inverse-system factor of an actual annihilator functional. -/
def inverseFactor (φ : annihilator K t j) : Slots K (j + 1) :=
  (encode_factorization φ.val φ.property).choose

@[simp] theorem inverseFactor_spec (φ : annihilator K t j) :
    encode φ.val = diagonalProduct K (j + 1) * inverseFactor φ :=
  (encode_factorization φ.val φ.property).choose_spec.1

/-- The inverse-system factor retains all information in the original dual. -/
theorem inverseFactor_injective : Function.Injective
    (inverseFactor (K := K) (t := t) (j := j)) := by
  intro φ ψ h
  apply Subtype.ext
  apply encode_injective
  rw [inverseFactor_spec, inverseFactor_spec, h]

/-- Factor extraction is a linear injection, by uniqueness of division by the
fixed nonzero diagonal product. -/
def inverseFactorLinear : annihilator K t j →ₗ[K] Slots K (j + 1) where
  toFun := inverseFactor
  map_add' φ ψ := by
    apply mul_left_cancel₀ (diagonalProduct_ne_zero K (j + 1))
    rw [← inverseFactor_spec, mul_add, ← inverseFactor_spec, ← inverseFactor_spec]
    exact encodeLinear.map_add φ.val ψ.val
  map_smul' a φ := by
    apply mul_left_cancel₀ (diagonalProduct_ne_zero K (j + 1))
    rw [← inverseFactor_spec, mul_smul_comm, ← inverseFactor_spec]
    exact encodeLinear.map_smul a φ.val

/-- Both separate degree restrictions hold for the extracted actual factor. -/
theorem inverseFactor_bounds (φ : annihilator K t j) :
    (inverseFactor φ).degreeOf none ≤ 2 - (j + 1) ∧
      ∀ i, (inverseFactor φ).degreeOf (some i) ≤ (t - 1) - 1 :=
  encode_factor_bounds φ.val (inverseFactor_spec φ)

/-- The actual inverse-system factor is symmetric in its ordinary slots. -/
theorem inverseFactor_invariant (φ : annihilator K t j)
    (σ : Equiv.Perm (Fin (j + 1))) :
    permuteSlots σ (inverseFactor φ) = inverseFactor φ :=
  diagonal_factor_invariant (inverseFactor_spec φ) σ (encode_invariant φ.val σ)

/-- There are no nonzero actual dual cokernel elements in degrees at least three. -/
theorem annihilator_eq_bot_of_three_le (hj : 3 ≤ j + 1) :
    annihilator K t j = ⊥ := by
  apply eq_bot_iff.mpr
  intro φ hφ
  change φ = 0
  apply encode_injective
  rw [encode_zero]
  exact quadratic_slot_eq_zero _ (encode_vanishes φ hφ)
    (ofCoefficients_degree_none _) hj

/-- The actual convolution presentation is onto in every target degree at least three. -/
theorem presentation_surjective_of_three_le (hj : 3 ≤ j + 1) :
    Function.Surjective (presentation (K := K) (t := t) (j := j)) := by
  apply LinearMap.range_eq_top.mp
  apply Submodule.dualAnnihilator_eq_bot_iff.mp
  exact annihilator_eq_bot_of_three_le hj

/-- The positive-degree cokernel has zero dimension from degree three onward. -/
theorem cokernel_finrank_eq_zero_of_three_le (hj : 3 ≤ j + 1) :
    Module.finrank K (Cokernel K t j) = 0 := by
  have htop := LinearMap.range_eq_top.mpr (presentation_surjective_of_three_le
    (K := K) (t := t) hj)
  have hsub : Subsingleton (Cokernel K t j) := Submodule.Quotient.subsingleton_iff.mpr htop
  exact Module.finrank_zero_of_subsingleton

end Quartic.ConvolutionInverse
