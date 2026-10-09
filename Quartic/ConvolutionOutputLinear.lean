module

public import Quartic.ConvolutionOutput
public import Quartic.ConvolutionLinearFactor

@[expose] public section

/-!
# Linear images of the actual output space

The degree-one inverse factor gives explicit two-row polynomial equations
for functionals annihilating an output multiplication image.
-/

noncomputable section
namespace Quartic.ConvolutionOutputLinear
open MvPolynomial ConvolutionPresentation ConvolutionDual ConvolutionInverse
open ConvolutionSlots ConvolutionTuples ConvolutionFactor ConvolutionLinearFactor
open ConvolutionOutput ConvolutionHilbert
variable {K : Type*} [Field K] {t : ℕ}

/-- Linear multiplication by a fixed output coefficient vector. -/
def outputLinear (c : Fin 3 → K) : Forms K t 1 →ₗ[K] Cokernel K t 0 :=
  (Submodule.mkQ _).comp (outputTarget c 1)

/-- A distinguished coefficient, retained as an ordinary univariate polynomial. -/
def rowPolynomial (d : ℕ) (H : Slots K 1) : Poly K 1 :=
  (optionEquivLeft K (Fin 1) H).coeff d

/-- Output contraction of a degree-one encoded functional. -/
def contractLinear (c : Fin 3 → K) (F : Slots K 1) : Poly K 1 :=
  ∑ d : Fin 3, c d • rowPolynomial d.val F

def firstMultiplier (c : Fin 3 → K) : Poly K 1 := C (c 1) - C (c 0) * X 0

def secondMultiplier (c : Fin 3 → K) : Poly K 1 := C (c 2) - C (c 1) * X 0

/-- The distinguished degree bound gives an exact two-row expansion. -/
theorem optionEquiv_expansion (H : Slots K 1) (hH : H.degreeOf none ≤ 1) :
    optionEquivLeft K (Fin 1) H =
      Polynomial.C (rowPolynomial 1 H) * Polynomial.X + Polynomial.C (rowPolynomial 0 H) :=
  Polynomial.eq_X_add_C_of_natDegree_le_one (by rwa [natDegree_optionEquivLeft])

/-- Contracting `(s-z)H` gives the two explicit coefficient multipliers. -/
theorem contractLinear_factor (c : Fin 3 → K) (H : Slots K 1)
    (hH : H.degreeOf none ≤ 1) :
    contractLinear c (diagonalProduct K 1 * H) =
      firstMultiplier c * rowPolynomial 0 H + secondMultiplier c * rowPolynomial 1 H := by
  have hpoly : optionEquivLeft K (Fin 1) (diagonalProduct K 1 * H) =
      Polynomial.C (rowPolynomial 1 H) * Polynomial.X ^ 2 +
      Polynomial.C (rowPolynomial 0 H - X 0 * rowPolynomial 1 H) * Polynomial.X -
      Polynomial.C (X 0 * rowPolynomial 0 H) := by
    simp only [diagonalProduct, Fin.prod_univ_one, map_mul, map_sub,
      optionEquivLeft_X_none, optionEquivLeft_X_some]
    rw [optionEquiv_expansion H hH]
    ring
  simp only [contractLinear, rowPolynomial, hpoly, Fin.sum_univ_three,
    Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]
  norm_num
  simp only [firstMultiplier, secondMultiplier, smul_eq_C_mul]
  ring

/-- The two multipliers cannot both vanish for a nonzero output vector. -/
theorem multipliers_nonzero {c : Fin 3 → K} (hc : c ≠ 0) :
    firstMultiplier c ≠ 0 ∨ secondMultiplier c ≠ 0 := by
  by_contra h
  push Not at h
  have h0 := congrArg (fun F : Poly K 1 => F.coeff (Finsupp.single 0 1)) h.1
  have h1 := congrArg (fun F : Poly K 1 => F.coeff 0) h.1
  have h2 := congrArg (fun F : Poly K 1 => F.coeff 0) h.2
  simp [firstMultiplier, secondMultiplier, coeff_C_mul, coeff_X] at h0 h1 h2
  apply hc
  funext d
  fin_cases d <;> simp_all

/-- The row coefficients are the same coefficients retained by `coefficientFunctional`. -/
theorem rowPolynomial_coeff (d n : ℕ) (H : Slots K 1) :
    (rowPolynomial d H).coeff (Finsupp.single 0 n) = H.coeff (oneExponent d n) := by
  rw [rowPolynomial, optionEquivLeft_coeff_coeff]
  congr 1
  ext o
  cases o with
  | none => simp
  | some i => fin_cases i; simp

/-- A bounded row polynomial is determined by its finite coefficient functional. -/
theorem rowPolynomial_eq_zero_of_functional {p : ℕ} (hp : 1 ≤ p) (d : ℕ)
    (H : Slots K 1) (hH : H.degreeOf (some 0) ≤ p - 1)
    (h : coefficientFunctional p d H = 0) : rowPolynomial d H = 0 := by
  apply MvPolynomial.ext
  intro e
  have he : e = Finsupp.single 0 (e 0) := by
    apply Finsupp.ext
    intro i
    fin_cases i
    simp
  rw [he, rowPolynomial_coeff]
  by_cases hn : e 0 < p
  · have hc := congrArg (fun f : Module.Dual K (Fin p → K) => f (Pi.single ⟨e 0, hn⟩ 1)) h
    simpa only [coefficientFunctional_single, LinearMap.zero_apply, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using hc
  · have hc := coeff_zero_of_degreeOf_lt H (oneExponent d (e 0)) (some 0) (by
      simp only [slotExponent_some]; omega)
    simpa using hc

/-- Vanishing of both row polynomials kills the whole degree-one factor. -/
theorem eq_zero_of_rows (H : Slots K 1) (hH : H.degreeOf none ≤ 1)
    (h0 : rowPolynomial 0 H = 0) (h1 : rowPolynomial 1 H = 0) : H = 0 := by
  apply (optionEquivLeft K (Fin 1)).injective
  rw [optionEquiv_expansion H hH, h0, h1]
  simp

/-- The actual inverse factor as a linear map on the first cokernel dual. -/
def dualFactor : Module.Dual K (Cokernel K t 0) →ₗ[K] Slots K 1 :=
  inverseFactorLinear.comp (cokernelDualEquiv K t 0).toLinearMap

theorem dualFactor_injective : Function.Injective (dualFactor (K := K) (t := t)) :=
  inverseFactor_injective.comp (cokernelDualEquiv K t 0).injective

theorem dualFactor_bounds (φ : Module.Dual K (Cokernel K t 0)) :
    (dualFactor φ).degreeOf none ≤ 1 ∧
      (dualFactor φ).degreeOf (some 0) ≤ (t - 1) - 1 := by
  exact ⟨(inverseFactor_bounds (cokernelDualEquiv K t 0 φ)).1,
    (inverseFactor_bounds (cokernelDualEquiv K t 0 φ)).2 0⟩

/-- Contraction of an actual functional which kills all products by `c` vanishes. -/
theorem contractLinear_encode_zero (c : Fin 3 → K)
    (φ : Module.Dual K (Cokernel K t 0))
    (hφ : φ ∈ (LinearMap.range (outputLinear c)).dualAnnihilator) :
    contractLinear c (encode (cokernelDualEquiv K t 0 φ).val) = 0 := by
  classical
  let ordinary (v : Fin 1 → Fin t) : Fin 1 →₀ ℕ :=
    Finsupp.equivFunOnFinite.symm (fun i => (v i).val)
  have hs (d : ℕ) (v : Fin 1 → Fin t) :
      (slotExponent d (fun i => (v i).val)).some = ordinary v := by
    apply Finsupp.ext
    intro i
    simp [ordinary]
  have hr (d : Fin 3) : rowPolynomial d.val (encode (cokernelDualEquiv K t 0 φ).val) =
      ∑ v : Fin 1 → Fin t, monomial (ordinary v)
        ((cokernelDualEquiv K t 0 φ).val (rowMonomial d (tupleExponent v) (tupleExponent_degree v))) := by
    simp only [rowPolynomial, encode, ofCoefficients, map_sum, Fintype.sum_prod_type,
      Polynomial.finsetSum_coeff, optionEquivLeft_monomial, slotExponent_none, hs,
      Polynomial.coeff_monomial, Fin.val_inj]
    rw [Finset.sum_eq_single d]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  simp only [contractLinear, hr, Finset.smul_sum, smul_monomial, smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro v _
  rw [← map_sum (monomial (ordinary v))]
  rw [Submodule.mem_dualAnnihilator] at hφ
  have hv := hφ
    (outputLinear c (monomialForm (tupleExponent v) (tupleExponent_degree v)))
    ⟨_, rfl⟩
  have htarget : outputTarget c 1 (monomialForm (tupleExponent v) (tupleExponent_degree v)) =
      ∑ d : Fin 3, c d • rowMonomial d (tupleExponent v) (tupleExponent_degree v) := by
    funext d; simp [outputTarget, rowMonomial, Pi.single_apply]
  change φ (Submodule.Quotient.mk (outputTarget c 1 _)) = 0 at hv
  change (cokernelDualEquiv K t 0 φ).val (outputTarget c 1 _) = 0 at hv
  rw [htarget, map_sum] at hv
  simpa only [map_smul, smul_eq_mul, map_zero] using congrArg (monomial (ordinary v)) hv

/-- The precise polynomial relation imposed by a vanishing output multiplication. -/
theorem annihilator_equation (c : Fin 3 → K) (φ : Module.Dual K (Cokernel K t 0))
    (hφ : φ ∈ (LinearMap.range (outputLinear c)).dualAnnihilator) :
    firstMultiplier c * rowPolynomial 0 (dualFactor φ) +
      secondMultiplier c * rowPolynomial 1 (dualFactor φ) = 0 := by
  have h := contractLinear_encode_zero c φ hφ
  rw [inverseFactor_spec (cokernelDualEquiv K t 0 φ)] at h
  change contractLinear c (diagonalProduct K 1 * dualFactor φ) = 0 at h
  exact (contractLinear_factor c _ (dualFactor_bounds φ).1).symm.trans h

/-- A nonzero output has at most `t-1` annihilators in the first cokernel dual. -/
theorem single_annihilator_finrank_le (ht : 2 ≤ t) {c : Fin 3 → K} (hc : c ≠ 0) :
    Module.finrank K (LinearMap.range (outputLinear (t := t) c)).dualAnnihilator ≤ t - 1 := by
  let T := (LinearMap.range (outputLinear (t := t) c)).dualAnnihilator
  have hinj (d : ℕ) (hk : ∀ φ : T,
      coefficientFunctional (t - 1) d (dualFactor φ.val) = 0 → dualFactor φ.val = 0) :
      Module.finrank K T ≤ t - 1 := by
    let f : T →ₗ[K] Module.Dual K (Fin (t - 1) → K) :=
      (coefficientFunctional (t - 1) d).comp (dualFactor.comp T.subtype)
    have hf : Function.Injective f := by
      intro φ ψ h
      apply Subtype.ext
      apply dualFactor_injective
      have hz := hk (φ - ψ) (by
        change coefficientFunctional (t - 1) d (dualFactor (φ.val - ψ.val)) = 0
        rw [map_sub, map_sub]
        exact sub_eq_zero.mpr h)
      simpa only [Submodule.coe_sub, map_sub, sub_eq_zero] using hz
    simpa using f.finrank_le_finrank_of_injective hf
  rcases multipliers_nonzero hc with hfirst | hsecond
  · apply hinj 1
    intro φ hφ
    have h1 := rowPolynomial_eq_zero_of_functional (by omega) 1 _ (dualFactor_bounds φ.val).2 hφ
    have he := annihilator_equation c φ.val φ.property
    rw [h1, mul_zero, add_zero] at he
    exact eq_zero_of_rows _ (dualFactor_bounds φ.val).1 ((mul_eq_zero.mp he).resolve_left hfirst) h1
  · apply hinj 0
    intro φ hφ
    have h0 := rowPolynomial_eq_zero_of_functional (by omega) 0 _ (dualFactor_bounds φ.val).2 hφ
    have he := annihilator_equation c φ.val φ.property
    rw [h0, mul_zero, zero_add] at he
    exact eq_zero_of_rows _ (dualFactor_bounds φ.val).1 h0 ((mul_eq_zero.mp he).resolve_left hsecond)

/-- Every nonzero output vector has at least `t-1` independent linear products. -/
theorem single_output_linear_finrank (ht : 2 ≤ t) {c : Fin 3 → K} (hc : c ≠ 0) :
    t - 1 ≤ Module.finrank K (LinearMap.range (outputLinear (t := t) c)) := by
  have h := single_annihilator_finrank_le ht hc
  have hd := Subspace.finrank_add_finrank_dualAnnihilator_eq
    (LinearMap.range (outputLinear (t := t) c))
  rw [cokernel_degreeOne_finrank (by omega)] at hd
  omega

/-- The determinant of two output-contraction equations. -/
def outputDeterminant (c d : Fin 3 → K) : Poly K 1 :=
  firstMultiplier c * secondMultiplier d - firstMultiplier d * secondMultiplier c

theorem outputDeterminant_expansion (c d : Fin 3 → K) :
    outputDeterminant c d =
      C (c 1 * d 2 - d 1 * c 2) +
      C (d 0 * c 2 - c 0 * d 2) * X 0 +
      C (c 0 * d 1 - d 0 * c 1) * (X 0) ^ 2 := by
  simp only [outputDeterminant, firstMultiplier, secondMultiplier, map_sub, map_mul]
  ring

/-- Independent outputs give a nonzero polynomial determinant over every field. -/
theorem outputDeterminant_ne_zero {v : Fin 2 → (Fin 3 → K)} (hv : LinearIndependent K v) :
    outputDeterminant (v 0) (v 1) ≠ 0 := by
  intro h
  rw [outputDeterminant_expansion] at h
  have h0 := congrArg (fun F : Poly K 1 => F.coeff 0) h
  have h1 := congrArg (fun F : Poly K 1 => F.coeff (Finsupp.single 0 1)) h
  have h2 := congrArg (fun F : Poly K 1 => F.coeff (Finsupp.single 0 2)) h
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_C_mul,
    X_pow_eq_monomial, coeff_X, coeff_monomial, coeff_C, AddMonoidAlgebra.coeff_zero,
    Finsupp.zero_apply] at h0 h1 h2
  simp at h0 h1 h2
  simp only [h0, ite_self, zero_add] at h1 h2
  have hw (i j : Fin 3) : v 0 i * v 1 j = v 1 i * v 0 j := by
    fin_cases i <;> fin_cases j <;> dsimp at *
    all_goals first | ring | linear_combination h0 | linear_combination -h0 |
      linear_combination h1 | linear_combination -h1 | linear_combination h2 |
      linear_combination -h2
  have hv' := linearIndependent_fin2.mp hv
  obtain ⟨i, hi⟩ : ∃ i : Fin 3, v 1 i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv'.1 (funext h)
  apply hv'.2 (v 0 i / v 1 i)
  funext j
  change (v 0 i / v 1 i) * v 1 j = v 0 j
  field_simp
  exact hw i j

/-- Two independent output equations kill both rows of the inverse factor. -/
theorem two_equations_zero {v : Fin 2 → (Fin 3 → K)} (hv : LinearIndependent K v)
    (H : Slots K 1) (hH : H.degreeOf none ≤ 1)
    (h : ∀ i, firstMultiplier (v i) * rowPolynomial 0 H +
      secondMultiplier (v i) * rowPolynomial 1 H = 0) : H = 0 := by
  have hdet := outputDeterminant_ne_zero hv
  apply eq_zero_of_rows H hH
  · apply (mul_eq_zero.mp (show outputDeterminant (v 0) (v 1) * rowPolynomial 0 H = 0 from ?_)).resolve_left hdet
    dsimp [outputDeterminant]
    linear_combination secondMultiplier (v 1) * h 0 - secondMultiplier (v 0) * h 1
  · apply (mul_eq_zero.mp (show outputDeterminant (v 0) (v 1) * rowPolynomial 1 H = 0 from ?_)).resolve_left hdet
    dsimp [outputDeterminant]
    linear_combination firstMultiplier (v 0) * h 1 - firstMultiplier (v 1) * h 0

/-- Coordinates on actual degree-zero output vectors form a linear injection. -/
def outputCoordinates : DegreeZero K t →ₗ[K] (Fin 3 → K) where
  toFun := outputCoefficients
  map_add' e f := by funext d; simp [outputCoefficients]
  map_smul' a e := by funext d; simp [outputCoefficients]

theorem outputCoordinates_injective : Function.Injective (outputCoordinates (K := K) (t := t)) :=
  outputCoefficients_injective

/-- Actual multiplication by a degree-zero output. -/
def linearFromOutput (e : DegreeZero K t) : Forms K t 1 →ₗ[K] Cokernel K t 0 :=
  outputLinear (outputCoefficients e)

/-- The complete linear multiplication image of an output subspace. -/
def linearOutputImage (D' : Submodule K (DegreeZero K t)) : Submodule K (Cokernel K t 0) :=
  ⨆ e : D', LinearMap.range (linearFromOutput e.val)

theorem linearFromOutput_range_le (D' : Submodule K (DegreeZero K t))
    (e : DegreeZero K t) (he : e ∈ D') :
    LinearMap.range (linearFromOutput e) ≤ linearOutputImage D' :=
  le_iSup (fun e : D' => LinearMap.range (linearFromOutput e.val)) ⟨e, he⟩

/-- Two independent output vectors already generate the whole first cokernel. -/
theorem linearOutputImage_eq_top_of_two_le (D' : Submodule K (DegreeZero K t))
    (hD : 2 ≤ Module.finrank K D') : linearOutputImage D' = ⊤ := by
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank hD
  let f : D' →ₗ[K] (Fin 3 → K) := outputCoordinates.comp D'.subtype
  have hf : Function.Injective f := outputCoordinates_injective.comp D'.injective_subtype
  have hfv : LinearIndependent K (fun i => f (v i)) := hv.map_injOn f hf.injOn
  apply Submodule.dualAnnihilator_eq_bot_iff.mp
  apply eq_bot_iff.mpr
  intro φ hφ
  change φ = 0
  apply dualFactor_injective
  rw [map_zero]
  apply two_equations_zero hfv _ (dualFactor_bounds φ).1
  intro i
  apply annihilator_equation
  rw [Submodule.mem_dualAnnihilator] at hφ ⊢
  intro x hx
  exact hφ x (linearFromOutput_range_le D' (v i).val (v i).property hx)

/-- A nonzero output subspace has at least `t-1` independent linear products. -/
theorem nonzero_output_linear_finrank (ht : 2 ≤ t)
    {D' : Submodule K (DegreeZero K t)} (hD : D' ≠ ⊥) :
    t - 1 ≤ Module.finrank K (linearOutputImage D') := by
  obtain ⟨e, he, hne⟩ := D'.ne_bot_iff.mp hD
  have hc : outputCoefficients e ≠ 0 := by
    intro h
    apply hne
    apply outputCoefficients_injective
    exact h.trans (by funext d; simp [outputCoefficients])
  exact (single_output_linear_finrank ht hc).trans
    (Submodule.finrank_mono (linearFromOutput_range_le D' e he))

/-- The manuscript's uniform output bound, expressed without rational division. -/
theorem output_linear_finrank_bound (ht : 2 ≤ t) (D' : Submodule K (DegreeZero K t)) :
    min (Module.finrank K D') 2 * (t - 1) ≤ Module.finrank K (linearOutputImage D') := by
  by_cases hD : 2 ≤ Module.finrank K D'
  · rw [min_eq_right hD, linearOutputImage_eq_top_of_two_le D' hD,
      finrank_top, cokernel_degreeOne_finrank (by omega)]
  · by_cases hzero : Module.finrank K D' = 0
    · simp [hzero]
    · have hdim : Module.finrank K D' = 1 := by omega
      rw [hdim]
      rw [min_eq_left (by decide : 1 ≤ 2), one_mul]
      apply nonzero_output_linear_finrank ht
      intro hbot
      simp [hbot] at hzero

end Quartic.ConvolutionOutputLinear
