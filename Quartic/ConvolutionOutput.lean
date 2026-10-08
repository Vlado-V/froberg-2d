import Quartic.ConvolutionHilbert
import Quartic.ConvolutionMultiplication

/-!
# The quadratic image of the actual output space

Every nonzero vector in the three-dimensional degree-zero output space
multiplies onto the actual second graded convolution cokernel. The proof
contracts the distinguished slot of the checked inverse system and cancels
a nonzero explicit bivariate polynomial.
-/

noncomputable section
namespace Quartic.ConvolutionOutput
open MvPolynomial ConvolutionPresentation ConvolutionDual ConvolutionInverse
open ConvolutionSlots ConvolutionTuples ConvolutionFactor ConvolutionConstantSlot
variable {K : Type*} [Field K] {t : ℕ}

/-- Multiply an output coefficient vector by a homogeneous polynomial. -/
def outputTarget (c : Fin 3 → K) (j : ℕ) : Forms K t j →ₗ[K] Target K t j :=
  LinearMap.pi fun d => c d • LinearMap.id

@[simp] theorem outputTarget_apply (c : Fin 3 → K) (j : ℕ) (a : Forms K t j) (d : Fin 3) :
    outputTarget c j a d = c d • a := rfl

/-- Quadratic multiplication from a fixed actual output vector. -/
def outputQuadratic (c : Fin 3 → K) : Forms K t 2 →ₗ[K] Cokernel K t 1 :=
  (Submodule.mkQ _).comp (outputTarget c 2)

@[simp] theorem outputQuadratic_apply (c : Fin 3 → K) (a : Forms K t 2) :
    outputQuadratic c a = Submodule.Quotient.mk (outputTarget c 2 a) := rfl

/-- Contract the three distinguished coefficients against an output vector. -/
def contractOutput (c : Fin 3 → K) (F : Slots K 2) : Poly K 2 :=
  ∑ d : Fin 3, c d • (optionEquivLeft K (Fin 2) F).coeff d.val

/-- The explicit nonzero factor produced by output contraction. -/
def outputFactor (c : Fin 3 → K) : Poly K 2 :=
  C (c 0) * X 0 * X 1 - C (c 1) * (X 0 + X 1) + C (c 2)

@[simp] theorem optionEquiv_rename (H : Poly K 2) :
    optionEquivLeft K (Fin 2) (rename Option.some H) = Polynomial.C H := by
  induction H using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

theorem contractOutput_factor (c : Fin 3 → K) (H : Poly K 2) :
    contractOutput c (diagonalProduct K 2 * rename Option.some H) = outputFactor c * H := by
  have hdiag : optionEquivLeft K (Fin 2) (diagonalProduct K 2) =
      Polynomial.X ^ 2 - Polynomial.C (X 0 + X 1) * Polynomial.X +
        Polynomial.C (X 0 * X 1 : Poly K 2) := by
    simp only [diagonalProduct, Fin.prod_univ_two, map_mul, map_sub,
      optionEquivLeft_X_none, optionEquivLeft_X_some, map_add]
    ring
  simp only [contractOutput, map_mul, optionEquiv_rename, hdiag,
    Polynomial.coeff_mul_C, Polynomial.coeff_add, Polynomial.coeff_sub,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X,
    Polynomial.coeff_C, Fin.sum_univ_three]
  norm_num
  simp only [outputFactor, smul_eq_C_mul]
  ring

theorem outputFactor_ne_zero {c : Fin 3 → K} (hc : c ≠ 0) : outputFactor c ≠ 0 := by
  intro h
  have h0 := congrArg (fun F : Poly K 2 => F.coeff (Finsupp.single 0 1 + Finsupp.single 1 1)) h
  have h1 := congrArg (fun F : Poly K 2 => F.coeff (Finsupp.single 0 1)) h
  have h2 := congrArg (fun F : Poly K 2 => F.coeff 0) h
  have he01 : (Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1 : Fin 2 →₀ ℕ) ≠ 0 := by
    intro he; have := congrArg (fun e => e 0) he; simp at this
  have he01a : (Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1 : Fin 2 →₀ ℕ) ≠ Finsupp.single 0 1 := by
    intro he; have := congrArg (fun e => e 1) he; simp at this
  have he01b : (Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1 : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 1 := by
    intro he; have := congrArg (fun e => e 0) he; simp at this
  have hs10 : (Finsupp.single (1 : Fin 2) 1 : Fin 2 →₀ ℕ) ≠ Finsupp.single 0 1 := by
    intro he; have := congrArg (fun e => e 0) he; simp at this
  simp only [outputFactor, mul_add, X, C_mul_monomial, monomial_mul_monomial,
    mul_one, AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_sub,
    Finsupp.add_apply, Finsupp.sub_apply, coeff_monomial, coeff_C] at h0 h1 h2
  simp [he01, he01.symm, he01a, he01a.symm, he01b.symm, hs10] at h0 h1 h2
  apply hc
  funext d
  fin_cases d <;> simp_all

/-- The scalar row expansion is the literal target vector. -/
theorem outputTarget_monomial (c : Fin 3 → K) (e : Fin t →₀ ℕ) (he : e.degree = 2) :
    outputTarget c 2 (monomialForm e he) = ∑ d : Fin 3, c d • rowMonomial d e he := by
  classical
  funext d
  simp [outputTarget, rowMonomial, Pi.single_apply]

/-- Ordinary slot exponents record the entries of the ordered tuple. -/
def ordinaryExponent (v : Fin 2 → Fin t) : Fin 2 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (v i).val)

@[simp] theorem slotExponent_some_eq (d : ℕ) (v : Fin 2 → Fin t) :
    (slotExponent d (fun i => (v i).val)).some = ordinaryExponent v := by
  ext i
  simp [ordinaryExponent]

/-- Extracting one distinguished row from the ordered encoding. -/
theorem distinguishedCoefficient_encode (φ : Module.Dual K (Target K t 2)) (d : Fin 3) :
    (optionEquivLeft K (Fin 2) (encode φ)).coeff d.val =
      ∑ v : Fin 2 → Fin t, monomial (ordinaryExponent v)
        (φ (rowMonomial d (tupleExponent v) (tupleExponent_degree v))) := by
  classical
  simp only [encode, ofCoefficients, map_sum, Fintype.sum_prod_type,
    Polynomial.finsetSum_coeff, optionEquivLeft_monomial, slotExponent_none,
    slotExponent_some_eq, Polynomial.coeff_monomial]
  simp only [Fin.val_inj]
  rw [Finset.sum_eq_single d]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

/-- Contraction of the encoded polynomial records actual output products. -/
theorem contractOutput_encode (c : Fin 3 → K) (φ : Module.Dual K (Target K t 2)) :
    contractOutput c (encode φ) =
      ∑ v : Fin 2 → Fin t, monomial (ordinaryExponent v)
        (φ (outputTarget c 2 (monomialForm (tupleExponent v) (tupleExponent_degree v)))) := by
  classical
  simp only [contractOutput, distinguishedCoefficient_encode, Finset.smul_sum,
    smul_monomial, smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  rw [outputTarget_monomial, map_sum]
  simp only [map_smul, smul_eq_mul]
  exact (map_sum (monomial (ordinaryExponent v)) _ _).symm

/-- Every nonzero coefficient vector multiplies onto the actual degree-two cokernel. -/
theorem outputQuadratic_surjective {c : Fin 3 → K} (hc : c ≠ 0) :
    Function.Surjective (outputQuadratic (t := t) c) := by
  apply LinearMap.dualMap_injective_iff.mp
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro φ hφ
  change φ = 0
  change (outputQuadratic c).dualMap φ = 0 at hφ
  let ψ : annihilator K t 1 := cokernelDualEquiv K t 1 φ
  have hcon : contractOutput c (encode ψ.val) = 0 := by
    rw [contractOutput_encode]
    apply Finset.sum_eq_zero
    intro v _
    have hv := congrArg (fun f : Module.Dual K (Forms K t 2) =>
      f (monomialForm (tupleExponent v) (tupleExponent_degree v))) hφ
    change φ (outputQuadratic c (monomialForm (tupleExponent v) (tupleExponent_degree v))) = 0 at hv
    change monomial _ (φ (outputQuadratic c _)) = 0
    rw [hv, map_zero]
  have hnone : (inverseFactor ψ).degreeOf none = 0 := by
    have h := (inverseFactor_bounds ψ).1
    omega
  rw [inverseFactor_spec, ← rename_erase_of_degree_none_zero (inverseFactor ψ) hnone,
    contractOutput_factor] at hcon
  have he : erase (inverseFactor ψ) = 0 := (mul_eq_zero.mp hcon).resolve_left (outputFactor_ne_zero hc)
  have hz : inverseFactor ψ = 0 := by
    rw [← rename_erase_of_degree_none_zero (inverseFactor ψ) hnone, he, map_zero]
  have hzero : inverseFactor (0 : annihilator K t 1) = 0 :=
    (inverseFactorLinear (K := K) (t := t) (j := 1)).map_zero
  have hψ : ψ = 0 := inverseFactor_injective (hz.trans hzero.symm)
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ b =>
    have hb := congrArg (fun θ : annihilator K t 1 => θ.val b) hψ
    exact hb

/-- Coordinates of an actual degree-zero target vector. -/
def outputCoefficients (e : DegreeZero K t) : Fin 3 → K :=
  fun d => (e d).val.coeff 0

theorem degreeZero_reconstruct (a : Forms K t 0) : a.val = C (a.val.coeff 0) :=
  totalDegree_eq_zero_iff_eq_C.mp ((totalDegree_zero_iff_isHomogeneous (Fin t)).mpr a.property)

theorem outputCoefficients_injective : Function.Injective (outputCoefficients (K := K) (t := t)) := by
  intro e f h
  funext d
  apply Subtype.ext
  rw [degreeZero_reconstruct (e d), degreeZero_reconstruct (f d)]
  exact congrArg C (congrFun h d)

/-- The coordinate construction is ordinary polynomial multiplication by the
actual homogeneous degree-zero output. -/
theorem outputTarget_from_degreeZero_val (e : DegreeZero K t) (j : ℕ)
    (a : Forms K t j) (d : Fin 3) :
    (outputTarget (outputCoefficients e) j a d).val = (e d).val * a.val := by
  change outputCoefficients e d • a.val = _
  rw [smul_eq_C_mul, degreeZero_reconstruct (e d)]
  rfl

/-- Quadratic multiplication by an actual degree-zero output vector. -/
def quadraticFromOutput (e : DegreeZero K t) : Forms K t 2 →ₗ[K] Cokernel K t 1 :=
  outputQuadratic (outputCoefficients e)

theorem quadraticFromOutput_surjective {e : DegreeZero K t} (he : e ≠ 0) :
    Function.Surjective (quadraticFromOutput e) := by
  apply outputQuadratic_surjective
  intro h
  apply he
  apply outputCoefficients_injective
  exact h.trans (by funext d; simp [outputCoefficients])

/-- The quadratic multiplication image of an actual output subspace. -/
def quadraticOutputImage (D' : Submodule K (DegreeZero K t)) : Submodule K (Cokernel K t 1) :=
  ⨆ e : D', LinearMap.range (quadraticFromOutput e.val)

/-- Every nonzero output subspace generates the whole second graded piece. -/
theorem quadraticOutputImage_eq_top {D' : Submodule K (DegreeZero K t)} (hD : D' ≠ ⊥) :
    quadraticOutputImage D' = ⊤ := by
  obtain ⟨e, he, hne⟩ := D'.ne_bot_iff.mp hD
  apply top_unique
  have hsurj := LinearMap.range_eq_top.mpr (quadraticFromOutput_surjective hne)
  rw [← hsurj]
  exact le_iSup (fun e : D' => LinearMap.range (quadraticFromOutput e.val)) ⟨e, he⟩

end Quartic.ConvolutionOutput
