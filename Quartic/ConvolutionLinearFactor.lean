import Quartic.ConvolutionEvaluation
import Quartic.ConvolutionConstantSlot

/-!
# Two-component coordinates on the degree-one inverse factor

The factor `H(s,z)=H₀(z)+s H₁(z)` is sent to `(H₁,-H₀)` in two copies of
the dual of the coefficient space. This is an injective linear map on the
actual degree-one convolution dual. Evaluated contraction becomes `(G,aG)`,
providing the precise bridge to the symmetric contraction bound.
-/

namespace Quartic.ConvolutionLinearFactor

noncomputable section

open MvPolynomial Quartic.ConvolutionFactor Quartic.ConvolutionSlots
open Quartic.ConvolutionDual Quartic.ConvolutionInverse Quartic.ConvolutionEvaluation
open Quartic.ConvolutionConstantSlot

variable {K : Type*} [Field K] {t p : ℕ}

abbrev oneExponent (d n : ℕ) : Option (Fin 1) →₀ ℕ :=
  slotExponent d (fun _ => n)

theorem oneExponent_all (e : Option (Fin 1) →₀ ℕ) :
    oneExponent (e none) (e (some 0)) = e := by
  ext o
  cases o with
  | none => simp
  | some i => fin_cases i; simp

/-- A coefficient row is a linear functional on the finite coefficient space. -/
def coefficientFunctional (p d : ℕ) : Slots K 1 →ₗ[K] Module.Dual K (Fin p → K) :=
  ∑ i : Fin p, (MvPolynomial.lcoeff K (oneExponent d i.val)).smulRight (LinearMap.proj i)

@[simp] theorem coefficientFunctional_apply (p d : ℕ) (H : Slots K 1) (v : Fin p → K) :
    coefficientFunctional p d H v = ∑ i : Fin p, H.coeff (oneExponent d i.val) * v i := by
  simp [coefficientFunctional]

@[simp] theorem coefficientFunctional_single (p d : ℕ) (H : Slots K 1) (i : Fin p) :
    coefficientFunctional p d H (Pi.single i 1) = H.coeff (oneExponent d i.val) := by
  classical
  simp [coefficientFunctional_apply, Pi.single_apply]

/-- Coefficients outside a separate degree bound vanish. -/
theorem coeff_zero_of_degreeOf_lt (H : Slots K 1) (e : Option (Fin 1) →₀ ℕ)
    (o : Option (Fin 1)) (h : H.degreeOf o < e o) : H.coeff e = 0 :=
  MvPolynomial.notMem_support_iff.mp (MvPolynomial.notMem_support_of_degreeOf_lt o h)

/-- The two bounded coefficient rows determine every linear-in-`s` factor. -/
theorem eq_of_two_coefficient_rows (hp : 1 ≤ p) (H G : Slots K 1)
    (hHs : H.degreeOf none ≤ 1) (hGs : G.degreeOf none ≤ 1)
    (hHz : H.degreeOf (some 0) ≤ p - 1) (hGz : G.degreeOf (some 0) ≤ p - 1)
    (h : ∀ (d : Fin 2) (i : Fin p),
      H.coeff (oneExponent d.val i.val) = G.coeff (oneExponent d.val i.val)) : H = G := by
  apply MvPolynomial.ext
  intro e
  by_cases hs : e none ≤ 1
  · by_cases hz : e (some 0) < p
    · have he := oneExponent_all e
      rw [← he]
      exact h ⟨e none, by omega⟩ ⟨e (some 0), hz⟩
    · rw [coeff_zero_of_degreeOf_lt H e (some 0) (by omega),
        coeff_zero_of_degreeOf_lt G e (some 0) (by omega)]
  · rw [coeff_zero_of_degreeOf_lt H e none (by omega),
      coeff_zero_of_degreeOf_lt G e none (by omega)]

/-- Two coefficient rows in the coordinates `(H₁,-H₀)`. -/
def coefficientPairMap (p : ℕ) : Slots K 1 →ₗ[K]
    Module.Dual K (Fin p → K) × Module.Dual K (Fin p → K) :=
  (coefficientFunctional p 1).prod (-(coefficientFunctional p 0))

/-- The actual degree-one dual in the coordinates `(H₁,-H₀)`. -/
def pairMap : annihilator K t 0 →ₗ[K]
    (Module.Dual K (Fin (t - 1) → K)) × (Module.Dual K (Fin (t - 1) → K)) :=
  (coefficientPairMap (t - 1)).comp
    (inverseFactorLinear (K := K) (t := t) (j := 0))

@[simp] theorem pairMap_apply (φ : annihilator K t 0) :
    pairMap φ = (coefficientFunctional (t - 1) 1 (inverseFactor φ),
      -coefficientFunctional (t - 1) 0 (inverseFactor φ)) := rfl

/-- No actual degree-one dual information is lost in the two coefficient rows. -/
theorem pairMap_injective (ht : 2 ≤ t) : Function.Injective (pairMap (K := K) (t := t)) := by
  intro φ ψ h
  apply inverseFactor_injective
  apply eq_of_two_coefficient_rows (p := t - 1) (by omega) (inverseFactor φ) (inverseFactor ψ)
  · simpa using (inverseFactor_bounds φ).1
  · simpa using (inverseFactor_bounds ψ).1
  · exact (inverseFactor_bounds φ).2 0
  · exact (inverseFactor_bounds ψ).2 0
  · intro d i
    fin_cases d
    · have hc := congrArg (fun x : Module.Dual K (Fin (t - 1) → K) ×
          Module.Dual K (Fin (t - 1) → K) => x.2 (Pi.single i 1)) h
      change -(coefficientFunctional (t - 1) 0 (inverseFactor φ) (Pi.single i 1)) =
        -(coefficientFunctional (t - 1) 0 (inverseFactor ψ) (Pi.single i 1)) at hc
      simpa only [coefficientFunctional_single, neg_inj] using hc
    · have hc := congrArg (fun x : Module.Dual K (Fin (t - 1) → K) ×
          Module.Dual K (Fin (t - 1) → K) => x.1 (Pi.single i 1)) h
      change coefficientFunctional (t - 1) 1 (inverseFactor φ) (Pi.single i 1) =
        coefficientFunctional (t - 1) 1 (inverseFactor ψ) (Pi.single i 1) at hc
      simpa only [coefficientFunctional_single] using hc

/-- Passage to the pair-coordinate image preserves every subspace dimension. -/
theorem pairMap_finrank_image (ht : 2 ≤ t) (P : Submodule K (annihilator K t 0)) :
    Module.finrank K (P.map pairMap) = Module.finrank K P :=
  (Submodule.equivMapOfInjective pairMap (pairMap_injective ht) P).finrank_eq.symm

/-- Polynomials obtained by renaming only ordinary variables have no distinguished variable. -/
theorem degree_none_rename (f : MvPolynomial (Fin 1) K) :
    (MvPolynomial.rename Option.some f).degreeOf none = 0 := by
  by_contra h
  obtain ⟨i, _, hi⟩ := MvPolynomial.mem_vars_rename Option.some f
    (MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mpr h)
  cases hi

/-- Specialization of the second ordinary variable in a bivariate polynomial. -/
def specializeSecond (a : K) : MvPolynomial (Fin 2) K →ₐ[K] MvPolynomial (Fin 1) K :=
  MvPolynomial.aeval fun i => if i = 0 then X 0 else C a

theorem evaluateSecond_rename (a : K) (f : MvPolynomial (Fin 2) K) :
    evaluateSecond a (MvPolynomial.rename Option.some f) =
      MvPolynomial.rename Option.some (specializeSecond a f) := by
  have h : (evaluateSecond a).comp (MvPolynomial.rename Option.some) =
      (MvPolynomial.rename Option.some).comp (specializeSecond a) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [AlgHom.comp_apply, evaluateSecond, specializeSecond]
  exact congrArg (fun g : MvPolynomial (Fin 2) K →ₐ[K] Slots K 1 => g f) h

theorem evaluateSecond_degree_none_zero (a : K) (H : Slots K 2)
    (hH : H.degreeOf none = 0) : (evaluateSecond a H).degreeOf none = 0 := by
  rw [← rename_erase_of_degree_none_zero H hH, evaluateSecond_rename]
  exact degree_none_rename _

theorem oneExponent_sub_none (n : ℕ) :
    oneExponent 1 n - Finsupp.single none 1 = oneExponent 0 n := by
  ext o
  cases o with
  | none => simp
  | some i => fin_cases i; simp

theorem coeff_linear_product_one (a : K) (G : Slots K 1)
    (hG : G.degreeOf none = 0) (n : ℕ) :
    ((X none - C a) * G).coeff (oneExponent 1 n) = G.coeff (oneExponent 0 n) := by
  have hzero : G.coeff (oneExponent 1 n) = 0 :=
    coeff_zero_of_degreeOf_lt G _ none (by simp [hG])
  have hmem : none ∈ (oneExponent 1 n).support := by simp [Finsupp.mem_support_iff]
  simp only [sub_mul, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, coeff_X_mul', coeff_C_mul,
    hmem, ite_true, oneExponent_sub_none, hzero, mul_zero, sub_zero]

theorem coeff_linear_product_zero (a : K) (G : Slots K 1) (n : ℕ) :
    ((X none - C a) * G).coeff (oneExponent 0 n) = -a * G.coeff (oneExponent 0 n) := by
  have hmem : none ∉ (oneExponent 0 n).support := by simp [Finsupp.mem_support_iff]
  simp only [sub_mul, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, coeff_X_mul', coeff_C_mul,
    hmem, ite_false, zero_sub, neg_mul]

theorem coefficientFunctional_linear_product_one (p : ℕ) (a : K) (G : Slots K 1)
    (hG : G.degreeOf none = 0) :
    coefficientFunctional p 1 ((X none - C a) * G) = coefficientFunctional p 0 G := by
  apply LinearMap.ext
  intro v
  simp only [coefficientFunctional_apply, coeff_linear_product_one a G hG]

theorem coefficientFunctional_linear_product_zero (p : ℕ) (a : K) (G : Slots K 1) :
    -coefficientFunctional p 0 ((X none - C a) * G) = a • coefficientFunctional p 0 G := by
  apply LinearMap.ext
  intro v
  simp only [LinearMap.neg_apply, LinearMap.smul_apply, smul_eq_mul,
    coefficientFunctional_apply, coeff_linear_product_zero, Finset.mul_sum]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The polynomial-level coordinate formula for any constant-in-`s` factor. -/
theorem coefficientPairMap_linear_product (p : ℕ) (a : K) (G : Slots K 1)
    (hG : G.degreeOf none = 0) :
    coefficientPairMap p ((X none - C a) * G) =
      (coefficientFunctional p 0 G, a • coefficientFunctional p 0 G) := by
  change (coefficientFunctional p 1 _, -coefficientFunctional p 0 _) = _
  rw [coefficientFunctional_linear_product_one _ _ _ hG,
    coefficientFunctional_linear_product_zero]

/-- In particular, the formula applies to every polynomial in the ordinary variable. -/
theorem coefficientPairMap_linear_product_rename (p : ℕ) (a : K)
    (G : MvPolynomial (Fin 1) K) :
    coefficientPairMap p ((X none - C a) * MvPolynomial.rename Option.some G) =
      (coefficientFunctional p 0 (MvPolynomial.rename Option.some G),
        a • coefficientFunctional p 0 (MvPolynomial.rename Option.some G)) :=
  coefficientPairMap_linear_product p a _ (degree_none_rename G)

/-- Evaluated actual contraction is exactly a pair `(G,aG)` in these coordinates. -/
theorem pairMap_evaluatedContract (a : K) (φ : annihilator K t 1) :
    pairMap (evaluatedContract a φ) =
      (coefficientFunctional (t - 1) 0 (evaluateSecond a (inverseFactor φ)),
        a • coefficientFunctional (t - 1) 0 (evaluateSecond a (inverseFactor φ))) := by
  have hnone : (inverseFactor φ).degreeOf none = 0 := by
    have h := (inverseFactor_bounds φ).1
    omega
  rw [pairMap_apply, inverseFactor_evaluatedContract,
    coefficientFunctional_linear_product_one _ _ _ (evaluateSecond_degree_none_zero a _ hnone),
    coefficientFunctional_linear_product_zero]

/-- The evaluated pair lies in the transported subspace whenever the actual
contraction lies in the original degree-one annihilator subspace. -/
theorem evaluated_pair_mem_image (a : K) (φ : annihilator K t 1)
    (P : Submodule K (annihilator K t 0)) (h : evaluatedContract a φ ∈ P) :
    (coefficientFunctional (t - 1) 0 (evaluateSecond a (inverseFactor φ)),
      a • coefficientFunctional (t - 1) 0 (evaluateSecond a (inverseFactor φ))) ∈ P.map pairMap :=
  ⟨evaluatedContract a φ, h, pairMap_evaluatedContract a φ⟩

end

end Quartic.ConvolutionLinearFactor
