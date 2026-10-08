import Quartic.Homogeneous
import Mathlib.LinearAlgebra.Finsupp.Defs

/-!
# Coefficients in a disjoint set of free polynomial variables

The first `t` variables are the core variables and the last `w` are free.
Taking the coefficient of a fixed free-variable monomial gives an actual
polynomial in the core variables. Homogeneous degrees and multiplication by
core variables behave exactly as required by polynomial extension.
-/

noncomputable section
namespace Quartic.FreeCoefficients
open MvPolynomial
variable {K : Type*} [Field K] {t w d : ℕ}

/-- Combine the exponent vectors on two disjoint finite variable sets. -/
def mergeExponent (a : Fin t →₀ ℕ) (b : Fin w →₀ ℕ) : Fin (t + w) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (Fin.addCases a b)

@[simp] theorem mergeExponent_left (a : Fin t →₀ ℕ) (b : Fin w →₀ ℕ) (i : Fin t) :
    mergeExponent a b (Fin.castAdd w i) = a i := by simp [mergeExponent]

@[simp] theorem mergeExponent_right (a : Fin t →₀ ℕ) (b : Fin w →₀ ℕ) (i : Fin w) :
    mergeExponent a b (Fin.natAdd t i) = b i := by simp [mergeExponent]

def coreExponent (e : Fin (t + w) →₀ ℕ) : Fin t →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => e (Fin.castAdd w i))

def freeExponent (e : Fin (t + w) →₀ ℕ) : Fin w →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => e (Fin.natAdd t i))

@[simp] theorem merge_core_free (e : Fin (t + w) →₀ ℕ) :
    mergeExponent (coreExponent e) (freeExponent e) = e := by
  ext i
  refine Fin.addCases ?_ ?_ i <;> intro k <;> simp [coreExponent, freeExponent]

@[simp] theorem mergeExponent_degree (a : Fin t →₀ ℕ) (b : Fin w →₀ ℕ) :
    (mergeExponent a b).degree = a.degree + b.degree := by
  simp only [Finsupp.degree_eq_sum]
  rw [Fin.sum_univ_add]
  simp

theorem mergeExponent_left_injective (b : Fin w →₀ ℕ) :
    Function.Injective (fun a : Fin t →₀ ℕ => mergeExponent a b) := by
  intro a c h
  ext i
  simpa using congrArg (fun e => e (Fin.castAdd w i)) h

theorem mergeExponent_eq_iff (a c : Fin t →₀ ℕ) (b e : Fin w →₀ ℕ) :
    mergeExponent a b = mergeExponent c e ↔ a = c ∧ b = e := by
  constructor
  · intro h
    constructor
    · ext i
      simpa using congrArg (fun v => v (Fin.castAdd w i)) h
    · ext i
      simpa using congrArg (fun v => v (Fin.natAdd t i)) h
  · rintro ⟨rfl, rfl⟩
    rfl


/-- Subtracting one core variable leaves the free exponents unchanged. -/
theorem mergeExponent_sub_single (a : Fin t →₀ ℕ) (b : Fin w →₀ ℕ) (i : Fin t) :
    mergeExponent (a - Finsupp.single i 1) b =
      mergeExponent a b - Finsupp.single (Fin.castAdd w i) 1 := by
  ext k
  refine Fin.addCases ?_ ?_ k
  · intro l
    simp [Finsupp.single_apply]
  · intro l
    have hne : Fin.castAdd w i ≠ Fin.natAdd t l := by
      intro h
      have := congrArg Fin.val h
      simp at this
      omega
    simp [hne]


/-- Extract the coefficient polynomial of one free-variable monomial. -/
def freeCoeff (b : Fin w →₀ ℕ) : Quartic.Poly K (t + w) →ₗ[K] Quartic.Poly K t where
  toFun p := AddMonoidAlgebra.ofCoeff (Finsupp.comapDomain
    (fun a : Fin t →₀ ℕ => mergeExponent a b) p.coeff (mergeExponent_left_injective b).injOn)
  map_add' p q := by ext a; simp [Finsupp.comapDomain_apply]
  map_smul' c p := by ext a; simp [Finsupp.comapDomain_apply]

@[simp] theorem freeCoeff_coeff (b : Fin w →₀ ℕ) (p : Quartic.Poly K (t + w))
    (a : Fin t →₀ ℕ) : (freeCoeff b p).coeff a = p.coeff (mergeExponent a b) := by
  rfl

/-- Extraction from a monomial keeps exactly the requested free exponent. -/
theorem freeCoeff_monomial (a : Fin t →₀ ℕ) (b e : Fin w →₀ ℕ) (c : K) :
    freeCoeff b (monomial (mergeExponent a e) c) = if e = b then monomial a c else 0 := by
  classical
  apply MvPolynomial.ext
  intro f
  rw [freeCoeff_coeff]
  by_cases h : e = b
  · subst e
    simp [coeff_monomial, mergeExponent_eq_iff]
  · simp [coeff_monomial, mergeExponent_eq_iff, h]

/-- Insert one free-monomial factor into every term of a core polynomial. -/
def liftCoeff (b : Fin w →₀ ℕ) : Quartic.Poly K t →ₗ[K] Quartic.Poly K (t + w) :=
  AddMonoidAlgebra.mapDomainLinearMap K K (fun a => mergeExponent a b)

@[simp] theorem liftCoeff_monomial (b : Fin w →₀ ℕ) (a : Fin t →₀ ℕ) (c : K) :
    liftCoeff b (monomial a c) = monomial (mergeExponent a b) c :=
  AddMonoidAlgebra.mapDomainLinearMap_single _ _ _

/-- Insertion and extraction give mutually orthogonal coefficient components. -/
theorem freeCoeff_liftCoeff (b e : Fin w →₀ ℕ) (p : Quartic.Poly K t) :
    freeCoeff b (liftCoeff e p) = if e = b then p else 0 := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial a c =>
      exact (congrArg (freeCoeff b) (liftCoeff_monomial e a c)).trans
        (freeCoeff_monomial a b e c)
  | add p q hp hq =>
      simp only [map_add, hp, hq]
      split_ifs <;> simp

/-- Coefficients of the inserted polynomial have the expected disjoint support. -/
theorem liftCoeff_coeff (b e : Fin w →₀ ℕ) (p : Quartic.Poly K t) (a : Fin t →₀ ℕ) :
    (liftCoeff b p).coeff (mergeExponent a e) = if b = e then p.coeff a else 0 := by
  rw [← freeCoeff_coeff, freeCoeff_liftCoeff]
  split_ifs <;> simp

/-- Inserting a free monomial adds its degree to the core homogeneous degree. -/
theorem liftCoeff_homogeneous (b : Fin w →₀ ℕ) (p : Quartic.Poly K t)
    (hp : p.IsHomogeneous d) : (liftCoeff b p).IsHomogeneous (d + b.degree) := by
  intro e he
  have hc := congrArg (fun q : Quartic.Poly K t => q.coeff (coreExponent e))
    (freeCoeff_liftCoeff (freeExponent e) b p)
  simp only [freeCoeff_coeff, merge_core_free] at hc
  have hb : b = freeExponent e := by
    by_contra h
    simp [h] at hc
    exact he hc
  rw [ite_eq_left_iff.mpr (fun h => (h hb).elim)] at hc
  have hcore := hp (by rwa [← hc])
  change (Finsupp.weight (fun _ : Fin t => (1 : ℕ))) (coreExponent e) = d at hcore
  rw [← Finsupp.degree_eq_weight_one] at hcore
  change (Finsupp.weight (fun _ : Fin (t + w) => (1 : ℕ))) e = d + b.degree
  rw [← Finsupp.degree_eq_weight_one, ← merge_core_free e, mergeExponent_degree, hcore, hb]


/-- Core-variable multiplication commutes with free coefficient extraction. -/
theorem freeCoeff_core_X_mul (b : Fin w →₀ ℕ) (p : Quartic.Poly K (t + w)) (i : Fin t) :
    freeCoeff b (X (Fin.castAdd w i) * p) = X i * freeCoeff b p := by
  classical
  apply MvPolynomial.ext
  intro a
  rw [freeCoeff_coeff, coeff_X_mul', coeff_X_mul']
  simp only [Finsupp.mem_support_iff, mergeExponent_left]
  split_ifs
  · rw [← mergeExponent_sub_single, freeCoeff_coeff]
  · rfl

/-- Insertion of a free monomial commutes with multiplication by a core variable. -/
theorem liftCoeff_core_X_mul (b : Fin w →₀ ℕ) (p : Quartic.Poly K t) (i : Fin t) :
    liftCoeff b (X i * p) = X (Fin.castAdd w i) * liftCoeff b p := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial a c =>
      have hm : mergeExponent (Finsupp.single i 1 + a) b =
          Finsupp.single (Fin.castAdd w i) 1 + mergeExponent a b := by
        ext k
        refine Fin.addCases ?_ ?_ k
        · intro l
          simp [Finsupp.single_apply]
        · intro l
          have hne : Fin.castAdd w i ≠ Fin.natAdd t l := by
            intro h
            have := congrArg Fin.val h
            simp at this
            omega
          simp [hne]
      simp [MvPolynomial.X, monomial_mul_monomial, hm]
  | add p q hp hq => simp [mul_add, hp, hq]


/-- All free-variable coefficients together determine the original polynomial. -/
theorem eq_zero_of_freeCoeff (p : Quartic.Poly K (t + w))
    (hp : ∀ b : Fin w →₀ ℕ, freeCoeff b p = 0) : p = 0 := by
  apply MvPolynomial.ext
  intro e
  have h := congrArg (fun q : Quartic.Poly K t => q.coeff (coreExponent e)) (hp (freeExponent e))
  simpa using h

/-- Taking a free-variable coefficient subtracts exactly its free degree. -/
theorem freeCoeff_homogeneous (p : Quartic.Poly K (t + w)) (hp : p.IsHomogeneous d)
    (b : Fin w →₀ ℕ) : (freeCoeff b p).IsHomogeneous (d - b.degree) := by
  intro a ha
  have h := hp (by simpa using ha : p.coeff (mergeExponent a b) ≠ 0)
  change (Finsupp.weight (fun _ : Fin (t + w) => (1 : ℕ))) (mergeExponent a b) = d at h
  rw [← Finsupp.degree_eq_weight_one] at h
  change (Finsupp.weight (fun _ : Fin t => (1 : ℕ))) a = d - b.degree
  rw [← Finsupp.degree_eq_weight_one]
  rw [mergeExponent_degree] at h
  omega

/-- A free monomial of excessive degree has zero coefficient in a homogeneous polynomial. -/
theorem freeCoeff_eq_zero_of_degree_lt (p : Quartic.Poly K (t + w))
    (hp : p.IsHomogeneous d) (b : Fin w →₀ ℕ) (hb : d < b.degree) : freeCoeff b p = 0 := by
  apply MvPolynomial.ext
  intro a
  by_contra h
  have h' : p.coeff (mergeExponent a b) ≠ 0 := by simpa using h
  have hd := hp h'
  change (Finsupp.weight (fun _ : Fin (t + w) => (1 : ℕ))) (mergeExponent a b) = d at hd
  rw [← Finsupp.degree_eq_weight_one] at hd
  rw [mergeExponent_degree] at hd
  omega

/-- Free coefficient extraction restricted to an actual homogeneous polynomial space. -/
def homogeneousCoeff (b : Fin w →₀ ℕ) :
    Quartic.Forms K (t + w) d →ₗ[K] Quartic.Forms K t (d - b.degree) :=
  ((freeCoeff b).comp (Quartic.Forms K (t + w) d).subtype).codRestrict _
    (fun p => freeCoeff_homogeneous p.val p.property b)

end Quartic.FreeCoefficients
