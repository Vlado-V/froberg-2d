import Froberg.Matching
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Funext

/-! Actual coefficient-polynomial minors for finite families of monomial-supported forms. -/
noncomputable section
namespace Froberg.ProductMinors
open MvPolynomial

variable {K α τ ι : Type*} [CommRing K]

/-- Each permitted monomial of each form has its own independent coefficient. -/
def genericForm (terms : α → Finset (τ →₀ ℕ)) (a : α) :
    MvPolynomial τ (MvPolynomial (α × (τ →₀ ℕ)) K) :=
  ∑ m ∈ terms a, C (X (a,m)) * monomial m 1

/-- Select one monomial in each form. -/
def monomialValues [DecidableEq (τ →₀ ℕ)] (c : α → τ →₀ ℕ) :
    α × (τ →₀ ℕ) → K := fun p => if p.2 = c p.1 then 1 else 0

/-- Specialization of the actual generic polynomial to any permitted monomial. -/
theorem genericForm_specialize [DecidableEq (τ →₀ ℕ)]
    (terms : α → Finset (τ →₀ ℕ)) (c : α → τ →₀ ℕ) (a : α)
    (hc : c a ∈ terms a) :
    MvPolynomial.map (MvPolynomial.eval (monomialValues c))
      (genericForm (K := K) terms a) = monomial (c a) 1 := by
  classical
  simp only [genericForm, map_sum, map_mul, map_C, eval_X, map_monomial, map_one,
    monomialValues]
  simp [hc]

/-- The coefficient minor selected by the prescribed product monomials. -/
def productMinor (terms : α → Finset (τ →₀ ℕ)) (left right : ι → α)
    (rows : ι → τ →₀ ℕ) : Matrix ι ι (MvPolynomial (α × (τ →₀ ℕ)) K) :=
  fun i j => ((genericForm terms (left j)) * (genericForm terms (right j))).coeff (rows i)

/-- A consistent selection of factor monomials with pairwise distinct products
certifies that the actual coefficient-polynomial determinant is nonzero. -/
theorem productMinor_ne_zero [Nontrivial K] [Fintype ι] [DecidableEq ι]
    [DecidableEq (τ →₀ ℕ)] (terms : α → Finset (τ →₀ ℕ))
    (left right : ι → α) (c : α → τ →₀ ℕ)
    (hl : ∀ i, c (left i) ∈ terms (left i))
    (hr : ∀ i, c (right i) ∈ terms (right i))
    (hinj : Function.Injective (fun i => c (left i) + c (right i))) :
    (productMinor (K := K) terms left right (fun i => c (left i) + c (right i))).det ≠ 0 := by
  classical
  apply Froberg.Matching.determinant_ne_zero_of_identity_specialization _
    (monomialValues c)
  ext i j
  change MvPolynomial.eval (monomialValues c)
    (((genericForm terms (left j)) * (genericForm terms (right j))).coeff
      (c (left i) + c (right i))) = _
  rw [← MvPolynomial.coeff_map, map_mul, genericForm_specialize terms c _ (hl j),
    genericForm_specialize terms c _ (hr j), monomial_mul_monomial, mul_one,
    coeff_monomial]
  simp only [hinj.eq_iff, Matrix.one_apply, eq_comm]

/-- Pairwise disjoint labels make all choices of factor monomials consistent. -/
theorem exists_consistent_choices (labels : ι × Bool → α)
    (hinj : Function.Injective labels) (choices : ι × Bool → τ →₀ ℕ) :
    ∃ c : α → τ →₀ ℕ, ∀ p, c (labels p) = choices p := by
  refine ⟨Function.extend labels choices (fun _ => 0), ?_⟩
  exact hinj.extend_apply choices (fun _ => 0)

/-- The polynomial-minor conclusion for the unique-partner product fibers.
The hypotheses refer only to permitted monomials, distinct matched products,
and the fact that each form label is used at most once in the fiber. -/
theorem disjoint_productMinor_ne_zero [Nontrivial K] [Fintype ι] [DecidableEq ι]
    [DecidableEq (τ →₀ ℕ)] (terms : α → Finset (τ →₀ ℕ))
    (labels : ι × Bool → α) (hlabels : Function.Injective labels)
    (choices : ι × Bool → τ →₀ ℕ)
    (hchoices : ∀ p, choices p ∈ terms (labels p))
    (hinj : Function.Injective (fun i => choices (i,false) + choices (i,true))) :
    (productMinor (K := K) terms (fun i => labels (i,false)) (fun i => labels (i,true))
      (fun i => choices (i,false) + choices (i,true))).det ≠ 0 := by
  obtain ⟨c, hc⟩ := exists_consistent_choices labels hlabels choices
  have h := productMinor_ne_zero (K := K) terms
    (fun i => labels (i,false)) (fun i => labels (i,true)) c
    (fun i => by rw [hc]; exact hchoices (i,false))
    (fun i => by rw [hc]; exact hchoices (i,true))
    (by simpa only [hc] using hinj)
  simpa only [hc] using h

/-- Over an infinite integral domain, finitely many nonzero coefficient
polynomials can be made nonzero at one common assignment. -/
theorem exists_common_specialization {σ δ : Type*} [Fintype δ] [IsDomain K] [Infinite K]
    (p : δ → MvPolynomial σ K) (hp : ∀ i, p i ≠ 0) :
    ∃ values : σ → K, ∀ i, MvPolynomial.eval values (p i) ≠ 0 := by
  classical
  have hprod : (∏ i, p i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  have heval : ∃ values : σ → K, MvPolynomial.eval values (∏ i, p i) ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hprod
    apply MvPolynomial.funext
    intro values
    simpa only [map_zero] using hn values
  obtain ⟨values, hv⟩ := heval
  refine ⟨values, ?_⟩
  simp only [map_prod] at hv
  exact fun i => Finset.prod_ne_zero_iff.mp hv i (Finset.mem_univ i)

/-- A nonzero coefficient minor proves independence of the actual polynomials. -/
theorem linearIndependent_of_coeff_minor [IsDomain K] [Fintype ι] [DecidableEq ι]
    (p : ι → MvPolynomial τ K) (rows : ι → τ →₀ ℕ)
    (hdet : Matrix.det (fun i j : ι => (p j).coeff (rows i)) ≠ 0) :
    LinearIndependent K p := by
  let coordinates : MvPolynomial τ K →ₗ[K] (ι → K) :=
    LinearMap.pi (fun i => MvPolynomial.lcoeff K (rows i))
  apply LinearIndependent.of_comp coordinates
  exact Matrix.linearIndependent_cols_of_det_ne_zero hdet

/-- Finitely many actual product-fiber minors can be realized simultaneously.
This is the final generic-parameter step in the independent-product construction. -/
theorem exists_simultaneous_independent_products {δ : Type*} [Fintype δ]
    {I : δ → Type*} [∀ d, Fintype (I d)] [∀ d, DecidableEq (I d)]
    [IsDomain K] [Infinite K]
    (terms : α → Finset (τ →₀ ℕ)) (left right : (d : δ) → I d → α)
    (rows : (d : δ) → I d → τ →₀ ℕ)
    (hdet : ∀ d, (productMinor (K := K) terms (left d) (right d) (rows d)).det ≠ 0) :
    ∃ values : α × (τ →₀ ℕ) → K, ∀ d,
      LinearIndependent K (fun i : I d =>
        MvPolynomial.map (MvPolynomial.eval values) (genericForm terms (left d i)) *
        MvPolynomial.map (MvPolynomial.eval values) (genericForm terms (right d i))) := by
  classical
  obtain ⟨values, hv⟩ := exists_common_specialization
    (fun d => (productMinor (K := K) terms (left d) (right d) (rows d)).det) hdet
  refine ⟨values, fun d => ?_⟩
  apply linearIndependent_of_coeff_minor _ (rows d)
  have hm : (fun i j =>
      (MvPolynomial.map (MvPolynomial.eval values) (genericForm terms (left d j)) *
       MvPolynomial.map (MvPolynomial.eval values) (genericForm terms (right d j))).coeff
        (rows d i) : Matrix (I d) (I d) K) =
      (MvPolynomial.eval values).mapMatrix (productMinor terms (left d) (right d) (rows d)) := by
    ext i j
    rw [← map_mul, MvPolynomial.coeff_map]
    rfl
  rw [hm, ← RingHom.map_det]
  exact hv d

/-- Independent fiber minors combine when selected rows have zero coefficients
on all other fibers. This is the precise index-degree separation step. -/
theorem linearIndependent_of_fiber_minors {δ : Type*} [DecidableEq δ]
    [IsDomain K] [Fintype ι] [DecidableEq ι]
    (p : ι → MvPolynomial τ K) (key : ι → δ) (rows : ι → τ →₀ ℕ)
    (hdet : ∀ d, Matrix.det (fun i j : {i // key i = d} =>
      (p j.1).coeff (rows i.1)) ≠ 0)
    (hcross : ∀ i j, key i ≠ key j → (p j).coeff (rows i) = 0) :
    LinearIndependent K p := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc j
  have hlocal := Matrix.linearIndependent_cols_of_det_ne_zero (hdet (key j))
  apply Fintype.linearIndependent_iff.mp hlocal (fun i => c i.1) _ ⟨j,rfl⟩
  ext i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.col_apply,
    Matrix.transpose_apply, Pi.zero_apply]
  change (∑ z : {z // key z = key j}, c z.1 * (p z.1).coeff (rows i.1)) = 0
  have hv := congrArg (fun q : MvPolynomial τ K => q.coeff (rows i.1)) hc
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, smul_eq_mul,
    MvPolynomial.coeff_zero] at hv
  rw [← Finset.sum_subtype (Finset.univ.filter (fun z => key z = key j))
    (by simp) (fun z => c z * (p z).coeff (rows i.1))]
  refine Eq.trans ?_ hv
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro z hz hnot
  have hneq : key z ≠ key j := by simpa using hnot
  rw [hcross i.1 z (fun h => hneq (h.symm.trans i.2)), mul_zero]

end Froberg.ProductMinors
