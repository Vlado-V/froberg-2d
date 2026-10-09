module

public import Mathlib.Algebra.Polynomial.OfFn
public import Mathlib.Algebra.MvPolynomial.Nilpotent
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Tactic

@[expose] public section

/-!
# Primitive vectors and proportionality over a fraction field

Primitive means that every common divisor of the coordinates is a unit.
This does not assert that the coordinates generate the unit ideal; those
notions differ over multivariate polynomial rings.
-/

namespace Froberg

open Polynomial Matrix

variable {R K : Type*} [CommRing R] [IsDomain R] [IsGCDMonoid R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- Proportional primitive polynomials over a gcd domain differ by a unit of
the original domain, even when their proportionality factor is initially
given only in its fraction field. -/
theorem primitive_polynomial_fraction_scalar
    (P Q : Polynomial R) (hP : P.IsPrimitive) (hQ : Q.IsPrimitive)
    (c : K) (hrel : Q.map (algebraMap R K) = C c * P.map (algebraMap R K)) :
    ∃ a : R, IsUnit a ∧ algebraMap R K a = c ∧ Q = C a * P := by
  have hclift : C c ∈ Polynomial.lifts (algebraMap R K) :=
    hP.mul_map_mem_lifts_iff.mp ⟨Q, hrel⟩
  obtain ⟨T, hT⟩ := hclift
  change T.map (algebraMap R K) = C c at hT
  let a : R := T.coeff 0
  have hac : algebraMap R K a = c := by
    have hc := congrArg (fun S : Polynomial K => S.coeff 0) hT
    simpa only [Polynomial.coeff_map, Polynomial.coeff_C_zero] using hc
  have heq : Q = C a * P := by
    apply Polynomial.map_injective (algebraMap R K) (IsFractionRing.injective R K)
    simpa only [Polynomial.map_mul, Polynomial.map_C, hac] using hrel
  exact ⟨a, hQ a ⟨P, heq⟩, hac, heq⟩

/-- A coordinate tuple has no common nonunit divisor. -/
def IsPrimitiveVector {ι : Type*} (v : ι → R) : Prop :=
  ∀ a : R, (∀ i, a ∣ v i) → IsUnit a

omit [IsDomain R] [IsGCDMonoid R] in
/-- Primitivity is unchanged by a bijective relabeling of coordinates. -/
theorem IsPrimitiveVector.reindex {ι κ : Type*} {v : ι → R}
    (hv : IsPrimitiveVector v) (e : κ ≃ ι) : IsPrimitiveVector (fun i => v (e i)) := by
  intro a ha
  apply hv a
  intro i
  simpa only [e.apply_symm_apply] using ha (e.symm i)

variable [DecidableEq R]

omit [IsDomain R] [IsGCDMonoid R] in
/-- Encoding a primitive vector as polynomial coefficients preserves
primitivity. -/
theorem IsPrimitiveVector.ofFn {n : ℕ} {v : Fin n → R}
    (hv : IsPrimitiveVector v) : (Polynomial.ofFn n v).IsPrimitive := by
  intro a ha
  apply hv a
  intro i
  have hc := (Polynomial.C_dvd_iff_dvd_coeff a (Polynomial.ofFn n v)).mp ha i.val
  simpa only [Polynomial.ofFn_coeff_eq_val_of_lt v i.isLt] using hc

omit [IsDomain R] [IsGCDMonoid R] in
/-- The coefficient encoding has exactly the same common divisors. -/
theorem isPrimitiveVector_iff_ofFn {n : ℕ} (v : Fin n → R) :
    IsPrimitiveVector v ↔ (Polynomial.ofFn n v).IsPrimitive := by
  refine ⟨IsPrimitiveVector.ofFn, ?_⟩
  intro hv a ha
  apply hv a
  apply (Polynomial.C_dvd_iff_dvd_coeff a (Polynomial.ofFn n v)).mpr
  intro j
  by_cases hj : j < n
  · simpa only [Polynomial.ofFn_coeff_eq_val_of_lt v hj] using ha ⟨j, hj⟩
  · simp only [Polynomial.ofFn_coeff_eq_zero_of_ge v (Nat.le_of_not_gt hj), dvd_zero]

omit [IsDomain R] in
/-- Every nonzero tuple over a gcd domain has a primitive part, obtained by
dividing its coordinates by their common content. -/
theorem exists_primitive_vector_factor {n : ℕ} (v : Fin n → R) (hv : v ≠ 0) :
    ∃ a : R, a ≠ 0 ∧ ∃ w : Fin n → R,
      IsPrimitiveVector w ∧ ∀ i, v i = a * w i := by
  classical
  let : NormalizedGCDMonoid R := Classical.choice inferInstance
  let P : Polynomial R := Polynomial.ofFn n v
  have hP : P ≠ 0 := by
    intro hP
    apply hv
    apply Polynomial.injective_ofFn n
    simpa only [map_zero] using hP
  have hn : 1 ≤ n := by
    by_contra hn
    have hn0 : n = 0 := by omega
    subst n
    apply hv
    ext i
    exact Fin.elim0 i
  let w := Polynomial.toFn n P.primPart
  have hdeg : P.primPart.natDegree < n := by
    rw [Polynomial.natDegree_primPart]
    exact Polynomial.ofFn_natDegree_lt hn v
  have hw : Polynomial.ofFn n w = P.primPart :=
    Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt hdeg
  refine ⟨P.content, ?_, w, ?_, ?_⟩
  · exact fun h => hP (Polynomial.content_eq_zero_iff.mp h)
  · apply (isPrimitiveVector_iff_ofFn w).mpr
    rw [hw]
    exact P.isPrimitive_primPart
  · intro i
    have hi := congrArg (fun S : Polynomial R => S.coeff i.val)
      P.eq_C_content_mul_primPart
    simpa [P, w, Polynomial.toFn] using hi

/-- Every nonzero finite-dimensional fraction-field vector is a nonzero
fraction-field scalar times a primitive vector over the original gcd domain.
This is the normalization needed for a generic Plücker line. -/
theorem exists_primitive_fraction_vector {n : ℕ} (v : Fin n → K) (hv : v ≠ 0) :
    ∃ c : K, c ≠ 0 ∧ ∃ w : Fin n → R,
      IsPrimitiveVector w ∧ ∀ i, v i = c * algebraMap R K (w i) := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors R) v
  choose u hu using hb
  have hb0 : algebraMap R K (b : R) ≠ 0 := by
    exact (map_ne_zero_iff (algebraMap R K) (IsFractionRing.injective R K)).mpr
      (nonZeroDivisors.ne_zero b.property)
  have hu0 : u ≠ 0 := by
    intro huz
    apply hv
    funext i
    have hi := hu i
    rw [huz] at hi
    simp only [Pi.zero_apply, map_zero, Algebra.smul_def] at hi
    exact (mul_eq_zero.mp hi.symm).resolve_left hb0
  obtain ⟨a, ha0, w, hw, huw⟩ := exists_primitive_vector_factor u hu0
  have haK : algebraMap R K a ≠ 0 :=
    (map_ne_zero_iff (algebraMap R K) (IsFractionRing.injective R K)).mpr ha0
  refine ⟨algebraMap R K a / algebraMap R K (b : R), div_ne_zero haK hb0,
    w, hw, ?_⟩
  intro i
  have hi : algebraMap R K a * algebraMap R K (w i) =
      algebraMap R K (b : R) * v i := by
    rw [← map_mul, ← huw]
    simpa only [Algebra.smul_def] using hu i
  calc
    v i = (algebraMap R K (b : R))⁻¹ * (algebraMap R K (b : R) * v i) := by
      rw [← mul_assoc, inv_mul_cancel₀ hb0, one_mul]
    _ = (algebraMap R K (b : R))⁻¹ *
        (algebraMap R K a * algebraMap R K (w i)) := by rw [← hi]
    _ = (algebraMap R K a / algebraMap R K (b : R)) * algebraMap R K (w i) := by ring

/-- Primitive vectors proportional over a fraction field differ by a unit
scalar from the original gcd domain.  In particular this applies to a UFD
of polynomial coefficients in a primitive Plücker-vector construction. -/
theorem primitive_vector_fraction_scalar
    {n : ℕ} (v w : Fin n → R)
    (hv : IsPrimitiveVector v) (hw : IsPrimitiveVector w)
    (c : K) (hrel : ∀ i, algebraMap R K (w i) = c * algebraMap R K (v i)) :
    ∃ a : R, IsUnit a ∧ algebraMap R K a = c ∧ ∀ i, w i = a * v i := by
  have hp : (Polynomial.ofFn n w).map (algebraMap R K) =
      C c * (Polynomial.ofFn n v).map (algebraMap R K) := by
    ext j
    by_cases hj : j < n
    · simpa only [Polynomial.coeff_map, Polynomial.coeff_C_mul,
        Polynomial.ofFn_coeff_eq_val_of_lt v hj,
        Polynomial.ofFn_coeff_eq_val_of_lt w hj] using hrel ⟨j, hj⟩
    · simp only [Polynomial.coeff_map, Polynomial.coeff_C_mul,
        Polynomial.ofFn_coeff_eq_zero_of_ge v (Nat.le_of_not_gt hj),
        Polynomial.ofFn_coeff_eq_zero_of_ge w (Nat.le_of_not_gt hj),
        map_zero, mul_zero]
  obtain ⟨a, ha, hac, heq⟩ := primitive_polynomial_fraction_scalar
    (Polynomial.ofFn n v) (Polynomial.ofFn n w) hv.ofFn hw.ofFn c hp
  refine ⟨a, ha, hac, ?_⟩
  intro i
  have hi := congrArg (fun S : Polynomial R => S.coeff i.val) heq
  simpa only [Polynomial.coeff_C_mul,
    Polynomial.ofFn_coeff_eq_val_of_lt v i.isLt,
    Polynomial.ofFn_coeff_eq_val_of_lt w i.isLt] using hi

/-- The proportionality theorem for any finite coordinate type. -/
theorem primitive_family_fraction_scalar
    {ι : Type*} [Fintype ι] (v w : ι → R)
    (hv : IsPrimitiveVector v) (hw : IsPrimitiveVector w)
    (c : K) (hrel : ∀ i, algebraMap R K (w i) = c * algebraMap R K (v i)) :
    ∃ a : R, IsUnit a ∧ algebraMap R K a = c ∧ ∀ i, w i = a * v i := by
  classical
  let e := Fintype.equivFin ι
  obtain ⟨a, ha, hac, heq⟩ := primitive_vector_fraction_scalar
    (fun i => v (e.symm i)) (fun i => w (e.symm i))
    (hv.reindex e.symm) (hw.reindex e.symm) c (fun i => hrel (e.symm i))
  refine ⟨a, ha, hac, ?_⟩
  intro i
  simpa only [e.symm_apply_apply] using heq (e i)

/-- A primitive representative exists for any nonzero finite family over
the fraction field, independently of the coordinate indexing. -/
theorem exists_primitive_fraction_family
    {ι : Type*} [Fintype ι] (v : ι → K) (hv : v ≠ 0) :
    ∃ c : K, c ≠ 0 ∧ ∃ w : ι → R,
      IsPrimitiveVector w ∧ ∀ i, v i = c * algebraMap R K (w i) := by
  classical
  let e := Fintype.equivFin ι
  have hv' : (fun i => v (e.symm i)) ≠ 0 := by
    intro h
    apply hv
    funext i
    simpa only [e.symm_apply_apply, Pi.zero_apply] using congrFun h (e i)
  obtain ⟨c, hc, w, hw, heq⟩ := exists_primitive_fraction_vector
    (R := R) (fun i => v (e.symm i)) hv'
  refine ⟨c, hc, (fun i => w (e i)), hw.reindex e, ?_⟩
  intro i
  simpa only [e.symm_apply_apply] using heq (e i)

omit [IsDomain R] [IsGCDMonoid R] [DecidableEq R] in
/-- Invertible changes of coordinates preserve primitive tuples. -/
theorem IsPrimitiveVector.mulVec {ι : Type*} [Fintype ι] [DecidableEq ι] {v : ι → R}
    (hv : IsPrimitiveVector v) (A B : Matrix ι ι R)
    (hBA : B * A = 1) : IsPrimitiveVector (A *ᵥ v) := by
  intro a ha
  apply hv a
  intro i
  have hi : v i = (B *ᵥ (A *ᵥ v)) i := by
    rw [Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec]
  rw [hi]
  change a ∣ ∑ j, B i j * (A *ᵥ v) j
  apply Finset.dvd_sum
  intro j _
  exact dvd_mul_of_dvd_right (ha j) (B i j)

omit [IsDomain R] [IsGCDMonoid R] [DecidableEq R] in
/-- Automorphisms of the coefficient domain preserve primitive tuples. -/
theorem IsPrimitiveVector.map {ι : Type*} {v : ι → R}
    (hv : IsPrimitiveVector v) (e : R ≃+* R) :
    IsPrimitiveVector (fun i => e (v i)) := by
  intro a ha
  have hu : IsUnit (e.symm a) := by
    apply hv
    intro i
    obtain ⟨b, hb⟩ := ha i
    refine ⟨e.symm b, ?_⟩
    have heq := congrArg e.symm hb
    simpa only [map_mul, e.symm_apply_apply] using heq
  simpa using hu.map (e : R →+* R)

/-- For a polynomial coefficient domain over a field, a fraction-field
proportionality between primitive tuples is already a nonzero constant from
the ground field. -/
theorem primitive_polynomial_vectors_constant_scalar
    {k F σ : Type*} [Field k] [Field F]
    [Algebra (MvPolynomial σ k) F] [IsFractionRing (MvPolynomial σ k) F]
    {ι : Type*} [Fintype ι] (v w : ι → MvPolynomial σ k)
    (hv : IsPrimitiveVector v) (hw : IsPrimitiveVector w)
    (c : F) (hrel : ∀ i,
      algebraMap (MvPolynomial σ k) F (w i) =
        c * algebraMap (MvPolynomial σ k) F (v i)) :
    ∃ a : k, a ≠ 0 ∧ algebraMap (MvPolynomial σ k) F (MvPolynomial.C a) = c ∧
      ∀ i, w i = MvPolynomial.C a * v i := by
  classical
  obtain ⟨a, ha, hac, hwv⟩ := primitive_family_fraction_scalar v w hv hw c hrel
  obtain ⟨a₀, ha₀, haa₀⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp ha
  subst a
  exact ⟨a₀, ha₀.ne_zero, hac, hwv⟩

end Froberg
