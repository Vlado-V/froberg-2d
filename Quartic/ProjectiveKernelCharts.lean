import Quartic.KernelPolynomialCharts
import Mathlib.Algebra.MvPolynomial.Monad

/-!
# Projective charts for kernels of polynomial matrix families

For a nonzero kernel vector, one free coordinate in a nonsingular-minor chart
is nonzero. Normalizing that coordinate to one removes exactly one parameter.
These explicit rational charts are useful for covector incidence arguments.
-/
noncomputable section
namespace Quartic.ProjectiveKernelCharts
open Matrix MvPolynomial SubspaceCharts KernelPolynomialCharts
variable {K I : Type*} [Field K] {a n r : ℕ}

abbrev Other (v : Fin r ↪ Fin n) (z : Outside v) := {j : Outside v // j ≠ z}
abbrev Parameters (I : Type*) (v : Fin r ↪ Fin n) (z : Outside v) := I ⊕ Other v z

def normalizedVariables (v : Fin r ↪ Fin n) (z : Outside v) :
    ChartParameters (I := I) v → MvPolynomial (Parameters I v z) K := by
  classical
  exact Sum.elim (fun i => X (Sum.inl i))
    (fun j => if h : j = z then 1 else X (Sum.inr ⟨j, h⟩))

def extend (v : Fin r ↪ Fin n) (z : Outside v) (p : Parameters I v z → K) :
    ChartParameters (I := I) v → K := by
  classical
  exact Sum.elim (fun i => p (Sum.inl i))
    (fun j => if h : j = z then 1 else p (Sum.inr ⟨j, h⟩))

@[simp] theorem eval_normalizedVariables (v : Fin r ↪ Fin n) (z : Outside v)
    (p : Parameters I v z → K) (j : ChartParameters (I := I) v) :
    eval p (normalizedVariables v z j) = extend v z p j := by
  classical
  cases j with
  | inl i => simp [normalizedVariables, extend]
  | inr j => by_cases h : j = z <;> simp [normalizedVariables, extend, h]

 theorem eval_substitution (v : Fin r ↪ Fin n) (z : Outside v)
    (p : Parameters I v z → K) (f : MvPolynomial (ChartParameters (I := I) v) K) :
    eval p (bind₁ (normalizedVariables v z) f) = eval (extend v z p) f := by
  change eval₂Hom (RingHom.id K) p (bind₁ _ f) = _
  rw [eval₂Hom_bind₁]
  change eval₂Hom (RingHom.id K) (fun i => eval p (normalizedVariables v z i)) f = _
  simp only [eval_normalizedVariables]
  rfl

def numerator (A : Matrix (Fin a) (Fin n) (MvPolynomial I K))
    (u : Fin r ↪ Fin a) (v : Fin r ↪ Fin n) (z : Outside v) :
    Fin n → MvPolynomial (Parameters I v z) K :=
  fun k => bind₁ (normalizedVariables v z) (KernelPolynomialCharts.numerator A u v k)

def denominator (A : Matrix (Fin a) (Fin n) (MvPolynomial I K))
    (u : Fin r ↪ Fin a) (v : Fin r ↪ Fin n) (z : Outside v) :
    MvPolynomial (Parameters I v z) K :=
  bind₁ (normalizedVariables v z) (KernelPolynomialCharts.denominator A u v)

 theorem rationalMap_substitution (A : Matrix (Fin a) (Fin n) (MvPolynomial I K))
    (u : Fin r ↪ Fin a) (v : Fin r ↪ Fin n) (z : Outside v)
    (p : Parameters I v z → K) :
    RationalImageAvoidance.rationalMap (numerator A u v z) (denominator A u v z) p =
      RationalImageAvoidance.rationalMap (KernelPolynomialCharts.numerator A u v)
        (KernelPolynomialCharts.denominator A u v) (extend v z p) := by
  funext k
  simp only [RationalImageAvoidance.rationalMap, numerator, denominator, eval_substitution]

/-- Every nonzero kernel vector has a nonzero free coordinate. -/
theorem exists_nonzero_outside (A : Matrix (Fin a) (Fin n) K)
    (u : Fin r ↪ Fin a) (v : Fin r ↪ Fin n)
    (hdet : (KernelCharts.minor A u v).det ≠ 0)
    (x : Fin n → K) (hx : A *ᵥ x = 0) (hnz : x ≠ 0) :
    ∃ z : Outside v, x z.val ≠ 0 := by
  by_contra! h
  apply hnz
  have he : KernelCharts.outside v x = KernelCharts.outside v (0 : Fin n → K) := funext h
  have he' : (fun y : LinearMap.ker A.mulVecLin => KernelCharts.outside v y.val)
      ⟨x, hx⟩ = (fun y : LinearMap.ker A.mulVecLin => KernelCharts.outside v y.val)
      ⟨0, by simp⟩ := he
  exact congrArg Subtype.val (KernelCharts.outside_injective_on_kernel A u v hdet he')

/-- The exact parameter count is p+n-r-1, with p the original family size. -/
theorem parameter_count [Fintype I] (v : Fin r ↪ Fin n) (z : Outside v) :
    Fintype.card (Parameters I v z) = Fintype.card I + (n - r) - 1 := by
  classical
  have hpos : 0 < n - r := by
    rw [← card_outside v]
    exact Fintype.card_pos_iff.mpr ⟨z⟩
  have hc : Fintype.card (Other v z) = (n - r) - 1 := by
    rw [Fintype.card_subtype_compl, card_outside]
    simp only [Fintype.card_subtype_eq]
  rw [Fintype.card_sum, hc]
  omega

/-- Actual projective coverage, on the genuine nonzero denominator domain. -/
theorem cover_nonzero_kernel (A : Matrix (Fin a) (Fin n) (MvPolynomial I K))
    (u : Fin r ↪ Fin a) (v : Fin r ↪ Fin n) (t : I → K)
    (hdet : (KernelCharts.minor (evaluated A t) u v).det ≠ 0)
    (x : Fin n → K) (hx : evaluated A t *ᵥ x = 0) (hnz : x ≠ 0) :
    ∃ z : Outside v, ∃ p : Parameters I v z → K, ∃ s : K,
      s ≠ 0 ∧ (∀ i, p (Sum.inl i) = t i) ∧ eval p (denominator A u v z) ≠ 0 ∧
      x = s • RationalImageAvoidance.rationalMap (numerator A u v z) (denominator A u v z) p := by
  classical
  obtain ⟨z, hz⟩ := exists_nonzero_outside (evaluated A t) u v hdet x hx hnz
  let s := x z.val
  let x' : Fin n → K := s⁻¹ • x
  let p : Parameters I v z → K := Sum.elim t (fun j => x' j.val.val)
  have hx' : evaluated A t *ᵥ x' = 0 := by
    change (evaluated A t).mulVecLin (s⁻¹ • x) = 0
    rw [map_smul]
    change s⁻¹ • (evaluated A t *ᵥ x) = 0
    rw [hx, smul_zero]
  have hn : x' z.val = 1 := inv_mul_cancel₀ hz
  have hext : extend v z p = Sum.elim t (KernelCharts.outside v x') := by
    funext j
    cases j with
    | inl i => rfl
    | inr j =>
      by_cases hj : j = z
      · subst j
        simp [extend, KernelCharts.outside, hn]
      · simp [extend, hj, p, KernelCharts.outside]
  refine ⟨z, p, s, hz, fun _ => rfl, ?_, ?_⟩
  · rw [denominator, eval_substitution, hext, eval_denominator]
    exact hdet
  · rw [rationalMap_substitution, hext, rationalMap_eq_reconstruct A u v t _ hdet,
      KernelCharts.reconstruct_kernel _ u v hdet x' hx']
    change x = s • (s⁻¹ • x)
    rw [smul_smul, mul_inv_cancel₀ hz, one_smul]

end Quartic.ProjectiveKernelCharts
