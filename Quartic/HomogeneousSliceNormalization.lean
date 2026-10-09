module

public import Quartic.SliceFiniteModule

@[expose] public section

/-! Homogeneous scaling and complete coverage by normalized linear-slice charts. -/
noncomputable section
namespace Quartic.HomogeneousSliceNormalization
open MvPolynomial
variable {K L : Type*} [Field K] [Field L] [Algebra K L] {n r s d : ℕ}

/-- The actual homogeneous evaluation formula over any extension field. -/
theorem aeval_smul (p : Forms K n d) (c : L) (x : Fin n → L) :
    aeval (c • x) p.val = c^d * aeval x p.val := by
  classical
  rw [← p.val.support_sum_monomial_coeff,map_sum,map_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  have hedeg : e.degree = d := by
    simpa only [Finsupp.degree_eq_weight_one,Pi.one_def] using
      p.property (mem_support_iff.mp he)
  simp only [aeval_monomial,Pi.smul_apply,smul_eq_mul,mul_pow,Finsupp.prod,
    Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]
  change _ = c^d * _
  rw [← Finsupp.degree_apply,hedeg]
  ring

/-- Base-field form of the same actual evaluation identity. -/
theorem eval_smul (p : Forms K n d) (c : K) (x : Fin n → K) :
    eval (c • x) p.val = c^d * eval x p.val :=
  aeval_smul p c x

/-- Nonzero scalar normalization preserves homogeneous zero equations in both directions. -/
theorem aeval_smul_eq_zero_iff (p : Forms K n d) (c : L) (hc : c ≠ 0)
    (x : Fin n → L) : aeval (c • x) p.val = 0 ↔ aeval x p.val = 0 := by
  rw [aeval_smul,mul_eq_zero]
  simp only [pow_ne_zero _ hc,false_or]

/-- Normalize by the value of a chosen linear slice. -/
def normalize (ℓ : Forms K n 1) (x : Fin n → L) : Fin n → L :=
  (aeval x ℓ.val)⁻¹ • x

@[simp] theorem normalize_slice (ℓ : Forms K n 1) (x : Fin n → L)
    (hℓ : aeval x ℓ.val ≠ 0) : aeval (normalize ℓ x) ℓ.val = 1 := by
  rw [normalize,aeval_smul,pow_one,inv_mul_cancel₀ hℓ]

/-- Every homogeneous equation is preserved when a nonzero slice is normalized. -/
theorem normalize_zero_iff (ℓ : Forms K n 1) (x : Fin n → L)
    (hℓ : aeval x ℓ.val ≠ 0) (p : Forms K n d) :
    aeval (normalize ℓ x) p.val = 0 ↔ aeval x p.val = 0 :=
  aeval_smul_eq_zero_iff p _ (inv_ne_zero hℓ) x

/-- The original point is recovered by multiplying the normalized point by its slice value. -/
theorem reconstruct (ℓ : Forms K n 1) (x : Fin n → L)
    (hℓ : aeval x ℓ.val ≠ 0) : (aeval x ℓ.val) • normalize ℓ x = x := by
  simp only [normalize,smul_smul,mul_inv_cancel₀ hℓ,one_smul]

/-- A normalized representative of a nonzero point remains nonzero. -/
theorem normalize_ne_zero (ℓ : Forms K n 1) (x : Fin n → L)
    (hx : x ≠ 0) (hℓ : aeval x ℓ.val ≠ 0) : normalize ℓ x ≠ 0 := by
  intro h
  apply hx
  rw [← reconstruct ℓ x hℓ,h,smul_zero]

/-- Move the selected slice to the first coordinate by an actual permutation. -/
def moveSlice (ℓ : Fin (s+1) → Forms K n 1) (i : Fin (s+1)) :
    Fin (s+1) → Forms K n 1 := fun j => ℓ (Equiv.swap 0 i j)

@[simp] theorem moveSlice_zero (ℓ : Fin (s+1) → Forms K n 1) (i : Fin (s+1)) :
    moveSlice ℓ i 0 = ℓ i := by simp [moveSlice]

/-- Reindexing neither loses nor adds a common slice-zero condition. -/
theorem moveSlice_zero_iff (ℓ : Fin (s+1) → Forms K n 1) (i : Fin (s+1))
    (x : Fin n → L) :
    (∀ j, aeval x (moveSlice ℓ i j).val = 0) ↔ ∀ j, aeval x (ℓ j).val = 0 := by
  constructor
  · intro h j
    simpa only [moveSlice,Equiv.swap_apply_self] using h (Equiv.swap 0 i j)
  · intro h j
    exact h (Equiv.swap 0 i j)

/-- The geometric empty sliced locus is unchanged by the chosen permutation. -/
theorem geometric_empty_moveSlice (degree : Fin r → ℕ)
    (f : ∀ j, Forms K n (degree j)) (ℓ : Fin (s+1) → Forms K n 1)
    (hempty : ∀ x : Fin n → L, (∀ j, aeval x (f j).val = 0) →
      (∀ j, aeval x (ℓ j).val = 0) → x = 0) (i : Fin (s+1)) :
    ∀ x : Fin n → L, (∀ j, aeval x (f j).val = 0) →
      (∀ j, aeval x (moveSlice ℓ i j).val = 0) → x = 0 := by
  intro x hf hℓ
  exact hempty x hf ((moveSlice_zero_iff ℓ i x).mp hℓ)

/-- Every nonzero point on the homogeneous equation locus lies in one of the
finitely many dehomogenized charts, after scaling and the explicit permutation. -/
theorem exists_normalized_chart (degree : Fin r → ℕ)
    (f : ∀ j, Forms K n (degree j)) (ℓ : Fin (s+1) → Forms K n 1)
    (hempty : ∀ x : Fin n → L, (∀ j, aeval x (f j).val = 0) →
      (∀ j, aeval x (ℓ j).val = 0) → x = 0)
    (x : Fin n → L) (hx : x ≠ 0) (hf : ∀ j, aeval x (f j).val = 0) :
    ∃ i : Fin (s+1), aeval x (ℓ i).val ≠ 0 ∧
      (∀ j, aeval (normalize (ℓ i) x) (f j).val = 0) ∧
      aeval (normalize (ℓ i) x) (moveSlice ℓ i 0).val = 1 ∧
      (aeval x (ℓ i).val) • normalize (ℓ i) x = x := by
  classical
  obtain ⟨i,hi⟩ : ∃ i, aeval x (ℓ i).val ≠ 0 := by
    by_contra! h
    exact hx (hempty x hf h)
  refine ⟨i,hi,fun j => (normalize_zero_iff (ℓ i) x hi (f j)).mpr (hf j),?_,
    reconstruct (ℓ i) x hi⟩
  simpa only [moveSlice_zero] using normalize_slice (ℓ i) x hi

/-- Emptiness over one algebraically closed extension descends through the
homogeneous certificate and holds over every extension, including the base field. -/
theorem geometric_empty_all_extensions [IsAlgClosed L]
    {M : Type*} [Field M] [Algebra K M] (degree : Fin r → ℕ)
    (f : ∀ j, Forms K n (degree j)) (ℓ : Fin (s+1) → Forms K n 1)
    (hempty : ∀ x : Fin n → L, (∀ j, aeval x (f j).val = 0) →
      (∀ j, aeval x (ℓ j).val = 0) → x = 0) :
    ∀ x : Fin n → M, (∀ j, aeval x (f j).val = 0) →
      (∀ j, aeval x (ℓ j).val = 0) → x = 0 := by
  open SliceFiniteModule in
  have hempty' : ∀ x : Fin n → L,
      (∀ i, aeval x (slicedForms degree f ℓ i).val = 0) → x = 0 := by
    intro x hx
    apply hempty x
    · intro i
      simpa only [slicedForms,Fin.addCases_left] using hx (Fin.castAdd (s+1) i)
    · intro i
      simpa only [slicedForms,Fin.addCases_right] using hx (Fin.natAdd r i)
  obtain ⟨N,hN,hcert⟩ := HomogeneousMultiplicationCertificate.exists_surjective_degree
    (SliceFiniteModule.slicedDegrees degree) (SliceFiniteModule.slicedForms degree f ℓ) hempty'
  intro x hf hℓ
  apply HomogeneousMultiplicationCertificate.zero_of_surjective
    (SliceFiniteModule.slicedDegrees degree) (SliceFiniteModule.slicedForms degree f ℓ)
    N hN hcert x
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simpa only [SliceFiniteModule.slicedForms,Fin.addCases_left] using hf j
  · intro j
    simpa only [SliceFiniteModule.slicedForms,Fin.addCases_right] using hℓ j

/-- The finite normalized-chart cover applies to base-field covectors even when
its geometric emptiness was originally known only over an algebraic closure. -/
theorem exists_normalized_chart_of_geometric_empty [IsAlgClosed L]
    {M : Type*} [Field M] [Algebra K M] (degree : Fin r → ℕ)
    (f : ∀ j, Forms K n (degree j)) (ℓ : Fin (s+1) → Forms K n 1)
    (hempty : ∀ x : Fin n → L, (∀ j, aeval x (f j).val = 0) →
      (∀ j, aeval x (ℓ j).val = 0) → x = 0)
    (x : Fin n → M) (hx : x ≠ 0) (hf : ∀ j, aeval x (f j).val = 0) :
    ∃ i : Fin (s+1), aeval x (ℓ i).val ≠ 0 ∧
      (∀ j, aeval (normalize (ℓ i) x) (f j).val = 0) ∧
      aeval (normalize (ℓ i) x) (moveSlice ℓ i 0).val = 1 ∧
      (aeval x (ℓ i).val) • normalize (ℓ i) x = x :=
  exists_normalized_chart degree f ℓ
    (geometric_empty_all_extensions degree f ℓ hempty) x hx hf

/-- Explicit base-field evaluation interface for the descended empty locus. -/
theorem base_empty [IsAlgClosed L] (degree : Fin r → ℕ)
    (f : ∀ j, Forms K n (degree j)) (ℓ : Fin (s+1) → Forms K n 1)
    (hempty : ∀ x : Fin n → L, (∀ j, aeval x (f j).val = 0) →
      (∀ j, aeval x (ℓ j).val = 0) → x = 0) :
    ∀ x : Fin n → K, (∀ j, eval x (f j).val = 0) →
      (∀ j, eval x (ℓ j).val = 0) → x = 0 :=
  geometric_empty_all_extensions degree f ℓ hempty

end Quartic.HomogeneousSliceNormalization
