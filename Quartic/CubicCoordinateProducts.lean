module

public import Quartic.CubicLinearCoordinates
public import Mathlib.RingTheory.Ideal.Quotient.Operations

@[expose] public section

/-!
# Cubic products of a coordinate subspace

Killing one set of variables gives a surjective map on actual cubic forms.
Its kernel is exactly the product of those linear variables with all quadrics.
-/

noncomputable section
namespace Quartic.CubicCoordinateProducts
open MvPolynomial Module CubicLinearCoordinates
variable {K σ ι τ : Type*} [Field K]

/-- The cubic products of an ambient subspace of linear polynomials. -/
def products (D : Submodule K (MvPolynomial σ K)) : Submodule K (H K σ 3) :=
  (D * H K σ 2).comap (H K σ 3).subtype

theorem component_three_mul_linear (f p : MvPolynomial σ K) (hf : f.IsHomogeneous 1) :
    homogeneousComponent 3 (f * p) = f * homogeneousComponent 2 p := by
  induction p using MvPolynomial.induction_on' with
  | monomial e a =>
      have he : (monomial e a : MvPolynomial σ K).IsHomogeneous e.degree :=
        isHomogeneous_monomial a rfl
      rw [homogeneousComponent_of_mem (hf.mul he), homogeneousComponent_of_mem he]
      by_cases h : e.degree = 2
      · simp [h]
      · have h3 : ¬3 = 1 + e.degree := by omega
        simp [Ne.symm h, h3]
  | add p q hp hq => simp only [mul_add, map_add, hp, hq]

theorem cubic_mem_ideal_iff (D : Submodule K (MvPolynomial σ K)) (hD : D ≤ H K σ 1)
    (p : H K σ 3) : p.val ∈ Ideal.span (D : Set (MvPolynomial σ K)) ↔
      p ∈ products D := by
  constructor
  · intro hp
    have hall : ∀ a : MvPolynomial σ K,
        homogeneousComponent 3 (a * p.val) ∈ D * H K σ 2 := by
      generalize hval : p.val = f at hp ⊢
      clear hval
      induction hp using Submodule.span_induction with
      | mem f hf =>
          intro a
          rw [mul_comm a f, component_three_mul_linear f a (hD hf)]
          exact Submodule.mul_mem_mul hf (homogeneousComponent_mem 2 a)
      | zero => intro a; simp
      | add f g hf hg ihf ihg =>
          intro a
          rw [mul_add, map_add]
          exact (D * H K σ 2).add_mem (ihf a) (ihg a)
      | smul b f hf ih =>
          intro a
          change homogeneousComponent 3 (a * (b * f)) ∈ D * H K σ 2
          rw [← mul_assoc]
          exact ih (a * b)
    have hz := hall 1
    change p.val ∈ D * H K σ 2
    simpa only [one_mul, homogeneousComponent_eq_self p.property] using hz
  · intro hp
    change p.val ∈ D * H K σ 2 at hp
    refine Submodule.mul_induction_on hp ?_ ?_
    · intro f hf a ha
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span hf)
    · intro f g hf hg
      exact Ideal.add_mem _ hf hg

/-- The span of the variables to be killed. -/
def leftSpace (K ι τ : Type*) [Field K] : Submodule K (MvPolynomial (ι ⊕ τ) K) :=
  Submodule.span K (Set.range (fun i : ι => (X (Sum.inl i) : MvPolynomial (ι ⊕ τ) K)))

theorem leftSpace_homogeneous : leftSpace K ι τ ≤ H K (ι ⊕ τ) 1 := by
  apply Submodule.span_le.mpr
  rintro p ⟨i, rfl⟩
  exact isHomogeneous_X K (Sum.inl i)

/-- Set all left variables to zero, retaining each right variable. -/
def dropLeft : MvPolynomial (ι ⊕ τ) K →ₐ[K] MvPolynomial τ K :=
  aeval (Sum.elim (fun _ => 0) X)

@[simp] theorem dropLeft_X_left (i : ι) : dropLeft (K := K) (τ := τ) (X (Sum.inl i)) = 0 := by
  simp [dropLeft]

@[simp] theorem dropLeft_X_right (i : τ) : dropLeft (K := K) (ι := ι) (X (Sum.inr i)) = X i := by
  simp [dropLeft]

@[simp] theorem dropLeft_rename (p : MvPolynomial τ K) :
    dropLeft (ι := ι) (rename Sum.inr p) = p := by
  have he : (dropLeft (K := K) (ι := ι) (τ := τ)).comp (rename Sum.inr) = AlgHom.id K _ := by
    ext i
    simp
  exact AlgHom.congr_fun he p

theorem dropLeft_eq_zero_of_mem {p : MvPolynomial (ι ⊕ τ) K}
    (hp : p ∈ leftSpace K ι τ) : dropLeft p = 0 := by
  have he : leftSpace K ι τ ≤ LinearMap.ker (dropLeft (K := K)).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro p ⟨i, rfl⟩
    simp
  exact he hp

private theorem sub_section_mem_ideal (p : MvPolynomial (ι ⊕ τ) K) :
    p - rename Sum.inr (dropLeft p) ∈ Ideal.span (leftSpace K ι τ : Set _) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [dropLeft]
  | add p q hp hq =>
      convert (Ideal.span (leftSpace K ι τ : Set _)).add_mem hp hq using 1
      simp only [map_add]
      ring
  | mul_X p i hp =>
      cases i with
      | inl i =>
          simpa using Ideal.mul_mem_left (Ideal.span (leftSpace K ι τ : Set _)) p
            (Ideal.subset_span (Submodule.subset_span (Set.mem_range_self i)))
      | inr i =>
          convert Ideal.mul_mem_right (X (Sum.inr i)) _ hp using 1
          simp only [map_mul, dropLeft_X_right, rename_X]
          ring

theorem dropLeft_zero_iff_ideal (p : MvPolynomial (ι ⊕ τ) K) :
    dropLeft p = 0 ↔ p ∈ Ideal.span (leftSpace K ι τ : Set _) := by
  constructor
  · intro h
    simpa only [h, map_zero, sub_zero] using sub_section_mem_ideal p
  · intro hp
    have hI : Ideal.span (leftSpace K ι τ : Set (MvPolynomial (ι ⊕ τ) K)) ≤
        RingHom.ker (dropLeft (K := K) (ι := ι) (τ := τ)).toRingHom := by
      apply Ideal.span_le.mpr
      intro f hf
      exact dropLeft_eq_zero_of_mem hf
    exact hI hp

theorem dropLeft_homogeneous {d : ℕ} (p : MvPolynomial (ι ⊕ τ) K) (hp : p.IsHomogeneous d) :
    (dropLeft p).IsHomogeneous d := by
  have hg : ∀ i : ι ⊕ τ,
      ((Sum.elim (fun _ : ι => 0) X i) : MvPolynomial τ K).IsHomogeneous 1 := by
    intro i
    cases i with
    | inl i => exact (H K τ 1).zero_mem
    | inr i => exact isHomogeneous_X K i
  simpa [dropLeft] using hp.aeval _ hg

/-- The coordinate projection on the actual cubic component. -/
def dropCubic : H K (ι ⊕ τ) 3 →ₗ[K] H K τ 3 :=
  ((dropLeft (K := K)).toLinearMap.comp (H K (ι ⊕ τ) 3).subtype).codRestrict _
    (fun p => dropLeft_homogeneous p.val p.property)

theorem dropCubic_surjective : Function.Surjective (dropCubic (K := K) (ι := ι) (τ := τ)) := by
  intro p
  refine ⟨⟨rename Sum.inr p.val, p.property.rename_isHomogeneous⟩, ?_⟩
  apply Subtype.ext
  exact dropLeft_rename p.val

theorem ker_dropCubic : LinearMap.ker (dropCubic (K := K) (ι := ι) (τ := τ)) =
    products (leftSpace K ι τ) := by
  ext p
  change dropCubic p = 0 ↔ p ∈ products (leftSpace K ι τ)
  rw [← Subtype.val_inj]
  change dropLeft p.val = 0 ↔ p ∈ products (leftSpace K ι τ)
  rw [dropLeft_zero_iff_ideal, cubic_mem_ideal_iff _ leftSpace_homogeneous]

/-- Exact dimension of the coordinate cubic product space. -/
theorem finrank_coordinate_products [Fintype ι] [Fintype τ] :
    finrank K (products (leftSpace K ι τ)) =
      (Fintype.card ι + Fintype.card τ + 2).choose 3 - (Fintype.card τ + 2).choose 3 := by
  have h := (dropCubic (K := K) (ι := ι) (τ := τ)).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr dropCubic_surjective, finrank_top,
    ker_dropCubic, finrank_homogeneous, finrank_homogeneous] at h
  simp only [Fintype.card_sum] at h
  have h₁ : Fintype.card τ + 3 - 1 = Fintype.card τ + 2 := by omega
  have h₂ : Fintype.card ι + Fintype.card τ + 3 - 1 =
      Fintype.card ι + Fintype.card τ + 2 := by omega
  rw [h₁, h₂] at h
  omega

end Quartic.CubicCoordinateProducts
