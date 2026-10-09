module

public import Quartic.HomogeneousMultiplicationCertificate
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

@[expose] public section

/-! Finite module generation from an actual homogeneous slice certificate. -/
noncomputable section
namespace Quartic.SliceFiniteModule
open Module MvPolynomial
variable {K A : Type*} [Field K] [CommRing A] [Algebra K A] {n s : ℕ}

/-- Images of monomials of total degree below the certificate degree. -/
def lowSpan (φ : Poly K n →ₐ[K] A) (S : Subalgebra K A) (N : ℕ) : Submodule S A :=
  Submodule.span S ((fun e : Fin n →₀ ℕ => φ (monomial e 1)) '' {e | e.degree < N})

lemma monomial_scalar (φ : Poly K n →ₐ[K] A) (S : Subalgebra K A)
    (e : Fin n →₀ ℕ) (c : K) :
    φ (monomial e c) = (algebraMap K S c) • φ (monomial e 1) := by
  change φ (monomial e c) = (algebraMap K A c) * φ (monomial e 1)
  rw [← φ.commutes, ← map_mul, MvPolynomial.algebraMap_eq, C_mul_monomial, mul_one]

/-- Degree-N reductions with linear slice coefficients lower total degree by one.
Consequently their low-degree monomials span every polynomial image. -/
theorem image_mem_lowSpan (φ : Poly K n →ₐ[K] A) (S : Subalgebra K A)
    (ℓ : Fin s → Forms K n 1) (N : ℕ) (hN : 0 < N)
    (hℓ : ∀ i, φ (ℓ i).val ∈ S)
    (hred : ∀ p : Forms K n N, ∃ u : Fin s → Forms K n (N-1),
      φ p.val = ∑ i, φ (ℓ i).val * φ (u i).val)
    (p : Poly K n) : φ p ∈ lowSpan φ S N := by
  classical
  have hm : ∀ D : ℕ, ∀ e : Fin n →₀ ℕ, e.degree = D →
      φ (monomial e 1) ∈ lowSpan φ S N := by
    intro D
    induction D using Nat.strong_induction_on with
    | h D ih =>
      intro e he
      by_cases helow : e.degree < N
      · exact Submodule.subset_span ⟨e,helow,rfl⟩
      · obtain ⟨f,hfe,hf⟩ := Finsupp.exists_le_degree_eq e N (Nat.le_of_not_gt helow)
        obtain ⟨u,hu⟩ := hred ⟨monomial f 1,isHomogeneous_monomial 1 hf⟩
        have heval : φ (monomial e 1) = φ (monomial (e-f) 1) * φ (monomial f 1) := by
          rw [← map_mul,monomial_mul_monomial,one_mul,tsub_add_cancel_of_le hfe]
        rw [heval,hu,Finset.mul_sum]
        apply Submodule.sum_mem
        intro i _
        have hprod : φ (monomial (e-f) 1 * (u i).val) ∈ lowSpan φ S N := by
          rw [← (u i).val.support_sum_monomial_coeff,Finset.mul_sum,map_sum]
          apply Submodule.sum_mem
          intro b hb
          rw [monomial_mul_monomial,one_mul,monomial_scalar φ S]
          apply Submodule.smul_mem
          apply ih (e-f+b).degree ?_ _ rfl
          have hbdeg : b.degree = N-1 := by
            simpa only [Finsupp.degree_eq_weight_one,Pi.one_def] using
              (u i).property (mem_support_iff.mp hb)
          have hdiff : (e-f).degree + f.degree = e.degree := by
            rw [← map_add,tsub_add_cancel_of_le hfe]
          rw [map_add]
          omega
        have hs := (lowSpan φ S N).smul_mem ⟨φ (ℓ i).val,hℓ i⟩ hprod
        change φ (ℓ i).val * φ (monomial (e-f) 1 * (u i).val) ∈ lowSpan φ S N at hs
        simpa only [map_mul,mul_assoc,mul_left_comm] using hs
  rw [← p.support_sum_monomial_coeff,map_sum]
  apply Submodule.sum_mem
  intro e _
  rw [monomial_scalar φ S]
  exact (lowSpan φ S N).smul_mem _ (hm e.degree e rfl)

/-- Surjectivity converts the explicit spanning theorem into module finiteness. -/
theorem finite_of_reductions (φ : Poly K n →ₐ[K] A) (hφ : Function.Surjective φ)
    (S : Subalgebra K A) (ℓ : Fin s → Forms K n 1) (N : ℕ) (hN : 0 < N)
    (hℓ : ∀ i, φ (ℓ i).val ∈ S)
    (hred : ∀ p : Forms K n N, ∃ u : Fin s → Forms K n (N-1),
      φ p.val = ∑ i, φ (ℓ i).val * φ (u i).val) : Module.Finite S A := by
  have htop : lowSpan φ S N = ⊤ := by
    apply top_unique
    intro a _
    obtain ⟨p,rfl⟩ := hφ a
    exact image_mem_lowSpan φ S ℓ N hN hℓ hred p
  exact ⟨Submodule.fg_def.mpr ⟨_,
    (Finsupp.finite_of_degree_lt N).image (fun e : Fin n →₀ ℕ => φ (monomial e 1)),htop⟩⟩

variable {r : ℕ}

/-- Degrees of the original equations followed by the linear slices. -/
def slicedDegrees (d : Fin r → ℕ) : Fin (r+s) → ℕ := Fin.addCases d (fun _ => 1)

/-- The actual homogeneous equations together with their slicing linear forms. -/
def slicedForms (d : Fin r → ℕ) (f : ∀ i, Forms K n (d i))
    (ℓ : Fin s → Forms K n 1) : ∀ i, Forms K n (slicedDegrees (s := s) d i) :=
  fun i => ⟨Fin.addCases (fun j => (f j).val) (fun j => (ℓ j).val) i, by
    refine Fin.addCases ?_ ?_ i
    · intro j; simp [slicedDegrees]
    · intro j; simp [slicedDegrees]⟩

/-- The multiplication certificate yields the precise lower-degree slice reductions
in every algebra where the original equations vanish. -/
theorem reductions_of_certificate (φ : Poly K n →ₐ[K] A)
    (d : Fin r → ℕ) (f : ∀ i, Forms K n (d i)) (ℓ : Fin s → Forms K n 1)
    (hf : ∀ i, φ (f i).val = 0) (N : ℕ) (hN : 0 < N)
    (hcert : Function.Surjective (HomogeneousMultiplicationCertificate.multiplication
      (slicedDegrees d) (slicedForms d f ℓ) N)) :
    ∀ p : Forms K n N, ∃ u : Fin s → Forms K n (N-1),
      φ p.val = ∑ i, φ (ℓ i).val * φ (u i).val := by
  intro p
  obtain ⟨u,hu⟩ := hcert p
  refine ⟨fun i => ⟨(u (Fin.natAdd r i)).val, by
    simpa [slicedDegrees] using (u (Fin.natAdd r i)).property⟩, ?_⟩
  rw [← hu,HomogeneousMultiplicationCertificate.multiplication_val,map_sum,Fin.sum_univ_add]
  have hleft : (∑ i : Fin r, φ (if d i ≤ N then
      (u (Fin.castAdd s i)).val * (f i).val else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    split_ifs <;> simp [map_mul,hf]
  simp only [slicedDegrees,slicedForms,Fin.addCases_left,Fin.addCases_right]
  rw [hleft,zero_add]
  apply Finset.sum_congr rfl
  intro i _
  simp only [show 1 ≤ N by omega,↓reduceIte,map_mul,mul_comm]

/-- Actual finite module generation, derived from the homogeneous multiplication
certificate rather than supplied as an additional hypothesis. -/
theorem finite_of_certificate (φ : Poly K n →ₐ[K] A) (hφ : Function.Surjective φ)
    (S : Subalgebra K A) (d : Fin r → ℕ) (f : ∀ i, Forms K n (d i))
    (ℓ : Fin s → Forms K n 1) (hf : ∀ i, φ (f i).val = 0)
    (hℓ : ∀ i, φ (ℓ i).val ∈ S) (N : ℕ) (hN : 0 < N)
    (hcert : Function.Surjective (HomogeneousMultiplicationCertificate.multiplication
      (slicedDegrees d) (slicedForms d f ℓ) N)) : Module.Finite S A :=
  finite_of_reductions φ hφ S ℓ N hN hℓ
    (reductions_of_certificate φ d f ℓ hf N hN hcert)

/-- If one slice is already one, only the remaining s slices are needed as
coefficient algebra. Thus dehomogenization saves exactly one slice parameter. -/
theorem finite_over_remaining_slices (φ : Poly K n →ₐ[K] A)
    (hφ : Function.Surjective φ) (d : Fin r → ℕ) (f : ∀ i, Forms K n (d i))
    (ℓ : Fin (s+1) → Forms K n 1) (hf : ∀ i, φ (f i).val = 0)
    (hfirst : φ (ℓ 0).val = 1) (N : ℕ) (hN : 0 < N)
    (hcert : Function.Surjective (HomogeneousMultiplicationCertificate.multiplication
      (slicedDegrees d) (slicedForms d f ℓ) N)) :
    Module.Finite (Algebra.adjoin K (Set.range (fun i : Fin s => φ (ℓ i.succ).val))) A := by
  apply finite_of_certificate φ hφ _ d f ℓ hf ?_ N hN hcert
  intro i
  refine Fin.cases ?_ ?_ i
  · rw [hfirst]
    exact Subalgebra.one_mem _
  · intro j
    exact Algebra.subset_adjoin ⟨j,rfl⟩

/-- The homogeneous coordinate ring is finite over its actual linear-slice algebra. -/
theorem finite_quotient (I : Ideal (Poly K n)) (d : Fin r → ℕ)
    (f : ∀ i, Forms K n (d i)) (ℓ : Fin s → Forms K n 1)
    (hf : ∀ i, (f i).val ∈ I) (N : ℕ) (hN : 0 < N)
    (hcert : Function.Surjective (HomogeneousMultiplicationCertificate.multiplication
      (slicedDegrees d) (slicedForms d f ℓ) N)) :
    Module.Finite (Algebra.adjoin K (Set.range
      (fun i => Ideal.Quotient.mkₐ K I (ℓ i).val))) ((Poly K n) ⧸ I) := by
  apply finite_of_certificate (Ideal.Quotient.mkₐ K I)
    (Ideal.Quotient.mkₐ_surjective K I) _ d f ℓ ?_ ?_ N hN hcert
  · intro i
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hf i)
  · intro i
    exact Algebra.subset_adjoin ⟨i,rfl⟩

/-- Impose the affine chart equation that the first chosen linear slice equals one. -/
def dehomIdeal (I : Ideal (Poly K n)) (ℓ : Fin (s+1) → Forms K n 1) :
    Ideal (Poly K n) := I ⊔ Ideal.span {(ℓ 0).val-1}

/-- The dehomogenized algebra is finite over the algebra generated by the remaining
s linear slices, derived solely from the original homogeneous certificate. -/
theorem finite_dehom_quotient (I : Ideal (Poly K n)) (d : Fin r → ℕ)
    (f : ∀ i, Forms K n (d i)) (ℓ : Fin (s+1) → Forms K n 1)
    (hf : ∀ i, (f i).val ∈ I) (N : ℕ) (hN : 0 < N)
    (hcert : Function.Surjective (HomogeneousMultiplicationCertificate.multiplication
      (slicedDegrees d) (slicedForms d f ℓ) N)) :
    Module.Finite (Algebra.adjoin K (Set.range
      (fun i : Fin s => Ideal.Quotient.mkₐ K (dehomIdeal I ℓ) (ℓ i.succ).val)))
      ((Poly K n) ⧸ dehomIdeal I ℓ) := by
  apply finite_over_remaining_slices (Ideal.Quotient.mkₐ K (dehomIdeal I ℓ))
    (Ideal.Quotient.mkₐ_surjective K _) d f ℓ ?_ ?_ N hN hcert
  · intro i
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ((show I ≤ dehomIdeal I ℓ from le_sup_left) (hf i))
  · have hzero : Ideal.Quotient.mkₐ K (dehomIdeal I ℓ) ((ℓ 0).val-1) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr
        ((show Ideal.span {(ℓ 0).val-1} ≤ dehomIdeal I ℓ from le_sup_right)
          (Ideal.subset_span (Set.mem_singleton _)))
    simpa only [map_sub,map_one,sub_eq_zero] using hzero

/-- Geometric projective emptiness supplies the certificate, hence the same
finite-module conclusion with no assumed finite degree or finiteness premise. -/
theorem finite_dehom_of_geometric_empty {L : Type*} [Field L] [Algebra K L] [IsAlgClosed L]
    (I : Ideal (Poly K n)) (d : Fin r → ℕ) (f : ∀ i, Forms K n (d i))
    (ℓ : Fin (s+1) → Forms K n 1) (hf : ∀ i, (f i).val ∈ I)
    (hempty : ∀ x : Fin n → L, (∀ i, aeval x (f i).val = 0) →
      (∀ i, aeval x (ℓ i).val = 0) → x = 0) :
    Module.Finite (Algebra.adjoin K (Set.range
      (fun i : Fin s => Ideal.Quotient.mkₐ K (dehomIdeal I ℓ) (ℓ i.succ).val)))
      ((Poly K n) ⧸ dehomIdeal I ℓ) := by
  have hempty' : ∀ x : Fin n → L,
      (∀ i, aeval x (slicedForms d f ℓ i).val = 0) → x = 0 := by
    intro x hx
    apply hempty x
    · intro i
      simpa only [slicedForms,Fin.addCases_left] using hx (Fin.castAdd (s+1) i)
    · intro i
      simpa only [slicedForms,Fin.addCases_right] using hx (Fin.natAdd r i)
  obtain ⟨N,hN,hcert⟩ := HomogeneousMultiplicationCertificate.exists_surjective_degree
    (slicedDegrees d) (slicedForms d f ℓ) hempty'
  exact finite_dehom_quotient I d f ℓ hf N hN hcert

end Quartic.SliceFiniteModule
