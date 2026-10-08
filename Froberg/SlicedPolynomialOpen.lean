import Quartic.AmbientCovectorSpreading

/-! Empty sections persist for polynomially varying homogeneous equations
and polynomially varying linear cuts. -/
noncomputable section
namespace Froberg
open MvPolynomial Quartic SliceFiniteModule
variable {K I : Type*} [Field K] {n r s : ℕ}

theorem slicedForms_polynomial (d : Fin r → ℕ)
    (f : ∀ i,(I → K) → Forms K n (d i))
    (l : Fin s → (I → K) → Forms K n 1)
    (hf : ∀ i,IsPolynomialFamily (f i)) (hl : ∀ i,IsPolynomialFamily (l i)) :
    ∀ i,IsPolynomialFamily (fun p => slicedForms d (fun j => f j p) (fun j => l j p) i) := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro j
    let L : Forms K n (d j) →ₗ[K] Forms K n (slicedDegrees (s := s) d (Fin.castAdd s j)) :=
      Submodule.inclusion (by simp only [slicedDegrees,Fin.addCases_left]; exact le_rfl)
    convert (hf j).linear_comp L using 1
    funext p
    apply Subtype.ext
    simp only [slicedForms,Fin.addCases_left]
    rfl
  · intro j
    let L : Forms K n 1 →ₗ[K] Forms K n (slicedDegrees (s := s) d (Fin.natAdd r j)) :=
      Submodule.inclusion (by simp only [slicedDegrees,Fin.addCases_right]; exact le_rfl)
    convert (hl j).linear_comp L using 1
    funext p
    apply Subtype.ext
    simp only [slicedForms,Fin.addCases_right]
    rfl

theorem slicedForms_vanish_iff {L : Type*} [Field L] [Algebra K L]
    (d : Fin r → ℕ) (f : ∀ i,Forms K n (d i)) (l : Fin s → Forms K n 1) (x : Fin n → L) :
    (∀ i,aeval x (slicedForms d f l i).val=0) ↔
      (∀ i,aeval x (f i).val=0) ∧ (∀ i,aeval x (l i).val=0) := by
  constructor
  · intro h
    exact ⟨fun i => by simpa only [slicedForms,Fin.addCases_left] using h (Fin.castAdd s i),
      fun i => by simpa only [slicedForms,Fin.addCases_right] using h (Fin.natAdd r i)⟩
  · rintro ⟨hf,hl⟩ i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [slicedForms,Fin.addCases_left] using hf j
    · simpa only [slicedForms,Fin.addCases_right] using hl j

theorem principal_open_empty_slices {L : Type*} [Field L] [Algebra K L] [IsAlgClosed L]
    (d : Fin r → ℕ) (f : ∀ i,(I → K) → Forms K n (d i))
    (l : Fin s → (I → K) → Forms K n 1)
    (hf : ∀ i,IsPolynomialFamily (f i)) (hl : ∀ i,IsPolynomialFamily (l i))
    (p₀ : I → K)
    (hempty : ∀ x : Fin n → L,(∀ i,aeval x (f i p₀).val=0) →
      (∀ i,aeval x (l i p₀).val=0) → x=0) :
    ∃ P : MvPolynomial I K,eval p₀ P ≠ 0 ∧ ∀ p,eval p P ≠ 0 →
      ∀ x : Fin n → L,(∀ i,aeval x (f i p).val=0) →
        (∀ i,aeval x (l i p).val=0) → x=0 := by
  obtain ⟨P,hP,hgood⟩ := HomogeneousEmptyFiberOpen.principal_open_empty_fiber (L := L)
    (slicedDegrees (s := s) d) (fun i p => slicedForms d (fun j => f j p) (fun j => l j p) i)
    (slicedForms_polynomial d f l hf hl) p₀ (by
      intro x hx
      obtain ⟨hf,hl⟩ := (slicedForms_vanish_iff d _ _ x).mp hx
      exact hempty x hf hl)
  exact ⟨P,hP,fun p hp x hx hl => hgood p hp x ((slicedForms_vanish_iff d _ _ x).mpr ⟨hx,hl⟩)⟩

end Froberg
