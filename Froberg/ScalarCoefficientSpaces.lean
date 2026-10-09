module

public import Froberg.PairedScalarSeparation
public import Froberg.ScalarSeparation
public import Froberg.QuadraticQuotientSeparation

@[expose] public section

/-! Instantiate the scalar side of quadratic separation with an actual
paired-variable space and the checked generic deleted-bidegree theorem. -/
noncomputable section
namespace Froberg
open Module Filter MvPolynomial
open Quartic.PolynomialBilinearCoordinates
open scoped Topology
variable {K : Type} [Field K] [Infinite K]

/-- The scalar coefficient space required by C.2 exists for every scalar
family in the nonempty open set furnished by C.1. -/
theorem eventually_scalar_coefficient_spaces {d : ℕ} (hd : 2 ≤ d)
    (r : ℕ → ℕ)
    (hr : Tendsto (fun n : ℕ => (r n : ℝ) / (n : ℝ) ^ d)
      atTop (𝓝 (criticalRatio d / (d.factorial : ℝ)))) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ S : Finset (Fin n),
      S.card ≤ Sᶜ.card → Sᶜ.card ≤ S.card + 1 →
      ∃ P : MvPolynomial (Fin (finrank K (Fin (r n) → Forms K n d))) K,
        (∃ q : Fin (r n) → Forms K n d, eval (coordinates K _ q) P ≠ 0) ∧
        ∀ q : Fin (r n) → Forms K n d, eval (coordinates K _ q) P ≠ 0 →
          ∃ C : Submodule K (Poly K n),
            C ≤ Forms K n (d-1) ∧ finrank K C = S.card.choose (d-1) ∧
            Function.Injective (subspaceSymmetricMultiplication C) ∧
            Disjoint (C*C) (familySpace q * Forms K n (d-2)) := by
  obtain ⟨n₀,hn₀⟩ := eventually_generic_scalar_separation (K := K) hd r hr
  refine ⟨n₀,?_⟩
  intro n hn S hS hS'
  obtain ⟨P,hP,hgood⟩ := hn₀ n hn S hS hS' (2*((d-1)/2))
  refine ⟨P,hP,?_⟩
  intro q hq
  obtain ⟨C,hCh,hCd,hCi,hCC⟩ := paired_scalar_space_exists (K := K) S hS (d-1)
  refine ⟨C,hCh,hCd,hCi,?_⟩
  have hs := (hgood q hq).2.symm
  have he : 2*(d-1) = 2*d-2 := by omega
  rw [he] at hCC
  exact hs.mono_left hCC

/-- A finite-variable form of C.2: once the common scalar product image is
separated, the paired space attains the exact coefficient capacity. -/
theorem exists_quadratic_separated_family
    {n h d r L m : ℕ} (hd : 2 ≤ d) (S : Finset (Fin n))
    (hS : S.card ≤ Sᶜ.card) (q : Fin r → Forms K n d)
    (hscalar : Disjoint (familySpace q * Forms K n (d-2))
      (deletedBidegreeSpace K S (2*d-2) (2*((d-1)/2))))
    {X : Type*} [AddCommGroup X] [Module K X]
    (o : Fin L → Forms K h 1) (T : Poly K h →ₗ[K] X)
    (ho : LinearIndependent K (fun p => T (pairProducts (fun i => (o i).val) p)))
    (hm : m ≤ L * (S.card.choose (d-1) / 2)) :
    ∃ f : Fin m → Forms K (h+n) d,
      LinearIndependent K f ∧ finrank K (Submodule.span K (Set.range f)) = m ∧
      ∀ W : Submodule K (Forms K (h+n) d),
        (∀ w : Forms K (h+n) d, w ∈ W → ∀ a : Forms K (h+n) d,
          splitPolynomialDetector T (familySpace q * Forms K n (d-2)) (w.val*a.val) = 0) →
        formalSquare (Submodule.span K (Set.range f)) ⊓
          ((formalMixed W).map formalPolynomialMultiplication).comap
            (formalPolynomialMultiplication (K := K) (n := h+n) (d := d)) = ⊥ := by
  obtain ⟨C,hCh,hCd,hCi,hCC⟩ := paired_scalar_space_exists (K := K) S hS (d-1)
  have he : 2*(d-1) = 2*d-2 := by omega
  rw [he] at hCC
  have hm' : m ≤ Fintype.card (Fin L) * (finrank K C / 2) := by simpa [hCd] using hm
  have hh := exists_separated_homogeneous_family o T ho C
    (deletedBidegreeSpace K S (2*d-2) (2*((d-1)/2)))
    (familySpace q * Forms K n (d-2)) hCh hCi hCC hscalar.symm hm'
  rw [show 1+(d-1)=d by omega] at hh
  exact hh

end Froberg
