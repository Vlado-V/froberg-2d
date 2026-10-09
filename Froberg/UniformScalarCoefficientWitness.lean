module

public import Froberg.ScalarCoefficientWitness
public import Froberg.UniformScalarSeparation

@[expose] public section

/-! Scalar C.1 and C.2 witnesses with one threshold for all infinite fields. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace Froberg
open Module Filter MvPolynomial
open Quartic.PolynomialBilinearCoordinates
open scoped Topology

/-- One nonempty principal open supplies all scalar injections and the
separated paired coefficient space simultaneously. -/
theorem eventually_uniform_scalar_coefficient_witnesses {d : ℕ} (hd : 2≤d)
    (r : ℕ → ℕ)
    (hr : Tendsto (fun n : ℕ => (r n : ℝ)/(n : ℝ)^d)
      atTop (𝓝 (criticalRatio d/(d.factorial : ℝ)))) :
    ∃ n₀ : ℕ, ∀ n≥n₀, ∀ (K : Type) [Field K] [Infinite K], ∀ S : Finset (Fin n),
      S.card≤Sᶜ.card → Sᶜ.card≤S.card+1 →
      ∃ P : MvPolynomial (Fin (finrank K (Fin (r n) → Forms K n d))) K,
        (∃ Q : Fin (r n) → Forms K n d,eval (coordinates K _ Q) P≠0) ∧
        ∀ Q : Fin (r n) → Forms K n d,eval (coordinates K _ Q) P≠0 →
          (∀ t,t≤d-2 → Function.Injective (prefixMultiplication Q t)) ∧
          ∃ C : Submodule K (Poly K n),
            C≤Forms K n (d-1) ∧ finrank K C=S.card.choose (d-1) ∧
            Function.Injective (subspaceSymmetricMultiplication C) ∧
            Disjoint (C*C) (familySpace Q * Forms K n (d-2)) := by
  obtain ⟨n₀,hn₀⟩ := eventually_uniform_generic_scalar_separation hd r hr
  refine ⟨max n₀ 1,?_⟩
  intro n hn K _ _ S hS hS'
  obtain ⟨P,hP,hgood⟩ := hn₀ n (by omega) K S hS hS' (2*((d-1)/2))
  refine ⟨P,hP,?_⟩
  intro Q hQ
  have hh := hgood Q hQ
  exact scalar_coefficient_witness_of_quotient hd (by omega) S hS Q hh.1 hh.2

/-- Reserving z scalar variables preserves the C.1 asymptotic bound. The
family has its actual count r(n+z) while its polynomials use only n variables. -/
theorem eventually_uniform_scalar_coefficient_witnesses_shift {d : ℕ} (hd : 2≤d)
    (r : ℕ → ℕ)
    (hr : Tendsto (fun n : ℕ => (r n : ℝ)/(n : ℝ)^d)
      atTop (𝓝 (criticalRatio d/(d.factorial : ℝ)))) (z : ℕ) :
    ∃ n₀ : ℕ, ∀ n≥n₀, ∀ (K : Type) [Field K] [Infinite K], ∀ S : Finset (Fin n),
      S.card≤Sᶜ.card → Sᶜ.card≤S.card+1 →
      ∃ P : MvPolynomial (Fin (finrank K (Fin (r (n+z)) → Forms K n d))) K,
        (∃ Q : Fin (r (n+z)) → Forms K n d,eval (coordinates K _ Q) P≠0) ∧
        ∀ Q : Fin (r (n+z)) → Forms K n d,eval (coordinates K _ Q) P≠0 →
          (∀ t,t≤d-2 → Function.Injective (prefixMultiplication Q t)) ∧
          ∃ C : Submodule K (Poly K n),
            C≤Forms K n (d-1) ∧ finrank K C=S.card.choose (d-1) ∧
            Function.Injective (subspaceSymmetricMultiplication C) ∧
            Disjoint (C*C) (familySpace Q * Forms K n (d-2)) :=
  eventually_uniform_scalar_coefficient_witnesses hd (fun n => r (n+z))
    (normalized_limit_shift hr z)

/-- The same shifted scalar open also attains the actual outer-family count
in the paired coefficient space. Both count bounds use the full n+z variables,
while the witness itself is supported on the n core variables. -/
theorem eventually_uniform_scalar_coefficient_witnesses_capacity_shift {d h : ℕ}
    (hd : 3≤d) (hh : 0<h) (r f : ℕ → ℕ)
    (hr : Tendsto (fun n : ℕ => (r n : ℝ)/(n : ℝ)^d)
      atTop (𝓝 (criticalRatio d/(d.factorial : ℝ))))
    (hf : Tendsto (fun n : ℕ => (f n : ℝ)/(n : ℝ)^(d-1))
      atTop (𝓝 ((h : ℝ)*criticalRatio d/((d-1).factorial : ℝ)))) (z : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (K : Type) [Field K] [Infinite K], ∀ S : Finset (Fin n),
      S.card≤Sᶜ.card → Sᶜ.card≤S.card+1 →
      ∃ P : MvPolynomial (Fin (finrank K (Fin (r (n+z)) → Forms K n d))) K,
        (∃ Q : Fin (r (n+z)) → Forms K n d,eval (coordinates K _ Q) P≠0) ∧
        ∀ Q : Fin (r (n+z)) → Forms K n d,eval (coordinates K _ Q) P≠0 →
          (∀ t,t≤d-2 → Function.Injective (prefixMultiplication Q t)) ∧
          ∃ C : Submodule K (Poly K n),
            C≤Forms K n (d-1) ∧ finrank K C=S.card.choose (d-1) ∧
            Function.Injective (subspaceSymmetricMultiplication C) ∧
            Disjoint (C*C) (familySpace Q * Forms K n (d-2)) ∧
            f (n+z)≤outerColumnCount d h*(finrank K C/2) := by
  obtain ⟨n₀,hn₀⟩ := eventually_uniform_scalar_coefficient_witnesses_shift
    (by omega : 2≤d) r hr z
  have hcap := eventually_critical_paired_capacity hd hh (fun n => f (n+z))
    (normalized_limit_shift hf z)
  filter_upwards [eventually_ge_atTop n₀,hcap] with n hn hfn
  intro K _ _ S hS hS'
  obtain ⟨P,hP,hgood⟩ := hn₀ n hn K S hS hS'
  refine ⟨P,hP,?_⟩
  intro Q hQ
  obtain ⟨hqi,C,hCh,hCd,hCi,hsep⟩ := hgood Q hQ
  refine ⟨hqi,C,hCh,hCd,hCi,hsep,?_⟩
  have hsum : S.card+Sᶜ.card=n := by simp
  have hhalf : S.card=n/2 := by omega
  simpa only [hCd,hhalf] using hfn


end Froberg
