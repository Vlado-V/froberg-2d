import Froberg.ScalarCoefficientWitness

/-! Scalar C.2 data with a fixed number of variables reserved for private
powers. The threshold is independent of all output-frame parameters. -/
noncomputable section
namespace Froberg
open Module Filter MvPolynomial
open scoped Topology
variable {K : Type} [Field K] [Infinite K]

theorem eventually_quadratic_scalar_data {d h : ℕ}
    (hd : 3≤d) (hh : 0 < h) (r f : ℕ → ℕ)
    (hr : Tendsto (fun n : ℕ => (r n : ℝ)/(n : ℝ)^d)
      atTop (𝓝 (criticalRatio d/(d.factorial : ℝ))))
    (hf : Tendsto (fun n : ℕ => (f n : ℝ)/(n : ℝ)^(d-1))
      atTop (𝓝 ((h : ℝ)*criticalRatio d/((d-1).factorial : ℝ)))) (u : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      ∃ a : ℕ,a+u=n ∧ ∃ Q : Fin (r n) → Forms K a d,
        (∀ t,t≤d-2 → Function.Injective (prefixMultiplication Q t)) ∧
        ∃ C : Submodule K (Poly K a), C≤Forms K a (d-1) ∧
          Function.Injective (subspaceSymmetricMultiplication C) ∧
          Disjoint (C*C) (familySpace Q*Forms K a (d-2)) ∧
          f n≤outerColumnCount d h*(finrank K C/2) := by
  classical
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    (eventually_scalar_coefficient_witnesses_capacity_shift (K := K) hd hh r f hr hf u)
  refine eventually_atTop.mpr ⟨N+u,?_⟩
  intro n hn
  obtain ⟨a,han⟩ : ∃ a,a+u=n := ⟨n-u,Nat.sub_add_cancel (by omega)⟩
  have ha : N≤a := by omega
  subst n
  obtain ⟨S,_,hS⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin a)))
    (n := a/2) (by simp only [Finset.card_univ,Fintype.card_fin];omega)
  have hsum : S.card+Sᶜ.card=a := by simp
  have hS₁ : S.card≤Sᶜ.card := by omega
  have hS₂ : Sᶜ.card≤S.card+1 := by omega
  obtain ⟨P,⟨Q,hQP⟩,hgood⟩ := hN a ha S hS₁ hS₂
  obtain ⟨hQ,C,hCdeg,_,hC,hCQ,hcap⟩ := hgood Q hQP
  exact ⟨a,rfl,Q,hQ,C,hCdeg,hC,hCQ,hcap⟩

end Froberg
