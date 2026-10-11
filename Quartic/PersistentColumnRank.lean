/-
Copyright (c) 2026 Vlado Vojdanovski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vlado Vojdanovski
-/
module

public import Quartic.DeformationRank

/-!
# Rank from persistent response columns

Response columns obtained at different cancellation orders can be combined
before taking their rank. The hypothesis here records membership in the
perturbed image at every nonzero parameter, rather than imposing a common
cancellation order on all columns.
-/

@[expose] public section

noncomputable section
namespace Quartic.PersistentColumnRank
open Module MvPolynomial

variable {K V W J T : Type*} [Field K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  [AddCommGroup J] [Module K J]
  [AddCommGroup T] [Module K T] [FiniteDimensional K T]

/-- Any fixed family of persistent columns contributes its cokernel rank. -/
theorem rank_gain_principal_open (M₀ M₁ : V →ₗ[K] W) (π : W →ₗ[K] J)
    (B : T →ₗ[K] W) (hπ : π.comp M₀ = 0)
    (hpersist : ∀ ε : K, ε ≠ 0 → ∀ t : T, B t ∈ (M₀ + ε • M₁).range) :
    ∃ D : MvPolynomial (Fin 1) K, eval 0 D ≠ 0 ∧
      ∀ ε : K, ε ≠ 0 → eval (fun _ => ε) D ≠ 0 →
        finrank K M₀.range + finrank K (π.comp B).range ≤
          finrank K (M₀ + ε • M₁).range := by
  classical
  let R := π.comp B
  obtain ⟨P, hP⟩ := M₀.rangeRestrict.exists_rightInverse_of_surjective M₀.range_rangeRestrict
  obtain ⟨S, hS⟩ := R.rangeRestrict.exists_rightInverse_of_surjective R.range_rangeRestrict
  have hPval (u : M₀.range) : M₀ (P u) = u.val :=
    congrArg Subtype.val (LinearMap.congr_fun hP u)
  have hSval (u : R.range) : R (S u) = u.val :=
    congrArg Subtype.val (LinearMap.congr_fun hS u)
  let C := B.comp S
  have hC (u : R.range) : π (C u) = u.val := hSval u
  let E₀ : (M₀.range × R.range) →ₗ[K] W := M₀.range.subtype.coprod C
  let E₁ : (M₀.range × R.range) →ₗ[K] W := (M₁.comp P).comp (LinearMap.fst K _ _)
  have hπu (u : M₀.range) : π u.val = 0 := by
    rw [← hPval u]
    exact LinearMap.congr_fun hπ (P u)
  have hE₀ : Function.Injective E₀ := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm ?_ bot_le
    intro x hx
    change x = 0
    change x.1.val + C x.2 = 0 at hx
    have hy : x.2 = 0 := by
      apply Subtype.ext
      have hh := congrArg π hx
      simpa only [map_add, hπu, hC, zero_add, map_zero, Submodule.coe_zero] using hh
    have hu : x.1 = 0 := by
      apply Subtype.ext
      simpa only [hy, map_zero, add_zero, Submodule.coe_zero] using hx
    exact Prod.ext hu hy
  let E : (Fin 1 → K) → ((M₀.range × R.range) →ₗ[K] W) := fun a => E₀ + a 0 • E₁
  have hEpoly : IsPolynomialFamily E :=
    (isPolynomialFamily_const E₀).add
      ((isPolynomialFamily_linear (LinearMap.proj (0 : Fin 1))).smul
        (isPolynomialFamily_const E₁))
  obtain ⟨D, hD, hEinj⟩ := injective_polynomial_principal_open E hEpoly 0
    (by simpa [E] using hE₀)
  refine ⟨D, hD, ?_⟩
  intro ε he hDa
  let a : Fin 1 → K := fun _ => ε
  have hsub : (E a).range ≤ (M₀ + ε • M₁).range := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨z, hz⟩ := hpersist ε he (S x.2)
    refine ⟨P x.1 + z, ?_⟩
    rw [map_add, hz]
    change M₀ (P x.1) + ε • M₁ (P x.1) + C x.2 =
      x.1.val + C x.2 + ε • M₁ (P x.1)
    rw [hPval]
    abel
  have hr := Submodule.finrank_mono hsub
  rw [LinearMap.finrank_range_of_inj (hEinj a hDa), Module.finrank_prod] at hr
  exact hr

/-- A nonzero specialization realizes the combined response rank. -/
theorem rank_gain [Infinite K] (M₀ M₁ : V →ₗ[K] W) (π : W →ₗ[K] J)
    (B : T →ₗ[K] W) (hπ : π.comp M₀ = 0)
    (hpersist : ∀ ε : K, ε ≠ 0 → ∀ t : T, B t ∈ (M₀ + ε • M₁).range) :
    ∃ ε : K, ε ≠ 0 ∧ finrank K M₀.range + finrank K (π.comp B).range ≤
      finrank K (M₀ + ε • M₁).range := by
  obtain ⟨D, hD, h⟩ := rank_gain_principal_open M₀ M₁ π B hπ hpersist
  have hDn : D ≠ 0 := by intro hz; simp [hz] at hD
  obtain ⟨a, ha⟩ := PolynomialImageAvoidance.exists_eval_ne_zero
    (mul_ne_zero hDn (X_ne_zero (0 : Fin 1)))
  have hDa : eval a D ≠ 0 := (mul_ne_zero_iff.mp (by simpa using ha)).1
  have he : a 0 ≠ 0 := (mul_ne_zero_iff.mp (by simpa using ha)).2
  refine ⟨a 0, he, h (a 0) he ?_⟩
  have hconst : (fun _ : Fin 1 => a 0) = a := by ext i; fin_cases i; rfl
  rwa [hconst]

omit [FiniteDimensional K V] [FiniteDimensional K W] in
/-- Four exact cancellations produce a fourth-order response. -/
theorem fourth_response (M₀ M₁ : V →ₗ[K] W) (a₀ a₁ a₂ a₃ : V) (ε : K)
    (h₀ : M₀ a₀ = 0) (h₁ : M₀ a₁ = -M₁ a₀)
    (h₂ : M₀ a₂ = -M₁ a₁) (h₃ : M₀ a₃ = -M₁ a₂) :
    (M₀ + ε • M₁) (a₀ + ε • a₁ + ε ^ 2 • a₂ + ε ^ 3 • a₃) =
      ε ^ 4 • M₁ a₃ := by
  simp only [LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul,
    h₀, h₁, h₂, h₃, zero_add, smul_neg, smul_add, smul_smul]
  module

omit [FiniteDimensional K V] [FiniteDimensional K W] in
/-- The normalized fourth-order response is in the image for every nonzero parameter. -/
theorem fourth_response_mem (M₀ M₁ : V →ₗ[K] W) (a₀ a₁ a₂ a₃ : V) (ε : K)
    (he : ε ≠ 0) (h₀ : M₀ a₀ = 0) (h₁ : M₀ a₁ = -M₁ a₀)
    (h₂ : M₀ a₂ = -M₁ a₁) (h₃ : M₀ a₃ = -M₁ a₂) :
    M₁ a₃ ∈ (M₀ + ε • M₁).range := by
  refine ⟨(ε ^ 4)⁻¹ • (a₀ + ε • a₁ + ε ^ 2 • a₂ + ε ^ 3 • a₃), ?_⟩
  rw [map_smul, fourth_response M₀ M₁ a₀ a₁ a₂ a₃ ε h₀ h₁ h₂ h₃,
    smul_smul, inv_mul_cancel₀ (pow_ne_zero _ he), one_smul]

/-- The common image of every nonzero specialization is a vector space. -/
def persistent (M₀ M₁ : V →ₗ[K] W) : Submodule K W :=
  ⨅ ε : K, ⨅ (_ : ε ≠ 0), (M₀ + ε • M₁).range

omit [FiniteDimensional K V] [FiniteDimensional K W] in
theorem mem_persistent (M₀ M₁ : V →ₗ[K] W) (w : W) :
    w ∈ persistent M₀ M₁ ↔ ∀ ε : K, ε ≠ 0 → w ∈ (M₀ + ε • M₁).range := by
  simp only [persistent, Submodule.mem_iInf]

omit [FiniteDimensional K T] in
/-- Pointwise realizations suffice; the source corrections need not be chosen linearly. -/
theorem rank_gain_of_realizations_principal_open
    (M₀ M₁ : V →ₗ[K] W) (π : W →ₗ[K] J) (N : T →ₗ[K] J)
    (hπ : π.comp M₀ = 0)
    (hreal : ∀ t : T, ∃ w : W, w ∈ persistent M₀ M₁ ∧ π w = N t) :
    ∃ D : MvPolynomial (Fin 1) K, eval 0 D ≠ 0 ∧
      ∀ ε : K, ε ≠ 0 → eval (fun _ => ε) D ≠ 0 →
        finrank K M₀.range + finrank K N.range ≤ finrank K (M₀ + ε • M₁).range := by
  let P := persistent M₀ M₁
  have hsub : N.range ≤ (π.comp P.subtype).range := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨w, hw, he⟩ := hreal t
    exact ⟨⟨w, hw⟩, he⟩
  obtain ⟨D, hD, h⟩ := rank_gain_principal_open M₀ M₁ π P.subtype hπ
    (fun ε he w => (mem_persistent M₀ M₁ w.val).mp w.property ε he)
  exact ⟨D, hD, fun ε he hDε =>
    (Nat.add_le_add_left (Submodule.finrank_mono hsub) _).trans (h ε he hDε)⟩

omit [FiniteDimensional K V] [FiniteDimensional K W] in
theorem second_response_mem (M₀ M₁ : V →ₗ[K] W) (a b : V)
    (ha : M₀ a = 0) (hb : M₀ b = -M₁ a) : M₁ b ∈ persistent M₀ M₁ := by
  rw [mem_persistent]
  intro ε he
  refine ⟨(ε ^ 2)⁻¹ • (a + ε • b), ?_⟩
  rw [map_smul, deformation_second_response M₀ M₁ ε a b ha hb,
    smul_smul, inv_mul_cancel₀ (pow_ne_zero _ he), one_smul]

omit [FiniteDimensional K V] [FiniteDimensional K W] in
theorem first_response_mem (M₀ M₁ : V →ₗ[K] W) (a : V)
    (ha : M₀ a = 0) : M₁ a ∈ persistent M₀ M₁ := by
  rw [mem_persistent]
  intro ε he
  refine ⟨ε⁻¹ • a, ?_⟩
  rw [map_smul, deformation_first_response M₀ M₁ ε a ha,
    smul_smul, inv_mul_cancel₀ he, one_smul]

end Quartic.PersistentColumnRank
