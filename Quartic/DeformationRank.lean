import Quartic.PolynomialRankOpen
import Quartic.Deformation
import Quartic.PolynomialImageAvoidance

/-!
# Rank gained from exact corrected columns

This constructs a determinant-open normalized family directly from split
image pivots and the actual response of the two cancellation equations.
Every normalized response column belongs to the perturbed image at a
nonzero parameter. No weighted-factorization or numerical-rank premise is
retained in the resulting rank-gain theorem.
-/
noncomputable section
namespace Quartic.DeformationRank
open Module MvPolynomial
variable {K V W J : Type*} [Field K] [Infinite K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  [AddCommGroup J] [Module K J] [FiniteDimensional K J]
set_option maxHeartbeats 1000000

/-- The two exact cancellation equations on a corrected column. -/
def equations (M₀ M₁ : V →ₗ[K] W) : (V × V) →ₗ[K] W × W :=
  (M₀.comp (LinearMap.fst K V V)).prod
    ((M₁.comp (LinearMap.fst K V V)) + (M₀.comp (LinearMap.snd K V V)))

/-- The true second response of a corrected column. -/
def secondResponse (M₀ M₁ : V →ₗ[K] W) (π : W →ₗ[K] J) :
    (equations M₀ M₁).ker →ₗ[K] J :=
  π.comp (M₁.comp ((LinearMap.snd K V V).comp (equations M₀ M₁).ker.subtype))

theorem column_equations (M₀ M₁ : V →ₗ[K] W) (a : (equations M₀ M₁).ker) :
    M₀ a.val.1 = 0 ∧ M₀ a.val.2 = -M₁ a.val.1 := by
  have h := a.property
  change (M₀ a.val.1, M₁ a.val.1 + M₀ a.val.2) = (0,0) at h
  exact ⟨congrArg Prod.fst h, eq_neg_of_add_eq_zero_right (congrArg Prod.snd h)⟩

/-- Corrected source columns give the rank gain of their actual cokernel responses. -/
theorem rank_gain_principal_open (M₀ M₁ : V →ₗ[K] W) (π : W →ₗ[K] J)
    (hπ : π.comp M₀ = 0) :
    ∃ D : MvPolynomial (Fin 1) K, eval 0 D ≠ 0 ∧
      ∀ ε : K, ε ≠ 0 → eval (fun _ => ε) D ≠ 0 →
        finrank K M₀.range + finrank K (secondResponse M₀ M₁ π).range ≤
          finrank K (M₀ + ε • M₁).range := by
  classical
  let R := secondResponse M₀ M₁ π
  obtain ⟨P,hP⟩ := M₀.rangeRestrict.exists_rightInverse_of_surjective M₀.range_rangeRestrict
  obtain ⟨S,hS⟩ := R.rangeRestrict.exists_rightInverse_of_surjective R.range_rangeRestrict
  have hPval (u : M₀.range) : M₀ (P u) = u.val := by
    exact congrArg Subtype.val (LinearMap.congr_fun hP u)
  have hSval (u : R.range) : R (S u) = u.val := by
    exact congrArg Subtype.val (LinearMap.congr_fun hS u)
  let B : R.range →ₗ[K] W := M₁.comp
    ((LinearMap.snd K V V).comp ((equations M₀ M₁).ker.subtype.comp S))
  have hB (u : R.range) : π (B u) = u.val := hSval u
  let E₀ : (M₀.range × R.range) →ₗ[K] W := M₀.range.subtype.coprod B
  let E₁ : (M₀.range × R.range) →ₗ[K] W := (M₁.comp P).comp (LinearMap.fst K _ _)
  have hπu (u : M₀.range) : π u.val = 0 := by
    rw [← hPval u]
    exact LinearMap.congr_fun hπ (P u)
  have hE₀ : Function.Injective E₀ := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm ?_ bot_le
    intro x hx
    change x = 0
    change x.1.val + B x.2 = 0 at hx
    have hy : x.2 = 0 := by
      apply Subtype.ext
      have hh := congrArg π hx
      simpa only [map_add,hπu,hB,zero_add,map_zero,Submodule.coe_zero] using hh
    have hu : x.1 = 0 := by
      apply Subtype.ext
      simpa only [hy,map_zero,add_zero,Submodule.coe_zero] using hx
    exact Prod.ext hu hy
  let E : (Fin 1 → K) → ((M₀.range × R.range) →ₗ[K] W) := fun a => E₀ + a 0 • E₁
  have hEpoly : IsPolynomialFamily E :=
    (isPolynomialFamily_const E₀).add
      ((isPolynomialFamily_linear (LinearMap.proj (0 : Fin 1))).smul (isPolynomialFamily_const E₁))
  obtain ⟨D,hD,hEinj⟩ := injective_polynomial_principal_open E hEpoly 0 (by simpa [E] using hE₀)
  refine ⟨D,hD,?_⟩
  intro ε he hDa
  let a : Fin 1 → K := fun _ => ε
  have hsub : (E a).range ≤ (M₀ + a 0 • M₁).range := by
    rintro _ ⟨x,rfl⟩
    let z := S x.2
    have hz := column_equations M₀ M₁ z
    have he2 : (a 0)^2 ≠ 0 := pow_ne_zero _ he
    refine ⟨P x.1 + ((a 0)^2)⁻¹ • (z.val.1 + a 0 • z.val.2), ?_⟩
    rw [map_add,map_smul,deformation_second_response _ _ _ _ _ hz.1 hz.2,
      smul_smul,inv_mul_cancel₀ he2,one_smul]
    change M₀ (P x.1) + a 0 • M₁ (P x.1) + M₁ z.val.2 =
      x.1.val + B x.2 + a 0 • M₁ (P x.1)
    rw [hPval]
    change x.1.val + a 0 • M₁ (P x.1) + B x.2 = _
    abel
  have hr := Submodule.finrank_mono hsub
  rw [LinearMap.finrank_range_of_inj (hEinj a hDa),Module.finrank_prod] at hr
  exact hr


/-- A nonzero specialization attains the actual second-response rank gain. -/
theorem rank_gain (M₀ M₁ : V →ₗ[K] W) (π : W →ₗ[K] J)
    (hπ : π.comp M₀ = 0) :
    ∃ ε : K, ε ≠ 0 ∧
      finrank K M₀.range + finrank K (secondResponse M₀ M₁ π).range ≤
        finrank K (M₀ + ε • M₁).range := by
  obtain ⟨D,hD,h⟩ := rank_gain_principal_open M₀ M₁ π hπ
  have hDn : D ≠ 0 := by intro hz; simp [hz] at hD
  obtain ⟨a,ha⟩ := PolynomialImageAvoidance.exists_eval_ne_zero
    (mul_ne_zero hDn (X_ne_zero (0 : Fin 1)))
  have hDa : eval a D ≠ 0 := (mul_ne_zero_iff.mp (by simpa using ha)).1
  have he : a 0 ≠ 0 := (mul_ne_zero_iff.mp (by simpa using ha)).2
  refine ⟨a 0,he,h (a 0) he ?_⟩
  have hconst : (fun _ : Fin 1 => a 0) = a := by ext i; fin_cases i; rfl
  rwa [hconst]

/-- A response map realized by exact corrected columns contributes its full actual image rank. -/
theorem rank_gain_of_realizations {T : Type*} [AddCommGroup T] [Module K T]
    (M₀ M₁ : V →ₗ[K] W) (π : W →ₗ[K] J) (N : T →ₗ[K] J)
    (hπ : π.comp M₀ = 0)
    (hreal : ∀ ξ : T, ∃ a b : V,
      M₀ a = 0 ∧ M₀ b = -M₁ a ∧ π (M₁ b) = N ξ) :
    ∃ ε : K, ε ≠ 0 ∧ finrank K M₀.range + finrank K N.range ≤
      finrank K (M₀ + ε • M₁).range := by
  have hsub : N.range ≤ (secondResponse M₀ M₁ π).range := by
    rintro _ ⟨ξ,rfl⟩
    obtain ⟨a,b,ha,hb,he⟩ := hreal ξ
    refine ⟨⟨(a,b),?_⟩,he⟩
    change (M₀ a,M₁ a + M₀ b) = (0,0)
    rw [ha,hb,add_neg_cancel]
  obtain ⟨ε,he,hr⟩ := rank_gain M₀ M₁ π hπ
  exact ⟨ε,he,(Nat.add_le_add_left (Submodule.finrank_mono hsub) _).trans hr⟩

/-- The same concrete response rank gain holds on a principal open of nonzero parameters. -/
theorem rank_gain_of_realizations_principal_open {T : Type*} [AddCommGroup T] [Module K T]
    (M₀ M₁ : V →ₗ[K] W) (π : W →ₗ[K] J) (N : T →ₗ[K] J)
    (hπ : π.comp M₀ = 0)
    (hreal : ∀ ξ : T, ∃ a b : V,
      M₀ a = 0 ∧ M₀ b = -M₁ a ∧ π (M₁ b) = N ξ) :
    ∃ D : MvPolynomial (Fin 1) K, eval 0 D ≠ 0 ∧
      ∀ ε : K, ε ≠ 0 → eval (fun _ => ε) D ≠ 0 →
        finrank K M₀.range + finrank K N.range ≤ finrank K (M₀ + ε • M₁).range := by
  have hsub : N.range ≤ (secondResponse M₀ M₁ π).range := by
    rintro _ ⟨ξ,rfl⟩
    obtain ⟨a,b,ha,hb,he⟩ := hreal ξ
    refine ⟨⟨(a,b),?_⟩,he⟩
    change (M₀ a,M₁ a + M₀ b) = (0,0)
    rw [ha,hb,add_neg_cancel]
  obtain ⟨D,hD,h⟩ := rank_gain_principal_open M₀ M₁ π hπ
  exact ⟨D,hD,fun ε he hDε =>
    (Nat.add_le_add_left (Submodule.finrank_mono hsub) _).trans (h ε he hDε)⟩

end Quartic.DeformationRank
