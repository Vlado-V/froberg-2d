import Froberg.PolynomialLinearAvoidance
import Froberg.ProjectionCharts
import Quartic.BilinearGeneric

/-! Projective coefficient charts for two simultaneous generator families.
Each nonzero family has its own coefficient span; one relative scalar joins
the two projective charts without treating their parameters independently. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg
open Module MvPolynomial Quartic Quartic.ProjectiveTupleCharts
variable {K : Type*} [Field K] [Infinite K] {a₁ a₂ q₁ q₂ d₁ d₂ : ℕ}

/-- The existing projective tuple chart is a polynomial vector-space family. -/
theorem projectiveTuple_polynomial (c : ChartType a₁ q₁ d₁) :
    IsPolynomialFamily (tupleMap (K := K) c) := by
  classical
  intro L
  refine ⟨∑ i, ∑ j, tuplePolynomial c i j * C (L (Pi.single i (Pi.single j 1))),?_⟩
  intro p
  change _ = L (tupleMap c p)
  simp only [map_sum,map_mul,MvPolynomial.eval_C]
  calc
    _ = L (∑ i, ∑ j, tupleMap c p i j • Pi.single i (Pi.single j 1)) := by
      simp only [map_sum,map_smul,smul_eq_mul,tupleMap]
    _ = L (tupleMap c p) := congrArg L (ProjectiveKernelIncidence.tuple_expansion (tupleMap c p)).symm

abbrev TwoTupleParameters (c₁ : ChartType a₁ q₁ d₁) (c₂ : ChartType a₂ q₂ d₂) :=
  ParameterIndex c₁ ⊕ (ParameterIndex c₂ ⊕ Unit)

def twoTupleChart (c₁ : ChartType a₁ q₁ d₁) (c₂ : ChartType a₂ q₂ d₂)
    (p : TwoTupleParameters c₁ c₂ → K) :
    (Fin q₁ → Fin a₁ → K) × (Fin q₂ → Fin a₂ → K) :=
  (tupleMap c₁ (p ∘ Sum.inl),p (Sum.inr (Sum.inr ())) •
    tupleMap c₂ (p ∘ Sum.inr ∘ Sum.inl))

theorem twoTupleChart_polynomial (c₁ : ChartType a₁ q₁ d₁) (c₂ : ChartType a₂ q₂ d₂) :
    IsPolynomialFamily (twoTupleChart (K := K) c₁ c₂) := by
  classical
  exact (polynomial_family_reindex (projectiveTuple_polynomial c₁) Sum.inl).prod_mk
    ((isPolynomialFamily_linear (LinearMap.proj (Sum.inr (Sum.inr ())))).smul
      (polynomial_family_reindex (projectiveTuple_polynomial c₂) (Sum.inr ∘ Sum.inl)))

/-- Precisely one common projective normalization is saved. -/
theorem twoTuple_parameter_count (c₁ : ChartType a₁ q₁ d₁) (c₂ : ChartType a₂ q₂ d₂) :
    Fintype.card (TwoTupleParameters c₁ c₂) =
      d₁*(a₁-d₁)+q₁*d₁+d₂*(a₂-d₂)+q₂*d₂-1 := by
  classical
  have h₁ : 0 < q₁*d₁ := Nat.mul_pos (Fin.pos c₁.2.1) (Fin.pos c₁.2.2)
  have h₂ : 0 < q₂*d₂ := Nat.mul_pos (Fin.pos c₂.2.1) (Fin.pos c₂.2.2)
  have hc₁ := ProjectiveTupleCharts.parameter_count c₁
  have hc₂ := ProjectiveTupleCharts.parameter_count c₂
  simp only [TwoTupleParameters,Fintype.card_sum,Fintype.card_unit] at hc₁ hc₂ ⊢
  omega

/-- Every pair with both families nonzero has one common scaling and a
literal value of the combined polynomial chart. -/
theorem cover_two_nonzero_tuples
    (F₁ : Fin q₁ → Fin a₁ → K) (F₂ : Fin q₂ → Fin a₂ → K)
    (h₁ : 0 < d₁) (h₂ : 0 < d₂)
    (hr₁ : finrank K (Submodule.span K (Set.range F₁)) = d₁)
    (hr₂ : finrank K (Submodule.span K (Set.range F₂)) = d₂) :
    ∃ c₁ : ChartType a₁ q₁ d₁, ∃ c₂ : ChartType a₂ q₂ d₂,
      ∃ p : TwoTupleParameters c₁ c₂ → K, ∃ s : K,
        s ≠ 0 ∧ (F₁,F₂) = s • twoTupleChart c₁ c₂ p := by
  obtain ⟨c₁,p₁,s₁,hs₁,hF₁⟩ := cover_rank_tuple F₁ h₁ hr₁
  obtain ⟨c₂,p₂,s₂,hs₂,hF₂⟩ := cover_rank_tuple F₂ h₂ hr₂
  refine ⟨c₁,c₂,Sum.elim p₁ (Sum.elim p₂ (fun _ => s₁⁻¹*s₂)),s₁,hs₁,?_⟩
  apply Prod.ext
  · exact hF₁
  · change F₂ = s₁ • ((s₁⁻¹*s₂) • tupleMap c₂ p₂)
    rw [smul_smul,← mul_assoc,mul_inv_cancel₀ hs₁,one_mul]
    exact hF₂

/-- Avoidance on a combined chart with the exact two-family parameter count. -/
theorem twoTuple_chart_avoidance {V W : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (B : ((Fin q₁ → Fin a₁ → K) × (Fin q₂ → Fin a₂ → K)) →ₗ[K] V →ₗ[K] W)
    (c₁ : ChartType a₁ q₁ d₁) (c₂ : ChartType a₂ q₂ d₂) :
    ∃ D : MvPolynomial (Fin (finrank K V)) K, (∃ x, eval x D ≠ 0) ∧
      ∀ x, eval x D ≠ 0 → ∀ p,
        d₁*(a₁-d₁)+q₁*d₁+d₂*(a₂-d₂)+q₂*d₂ ≤
          finrank K (B (twoTupleChart c₁ c₂ p)).range →
        B (twoTupleChart c₁ c₂ p) ((Module.finBasis K V).equivFun.symm x) ≠ 0 := by
  apply polynomial_linear_kernel_avoidance
    (fun p => B (twoTupleChart c₁ c₂ p)) ((twoTupleChart_polynomial c₁ c₂).linear_comp B)
  rw [twoTuple_parameter_count]
  have h₁ : 0 < q₁*d₁ := Nat.mul_pos (Fin.pos c₁.2.1) (Fin.pos c₁.2.2)
  omega

end Froberg
