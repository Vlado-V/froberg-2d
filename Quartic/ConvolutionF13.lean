import Quartic.ConvolutionF13Square

/-!
# The actual convolution presentation modulo a quadratic family

The source is one copy of `(A_Q)₂` per convolution column and the target is
three copies of `(A_Q)₃`. The map is the original polynomial presentation
reduced modulo the actual quadratic family; no identification is assumed.
-/
noncomputable section
namespace Quartic.ConvolutionF13
open Module MvPolynomial ConvolutionFreePieces ConvolutionFreeMultiplication
open ConvolutionOuterIncidence ConvolutionF13Square
variable {K : Type*} [Field K] {t w q : ℕ}

/-- Taking a fixed linear map separately in each row gives the product image. -/
theorem range_rows {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Module K A] [Module K B] (n : ℕ) (f : (Fin q → A) →ₗ[K] B) :
    LinearMap.range (rowwise n f) =
        Submodule.pi Set.univ (fun _ : Fin n => LinearMap.range f) := by
  classical
  ext u
  constructor
  · rintro ⟨z, rfl⟩
    intro r _
    exact ⟨fun j => z j r, rfl⟩
  · intro hu
    have h : ∀ r, ∃ z : Fin q → A, f z = u r := fun r => hu r (Set.mem_univ r)
    choose z hz using h
    exact ⟨fun j r => z r j, funext hz⟩

/-- Multiplication by homogeneous constants has exactly the actual quadratic span. -/
theorem quadraticCombination_range (Q : Coefficients K t w q) :
    LinearMap.range (quadraticCombination Q) = Submodule.span K (Set.range Q) := by
  classical
  ext f
  constructor
  · rintro ⟨z, rfl⟩
    apply (Submodule.mem_span_range_iff_exists_fun K).mpr
    refine ⟨fun j => (z j).val.coeff 0, ?_⟩
    apply Subtype.ext
    simp only [quadraticCombination_val, AddSubmonoidClass.coe_finsetSum,
      SetLike.val_smul, smul_eq_C_mul]
    apply Finset.sum_congr rfl
    intro j _
    exact (mul_comm (C ((z j).val.coeff 0)) (Q j).val).trans
      (congrArg (fun p => (Q j).val * p)
        (ConvolutionPresentation.degreeZero_eq_constant (z j)).symm)
  · intro hf
    obtain ⟨s, hs⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hf
    refine ⟨fun j => ⟨C (s j), isHomogeneous_C _ _⟩, ?_⟩
    rw [← hs]
    apply Subtype.ext
    simp only [quadraticCombination_val, AddSubmonoidClass.coe_finsetSum,
      SetLike.val_smul, smul_eq_C_mul]
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _

/-- The top relations are exactly independent copies of the quadratic span. -/
theorem topRelations_range (Q : Coefficients K t w q) :
    LinearMap.range (topRelations Q) =
      Submodule.pi Set.univ (fun _ : Fin (t+2) => Submodule.span K (Set.range Q)) := by
  rw [topRelations, range_rows, quadraticCombination_range]

/-- The cubic row relations are precisely copies of the ordinary cubic product image. -/
theorem bottomMultiplication_range (Q : Coefficients K t w q) :
    LinearMap.range (bottomMultiplication Q) =
      Submodule.pi Set.univ (fun _ : Fin 3 => CubicGeneric.quadraticLinearProducts Q) := by
  rw [bottomMultiplication, range_rows, CubicGeneric.cubicMap_range]

abbrev QuadraticQuotient (Q : Coefficients K t w q) :=
  Forms K (t+w) 2 ⧸ Submodule.span K (Set.range Q)
abbrev Source (Q : Coefficients K t w q) := Fin (t+2) → QuadraticQuotient Q
abbrev Target (Q : Coefficients K t w q) := Fin 3 → CubicGeneric.CubicQuotient Q

/-- Coordinatewise identification of the top quotient with `E ⊗ (A_Q)₂`. -/
def sourceEquiv (Q : Coefficients K t w q) :
    (Top K t w ⧸ LinearMap.range (topRelations Q)) ≃ₗ[K] Source Q :=
  (Submodule.quotEquivOfEq _ _ (topRelations_range Q)).trans (Submodule.quotientPi _)

/-- Coordinatewise identification of the right quotient with `X ⊗ (A_Q)₃`. -/
def targetEquiv (Q : Coefficients K t w q) :
    (Ambient K t w ⧸ LinearMap.range (bottomMultiplication Q)) ≃ₗ[K] Target Q :=
  (Submodule.quotEquivOfEq _ _ (bottomMultiplication_range Q)).trans (Submodule.quotientPi _)

@[simp] theorem sourceEquiv_mk (Q : Coefficients K t w q) (u : Top K t w) :
    sourceEquiv Q (Submodule.Quotient.mk u) = fun k => Submodule.Quotient.mk (u k) := rfl

@[simp] theorem targetEquiv_mk (Q : Coefficients K t w q) (v : Ambient K t w) :
    targetEquiv Q (Submodule.Quotient.mk v) = fun r => Submodule.Quotient.mk (v r) := rfl

/-- The actual convolution presentation on the ordinary quadratic and cubic quotients. -/
def f13Map (Q : Coefficients K t w q) : Source Q →ₗ[K] Target Q :=
  (targetEquiv Q).toLinearMap.comp ((exchangeMap Q).comp (sourceEquiv Q).symm.toLinearMap)

/-- On polynomial representatives, this is exactly the original convolution matrix. -/
theorem f13Map_mk (Q : Coefficients K t w q) (u : Top K t w) :
    f13Map Q (fun k => Submodule.Quotient.mk (u k)) =
      fun r => Submodule.Quotient.mk (ConvolutionFree.presentation u r) := by
  change targetEquiv Q (exchangeMap Q ((sourceEquiv Q).symm _)) = _
  rw [← sourceEquiv_mk Q u, LinearEquiv.symm_apply_apply, exchangeMap_mk, targetEquiv_mk]

/-- Injectivity of the actual outer map implies injectivity of actual `F₁₃`. -/
theorem f13Map_injective (ht : 2 ≤ t) (Q : Coefficients K t w q)
    (hQ : Function.Injective (outerMap Q)) : Function.Injective (f13Map Q) :=
  (targetEquiv Q).injective.comp ((exchangeMap_injective ht Q hQ).comp
    (sourceEquiv Q).symm.injective)

/-- The ordinary quadratic quotient has its expected dimension for independent quadrics. -/
theorem quadraticQuotient_finrank (Q : Coefficients K t w q) (hQ : LinearIndependent K Q) :
    finrank K (QuadraticQuotient Q) = (t+w+1).choose 2 - q := by
  rw [Submodule.finrank_quotient, finrank_span_eq_card hQ, Fintype.card_fin]
  simp [Quartic.finrank_forms]

/-- The source dimension is the ordinary `c*α` count. -/
theorem source_finrank (Q : Coefficients K t w q) (hQ : LinearIndependent K Q) :
    finrank K (Source Q) = (t+2) * ((t+w+1).choose 2 - q) := by
  calc
    _ = ∑ k : Fin (t+2), finrank K (QuadraticQuotient Q) := Module.finrank_pi_fintype K
    _ = _ := by simp [quadraticQuotient_finrank Q hQ]

/-- The target dimension is the ordinary `3*β` count when cubic products are independent. -/
theorem target_finrank (Q : Coefficients K t w q)
    (hQ : Function.Injective (CubicGeneric.cubicMap Q)) :
    finrank K (Target Q) = 3 * ((t+w+2).choose 3 - (t+w)*q) := by
  calc
    _ = ∑ r : Fin 3, finrank K (CubicGeneric.CubicQuotient Q) := Module.finrank_pi_fintype K
    _ = _ := by simp [CubicGeneric.cubic_quotient_finrank_of_injective Q hQ]

abbrev Cokernel (Q : Coefficients K t w q) := Target Q ⧸ LinearMap.range (f13Map Q)

/-- Rank-nullity for the actual reduced convolution presentation. -/
theorem cokernel_euler (ht : 2 ≤ t) (Q : Coefficients K t w q)
    (hQ : Function.Injective (outerMap Q)) :
    finrank K (Cokernel Q) + finrank K (Source Q) = finrank K (Target Q) := by
  have h := Submodule.finrank_quotient_add_finrank (LinearMap.range (f13Map Q))
  rwa [LinearMap.finrank_range_of_inj (f13Map_injective ht Q hQ)] at h

end Quartic.ConvolutionF13
