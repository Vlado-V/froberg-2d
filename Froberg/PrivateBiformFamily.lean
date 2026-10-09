module

public import Froberg.PreparedPrivateFirstRow
public import Froberg.GeneralLinearColumns

@[expose] public section

/-! Literal private powers as homogeneous biforms, and the two independent
core linear forms used in the extension argument. -/
noncomputable section
namespace Froberg
open Module MvPolynomial PrivateColumns
variable {K : Type} [Field K] [Infinite K]
variable {σ : Type*} [Fintype σ] {a z d b : ℕ}

def privatePowerBiform (l : Fin b → homogeneousSubmodule σ K 1) (ι : Fin b ↪ Fin z) :
    Fin b → FullBiform K σ (a+z) 1 (d-1) := fun i =>
  ⟨rename Sum.inl (l i).val*rename Sum.inr (monomial (privateExponent a (d-1) ι i) (1:K)),
    mul_mem_biformImage _ _ (l i).property
      (isHomogeneous_monomial _ (privateExponent_degree ι i))⟩

@[simp] theorem privatePowerBiform_val
    (l : Fin b → homogeneousSubmodule σ K 1) (ι : Fin b ↪ Fin z) (i : Fin b) :
    (privatePowerBiform (a := a) (d := d) l ι i).val=
      rename Sum.inl (l i).val*rename Sum.inr (monomial (privateExponent a (d-1) ι i) (1:K)) := rfl

theorem exists_two_core_linear_forms (ha : 2≤a) :
    ∃ ell : Fin 2 → Forms K a 1,LinearIndependent K ell := by
  let e : (Fin a → K) ≃ₗ[K] Forms K a 1 := LinearEquiv.ofFinrankEq _ _ (by
    rw [finrank_forms K a 1 (by omega)]
    simp)
  let i : Fin 2 → Fin a := Fin.castLE ha
  have hi : Function.Injective i := Fin.castLE_injective ha
  refine ⟨fun j => e (Pi.basisFun K (Fin a) (i j)),?_⟩
  exact ((Pi.basisFun K (Fin a)).linearIndependent.comp i hi).map'
    e.toLinearMap (LinearMap.ker_eq_bot.mpr e.injective)

end Froberg
