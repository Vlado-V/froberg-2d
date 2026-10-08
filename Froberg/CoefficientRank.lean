import Mathlib

/-! The exact rank bound for restricting coefficient equations to an
injected homology space, as used in Proposition C.6. -/
noncomputable section
namespace Froberg
open Module
variable {K : Type*} [Field K]
variable {H V Z : Type*} [AddCommGroup H] [Module K H]
  [AddCommGroup V] [Module K V] [AddCommGroup Z] [Module K Z]
variable {r : ℕ}

/-- A kernel vector in an injected coefficient space gives one kernel
coefficient for each new generator. -/
def coefficientKernelMap (E : H →ₗ[K] (Fin r → V)) (C : V →ₗ[K] Z) :
    ((C.compLeft (Fin r)).comp E).ker →ₗ[K] (Fin r → C.ker) where
  toFun x i := ⟨E x.val i, congrFun x.property i⟩
  map_add' x y := by ext i; simp
  map_smul' a x := by ext i; simp

theorem coefficientKernelMap_injective (E : H →ₗ[K] (Fin r → V))
    (hE : Function.Injective E) (C : V →ₗ[K] Z) :
    Function.Injective (coefficientKernelMap E C) := by
  intro x y h
  apply Subtype.ext
  apply hE
  funext i
  exact congrArg Subtype.val (congrFun h i)

theorem coefficient_kernel_bound [FiniteDimensional K V]
    (E : H →ₗ[K] (Fin r → V)) (hE : Function.Injective E) (C : V →ₗ[K] Z) :
    finrank K ((C.compLeft (Fin r)).comp E).ker ≤ r * finrank K C.ker := by
  have h := LinearMap.finrank_le_finrank_of_injective (coefficientKernelMap_injective E hE C)
  simpa [Module.finrank_pi_fintype] using h

/-- The equations have at least `dim H - r*dim ker C` independent conditions. -/
theorem coefficient_rank_bound [FiniteDimensional K H] [FiniteDimensional K V]
    (E : H →ₗ[K] (Fin r → V)) (hE : Function.Injective E) (C : V →ₗ[K] Z) :
    finrank K H - r * finrank K C.ker ≤
      finrank K ((C.compLeft (Fin r)).comp E).range := by
  have hk := coefficient_kernel_bound E hE C
  have hd := ((C.compLeft (Fin r)).comp E).finrank_range_add_finrank_ker
  omega

end Froberg
