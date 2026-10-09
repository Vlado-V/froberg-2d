module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Tactic

@[expose] public section

/-! The actual relative odd injection and the ambient relation loss give
the target dimension term in the layered covector budget. -/
noncomputable section
namespace Froberg
open Module
variable {K A W W₀ H V : Type} [Field K]
  [AddCommGroup A] [Module K A] [FiniteDimensional K A]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  [AddCommGroup W₀] [Module K W₀] [FiniteDimensional K W₀]
  [AddCommGroup H] [Module K H] [FiniteDimensional K H]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {q j loss : ℕ}

theorem layered_target_dimension (e : A ≃ₗ[K] W₀ × H)
    (hambient : finrank K A ≤ finrank K W+loss)
    (f : (Fin q → V) →ₗ[K] W) (hf : Function.Injective f)
    (hj : finrank K (W ⧸ f.range)=j) :
    finrank K W₀+finrank K H ≤ j+q*finrank K V+loss := by
  have he : finrank K A=finrank K W₀+finrank K H := by
    rw [e.finrank_eq,Module.finrank_prod]
  have hr : finrank K f.range=q*finrank K V := by
    rw [LinearMap.finrank_range_of_inj hf,Module.finrank_pi_fintype]
    simp
  have hq := Submodule.finrank_quotient_add_finrank f.range
  rw [hj,hr] at hq
  omega

theorem ambient_dimension_of_kernel_bound (pi : A →ₗ[K] W)
    (hpi : Function.Surjective pi) (hloss : finrank K pi.ker ≤ loss) :
    finrank K A ≤ finrank K W+loss := by
  have h := pi.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hpi,finrank_top] at h
  omega

end Froberg
