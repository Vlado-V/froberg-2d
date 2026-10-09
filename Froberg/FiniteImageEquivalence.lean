module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

/-! # Equal-dimensional image containment produces the actual isomorphism -/

noncomputable section
namespace Froberg
open Module

variable {K M N V : Type*} [Field K]
    [AddCommMonoid M] [Module K M] [Module.Finite K M]
    [AddCommMonoid N] [Module K N] [Module.Finite K N]
    [AddCommMonoid V] [Module K V]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
theorem exists_linearEquiv_of_equal_dimension_range (F : M →ₗ[K] V) (J : N →ₗ[K] V)
    (hJ : Function.Injective J) (himage : LinearMap.range J ≤ LinearMap.range F)
    (hdim : finrank K M = finrank K N) :
    ∃ E : M ≃ₗ[K] N, ∀ x, J (E x) = F x := by
  letI : AddCommGroup M := Module.addCommMonoidToAddCommGroup K
  letI : AddCommGroup N := Module.addCommMonoidToAddCommGroup K
  letI : AddCommGroup V := Module.addCommMonoidToAddCommGroup K
  have hdJ := LinearMap.finrank_range_of_inj hJ
  have hle := Submodule.finrank_mono himage
  have heqDim : finrank K (LinearMap.range J) = finrank K (LinearMap.range F) := by
    apply Nat.le_antisymm hle
    calc
      finrank K (LinearMap.range F) ≤ finrank K M := F.finrank_range_le
      _ = finrank K N := hdim
      _ = finrank K (LinearMap.range J) := hdJ.symm
  have heq : LinearMap.range J = LinearMap.range F :=
    Submodule.eq_of_le_of_finrank_eq himage heqDim
  let F' : M →ₗ[K] LinearMap.range J := F.codRestrict (LinearMap.range J) (fun x => by
    rw [heq]
    exact F.mem_range_self x)
  have hF' : Function.Surjective F' := by
    intro y
    have hy : y.val ∈ LinearMap.range F := by rw [← heq]; exact y.property
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩
  let L : M →ₗ[K] N := (LinearEquiv.ofInjective J hJ).symm.toLinearMap.comp F'
  have hLsurj : Function.Surjective L := (LinearEquiv.ofInjective J hJ).symm.surjective.comp hF'
  have hLinj : Function.Injective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hLsurj
  refine ⟨LinearEquiv.ofBijective L ⟨hLinj, hLsurj⟩, ?_⟩
  intro x
  change J ((LinearEquiv.ofInjective J hJ).symm (F' x)) = F x
  simp only [LinearEquiv.ofInjective_symm_apply]
  rfl

end Froberg
