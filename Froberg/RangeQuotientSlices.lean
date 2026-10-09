module

public import Froberg.QuotientSliceOpen

@[expose] public section

/-! Closed quotient slices for a polynomial family of actual linear maps,
and in particular for an affine replacement pencil. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace Froberg.BilinearScalarFamily
open Module MvPolynomial Quartic
variable {K F V W U I : Type*} [Field K] [IsAlgClosed K]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  [AddCommGroup U] [Module K U] [FiniteDimensional K U]

theorem quotient_range_slices_principal_open (mu : F →ₗ[K] V →ₗ[K] W)
    (A : (I → K) → (U →ₗ[K] W)) (hA : IsPolynomialFamily A)
    (s : ℕ → ℕ) (p₀ : I → K)
    (hzero : HasClosedKernelSlices (targetPostcompose mu (A p₀).range.mkQ) s) :
    ∃ P : MvPolynomial I K,eval p₀ P ≠ 0 ∧ ∀ p,eval p P ≠ 0 →
      HasClosedKernelSlices (targetPostcompose mu (A p).range.mkQ) s := by
  let b := Module.finBasis K U
  let B : (I → K) → Fin (finrank K U) → W := fun p i => A p (b i)
  have hB (i : Fin (finrank K U)) : IsPolynomialFamily (fun p => B p i) :=
    hA.linear_comp (LinearMap.applyₗ (R := K) (M₂ := W) (b i))
  have hr (p : I → K) : Submodule.span K (Set.range (B p))=(A p).range := by
    calc
      _ = (Submodule.span K (Set.range b)).map (A p) := by
        rw [Submodule.map_span,← Set.range_comp]
        rfl
      _ = _ := by rw [b.span_eq,Submodule.map_top]
  obtain ⟨P,hP,hgood⟩ := quotient_slices_principal_open mu B hB s p₀ (by rwa [hr])
  refine ⟨P,hP,?_⟩
  intro p hp
  have ht := hgood p hp
  rw [hr p] at ht
  exact ht

theorem quotient_pencil_slices_principal_open (mu : F →ₗ[K] V →ₗ[K] W)
    (A₀ A₁ : U →ₗ[K] W) (s : ℕ → ℕ)
    (hzero : HasClosedKernelSlices (targetPostcompose mu A₀.range.mkQ) s) :
    ∃ P : MvPolynomial (Fin 1) K,eval 0 P ≠ 0 ∧ ∀ e : K,
      eval (fun _ => e) P ≠ 0 →
      HasClosedKernelSlices (targetPostcompose mu (A₀+e • A₁).range.mkQ) s := by
  let A : (Fin 1 → K) → U →ₗ[K] W := fun p => A₀+p 0 • A₁
  have hA : IsPolynomialFamily A := (isPolynomialFamily_const A₀).add
    ((isPolynomialFamily_linear (LinearMap.proj (0 : Fin 1))).smul (isPolynomialFamily_const A₁))
  obtain ⟨P,hP,hgood⟩ := quotient_range_slices_principal_open mu A hA s 0 (by
    change HasClosedKernelSlices (targetPostcompose mu (A₀+(0 : K) • A₁).range.mkQ) s
    rw [zero_smul,add_zero]
    exact hzero)
  exact ⟨P,hP,fun e he => hgood (fun _ => e) he⟩

end Froberg.BilinearScalarFamily
