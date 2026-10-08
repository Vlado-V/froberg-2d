import Froberg.PolynomialComplexOpen
import Froberg.RangeQuotientSlices
import Froberg.ReplacementParameter

/-! The exact odd complex and every closed scalar-contraction threshold
survive one common nonzero replacement. Any further principal open through
zero, such as generator independence or even-target surjectivity, can be
included in the same choice. -/
noncomputable section
namespace Froberg
open MvPolynomial Quartic BilinearScalarFamily
variable {K F V W U B : Type*} [Field K] [Infinite K] [IsAlgClosed K]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  [AddCommGroup U] [Module K U] [FiniteDimensional K U]
  [AddCommGroup B] [Module K B] [FiniteDimensional K B]

theorem exists_replacement_preserving_exactness_and_slices
    (mu : F →ₗ[K] V →ₗ[K] W) (A₀ A₁ : U →ₗ[K] W) (B₀ B₁ : B →ₗ[K] U)
    (hcomplex : ∀ e : K,(A₀+e • A₁).comp (B₀+e • B₁)=0)
    (hexact : A₀.ker=B₀.range) (s : ℕ → ℕ)
    (hslices : HasClosedKernelSlices (targetPostcompose mu A₀.range.mkQ) s)
    (P : MvPolynomial (Fin 1) K) (hP : eval 0 P ≠ 0) :
    ∃ e : K,e ≠ 0 ∧ eval (fun _ => e) P ≠ 0 ∧
      (A₀+e • A₁).ker=(B₀+e • B₁).range ∧
      HasClosedKernelSlices (targetPostcompose mu (A₀+e • A₁).range.mkQ) s := by
  obtain ⟨E,hE,he⟩ := complex_pencil_exact_principal_open A₀ A₁ B₀ B₁ hcomplex hexact
  obtain ⟨S,hS,hs⟩ := quotient_pencil_slices_principal_open mu A₀ A₁ s hslices
  obtain ⟨e,hne,hgood⟩ := exists_nonzero_replacement_fin (P*(E*S))
    (by simpa only [map_mul] using mul_ne_zero hP (mul_ne_zero hE hS))
  have hgood' : eval (fun _ => e) P ≠ 0 ∧
      eval (fun _ => e) E ≠ 0 ∧ eval (fun _ => e) S ≠ 0 := by
    simpa only [map_mul,mul_ne_zero_iff] using hgood
  exact ⟨e,hne,hgood'.1,he e hgood'.2.1,hs e hgood'.2.2⟩

end Froberg
