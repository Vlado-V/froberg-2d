import Quartic.PolynomialBilinearCoordinates
import Quartic.ProjectiveKernelIncidence

/-!
# Generic injectivity for actual finite-dimensional bilinear families

The parameter and target spaces may be any finite-dimensional vector spaces.
The only substantive hypothesis is the dimension of the actual image imposed
by every nonzero relation tuple. The conclusion is a nonempty principal open
in basis coordinates of the parameter space.
-/

noncomputable section
namespace Quartic.BilinearGeneric
open Module MvPolynomial PolynomialBilinearCoordinates
set_option backward.isDefEq.respectTransparency false

variable {K U V W : Type*} [Field K]
variable [AddCommGroup U] [Module K U] [FiniteDimensional K U]
variable [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable [AddCommGroup W] [Module K W] [FiniteDimensional K W]
variable {q : ℕ}

/-- A relation tuple of span dimension d must impose at least d(a-d)+qd
independent equations. This gives generic injectivity in actual spaces. -/
theorem generic_injective [Infinite K]
    (B : (Fin q → U) →ₗ[K] V →ₗ[K] W)
    (hbound : ∀ F : Fin q → U, F ≠ 0 →
      let d := finrank K (Submodule.span K (Set.range F))
      d * (finrank K U - d) + q * d ≤ finrank K (LinearMap.range (B F))) :
    ∃ P : MvPolynomial (Fin (finrank K V)) K,
      (∃ x : Fin (finrank K V) → K, eval x P ≠ 0) ∧
      ∀ x, eval x P ≠ 0 →
        Function.Injective (B.flip ((coordinates K V).symm x)) := by
  have hcoordinate : ∀ F : Fin q → Fin (finrank K U) → K, F ≠ 0 →
      let d := finrank K (ProjectiveKernelIncidence.tupleSpan F)
      d * (finrank K U - d) + q * d ≤
        finrank K (LinearMap.range (tupleCoordinate B F)) := by
    intro F hF
    have h := hbound (tupleDecode K U q F) (tupleDecode_ne_zero_iff F |>.mpr hF)
    dsimp only at h ⊢
    rw [finrank_range_tupleCoordinate]
    simpa only [ProjectiveKernelIncidence.tupleSpan, finrank_span_tupleDecode] using h
  obtain ⟨P, hP, hgood⟩ := ProjectiveKernelIncidence.generic_injective
    (tupleCoordinate B) hcoordinate
  refine ⟨P, hP, fun x hx => ?_⟩
  exact (injective_flip_tupleCoordinate_iff B x).mp (hgood x hx)

/-- The same nonempty principal open, with its good points expressed in the
actual parameter space rather than the decoded coordinate space. -/
theorem generic_injective_actual [Infinite K]
    (B : (Fin q → U) →ₗ[K] V →ₗ[K] W)
    (hbound : ∀ F : Fin q → U, F ≠ 0 →
      let d := finrank K (Submodule.span K (Set.range F))
      d * (finrank K U - d) + q * d ≤ finrank K (LinearMap.range (B F))) :
    ∃ P : MvPolynomial (Fin (finrank K V)) K,
      (∃ v : V, eval (coordinates K V v) P ≠ 0) ∧
      ∀ v : V, eval (coordinates K V v) P ≠ 0 → Function.Injective (B.flip v) := by
  obtain ⟨P, ⟨x, hx⟩, hgood⟩ := generic_injective B hbound
  refine ⟨P, ⟨(coordinates K V).symm x, ?_⟩, ?_⟩
  · simpa only [LinearEquiv.apply_symm_apply] using hx
  · intro v hv
    simpa only [LinearEquiv.symm_apply_apply] using hgood (coordinates K V v) hv

/-- In particular, the numerical image bounds produce an actual injective witness. -/
theorem exists_injective [Infinite K]
    (B : (Fin q → U) →ₗ[K] V →ₗ[K] W)
    (hbound : ∀ F : Fin q → U, F ≠ 0 →
      let d := finrank K (Submodule.span K (Set.range F))
      d * (finrank K U - d) + q * d ≤ finrank K (LinearMap.range (B F))) :
    ∃ v : V, Function.Injective (B.flip v) := by
  obtain ⟨P, ⟨v, hv⟩, hgood⟩ := generic_injective_actual B hbound
  exact ⟨v, hgood v hv⟩

end Quartic.BilinearGeneric
