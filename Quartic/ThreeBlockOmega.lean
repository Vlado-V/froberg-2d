module

public import Quartic.HomologyCoordinates

@[expose] public section

/-! The scalar contraction of the three-variable block over arbitrary
characteristic. The parameter avoids precisely the two exceptional scalars. -/
noncomputable section
namespace Quartic.ThreeBlockOmega
open MvPolynomial ThreeBlock HomologyCoordinates ThreeBlockQuotient
variable {K : Type*}
section Ring
variable [CommRing K]

def ell (ω : K) (p : Fin 2 → K) : K := p 0 + ω * p 1

def marked (ω : K) : Fin 2 → K := ![ω, -1]

def scalarCoefficients (ω : K) (t : Fin 3 → K) : Fin 4 → K :=
  fun i => ell ω (coefficientMaps t i)

@[simp] theorem ell_marked (ω : K) : ell ω (marked ω) = 0 := by
  simp [ell, marked]

theorem ell_kernel (ω : K) (p : Fin 2 → K) :
    ell ω p = 0 ↔ ∃ a : K, p = a • marked ω := by
  constructor
  · intro h
    refine ⟨-p 1, ?_⟩
    funext i
    fin_cases i
    · have hp : p 0 = -(ω * p 1) := eq_neg_of_add_eq_zero_left h
      simpa [marked, mul_comm] using hp
    · simp [marked]
  · rintro ⟨a, rfl⟩
    simp [ell, marked]
    ring

theorem scalarCoefficients_formula (ω : K) (t : Fin 3 → K) :
    scalarCoefficients ω t = ![-(1 + ω) * t 0, ω * t 1, t 2, 0] := by
  funext i
  fin_cases i <;> simp [scalarCoefficients, coefficientMaps, ell]
  ring

theorem scalar_minor_det (ω : K) :
    Matrix.det (!![-(1 + ω), 0, 0; 0, ω, 0; 0, 0, 1] :
      Matrix (Fin 3) (Fin 3) K) = -ω * (1 + ω) := by
  simp [Matrix.det_fin_three]
  ring

theorem scalarCoefficients_injective [NoZeroDivisors K] (ω : K)
    (hω : ω ≠ 0) (hω1 : ω ≠ -1) :
    Function.Injective (scalarCoefficients ω) := by
  have hsum : 1 + ω ≠ 0 := by
    intro h
    exact hω1 (eq_neg_of_add_eq_zero_right h)
  intro a b h
  rw [scalarCoefficients_formula, scalarCoefficients_formula] at h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] at h0 h1 h2
  funext i
  fin_cases i
  · exact mul_left_cancel₀ (neg_ne_zero.mpr hsum) h0
  · exact mul_left_cancel₀ hω h1
  · exact h2

end Ring

section Field
variable [Field K]

/-- Every infinite field contains a usable scalar, including in characteristic two. -/
theorem exists_parameter [Infinite K] : ∃ ω : K, ω ≠ 0 ∧ ω ≠ -1 := by
  classical
  obtain ⟨ω, hω⟩ := Infinite.exists_notMem_finset ({0, -1} : Finset K)
  refine ⟨ω, ?_⟩
  simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hω

def markedFunctional (ω : K) : PureQuotient K →ₗ[K] K :=
  ((LinearMap.fst K K K) + ω • (LinearMap.snd K K K)).comp quotientEquiv.toLinearMap

def scalarCoefficientMap (ω : K) : BlockHomology K →ₗ[K] (Fin 4 → K) :=
  LinearMap.pi (fun i => ((LinearMap.fst K K K) + ω • (LinearMap.snd K K K)).comp
    ((LinearMap.proj i).comp homologyReduction))

theorem scalarCoefficientMap_is_marked (ω : K) (ξ : BlockHomology K) (i : Fin 4) :
    scalarCoefficientMap ω ξ i = markedFunctional ω (coefficientMap i ξ) := by
  simp [scalarCoefficientMap, markedFunctional, coefficientMap]

theorem scalarCoefficientMap_coordinates (ω : K) (t : Fin 3 → K) :
    scalarCoefficientMap ω (homologyEquiv t) = scalarCoefficients ω t := by
  funext i
  change (homologyReduction (cycleClasses t) i).1 +
    ω * (homologyReduction (cycleClasses t) i).2 = _
  rw [homologyReduction_cycleClasses]
  rfl

theorem scalarCoefficientMap_injective (ω : K) (hω : ω ≠ 0) (hω1 : ω ≠ -1) :
    Function.Injective (scalarCoefficientMap ω) := by
  intro a b hab
  obtain ⟨s, rfl⟩ := homologyEquiv.surjective a
  obtain ⟨t, rfl⟩ := homologyEquiv.surjective b
  rw [scalarCoefficientMap_coordinates, scalarCoefficientMap_coordinates] at hab
  exact congrArg homologyEquiv (scalarCoefficients_injective ω hω hω1 hab)

end Field
end Quartic.ThreeBlockOmega
