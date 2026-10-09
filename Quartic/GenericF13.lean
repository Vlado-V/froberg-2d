module

public import Quartic.GeneralF13
public import Quartic.PolynomialRankOpen

@[expose] public section

/-! # Actual F₁₃ injectivity persists on a coefficient principal open -/
noncomputable section
namespace Quartic.GenericF13
set_option maxHeartbeats 800000
open Module MvPolynomial GeneralF13 MiddleCoordinates
variable {K : Type*} [Field K] {m c q : ℕ}

/-- The actual mixed polynomial multiplication is linear in its full coefficient family. -/
def multiplicationFamily : GeneralF13.Mixed K m c →ₗ[K]
    CoefficientSource K m c →ₗ[K] GeneralF13.Ambient K m where
  toFun := GeneralF13.multiplication
  map_add' E F := by
    apply LinearMap.ext
    intro u
    funext r
    simp only [GeneralF13.multiplication, LinearMap.coe_mk, AddHom.coe_mk,
      Pi.add_apply, map_add, LinearMap.add_apply, Finset.sum_add_distrib]
  map_smul' s E := by
    apply LinearMap.ext
    intro u
    funext r
    simp only [GeneralF13.multiplication, LinearMap.coe_mk, AddHom.coe_mk,
      Pi.smul_apply, map_smul, LinearMap.smul_apply, Finset.smul_sum, RingHom.id_apply]

/-- The shared child cubic multiplication is linear in the original quadrics. -/
def childFamily : Quadrics K m q →ₗ[K]
    CubicSource K m q →ₗ[K] GeneralF13.Ambient K m where
  toFun := childMultiplication
  map_add' Q R := by
    apply LinearMap.ext
    intro v
    funext r
    change CubicGeneric.bilinear.flip (Q+R) (fun j => v j r) = _
    exact LinearMap.congr_fun (CubicGeneric.bilinear.flip.map_add Q R) (fun j => v j r)
  map_smul' s Q := by
    apply LinearMap.ext
    intro v
    funext r
    change CubicGeneric.bilinear.flip (s • Q) (fun j => v j r) = _
    exact LinearMap.congr_fun (CubicGeneric.bilinear.flip.map_smul s Q) (fun j => v j r)

/-- One fixed-space linear map family in all mixed and child coefficients. -/
def combinedFamily : MiddleCoordinates.Parameters K m c q →ₗ[K]
    (CoefficientSource K m c × CubicSource K m q) →ₗ[K] GeneralF13.Ambient K m where
  toFun p := GeneralF13.combined p.1 p.2
  map_add' p z := by
    apply LinearMap.ext
    intro u
    change multiplicationFamily (p.1+z.1) u.1 + childFamily (p.2+z.2) u.2 = _
    simp only [map_add, LinearMap.add_apply]
    change _ = (multiplicationFamily p.1 u.1 + childFamily p.2 u.2) +
      (multiplicationFamily z.1 u.1 + childFamily z.2 u.2)
    abel
  map_smul' s p := by
    apply LinearMap.ext
    intro u
    change multiplicationFamily (s • p.1) u.1 + childFamily (s • p.2) u.2 = _
    simp only [map_smul, LinearMap.smul_apply]
    exact (smul_add s _ _).symm

/-- The exact monomial-coordinate family used by the determinant-open theorem. -/
def coordinateCombined : (MiddleCoordinates.CoefficientIndex m c q → K) →ₗ[K]
    (CoefficientSource K m c × CubicSource K m q) →ₗ[K] GeneralF13.Ambient K m :=
  combinedFamily.comp MiddleCoordinates.decode.toLinearMap

@[simp] theorem coordinateCombined_apply (a : MiddleCoordinates.CoefficientIndex m c q → K) :
    coordinateCombined a = GeneralF13.combined (MiddleCoordinates.decode a).1
      (MiddleCoordinates.decode a).2 := rfl

/-- Read the original child tuple from the full coefficient family. -/
def coordinateChild : (MiddleCoordinates.CoefficientIndex m c q → K) →ₗ[K] Quadrics K m q :=
  (LinearMap.snd K _ _).comp MiddleCoordinates.decode.toLinearMap

/-- All three concrete hypotheses needed for the varying-presentation F₁₃ theorem. -/
def Conditions (E : GeneralF13.Mixed K m c) (Q : Quadrics K m q) : Prop :=
  LinearIndependent K Q ∧ Function.Injective (CubicGeneric.cubicMap Q) ∧
    Function.Injective (GeneralF13.f13Map E Q)

/-- Every actual witness yields a principal open in all original E,Q coefficients.
No openness property of quotient families is assumed. -/
theorem principal_open_of_witness (E : GeneralF13.Mixed K m c) (Q : Quadrics K m q)
    (hQ : LinearIndependent K Q) (hC : Function.Injective (CubicGeneric.cubicMap Q))
    (hF : Function.Injective (GeneralF13.f13Map E Q)) :
    ∃ D : MvPolynomial (MiddleCoordinates.CoefficientIndex m c q) K,
      eval (MiddleCoordinates.decode.symm (E,Q)) D ≠ 0 ∧
      ∀ a, eval a D ≠ 0 → Conditions (MiddleCoordinates.decode a).1 (MiddleCoordinates.decode a).2 := by
  classical
  let a₀ := MiddleCoordinates.decode.symm (E,Q)
  have hp : IsPolynomialFamily (fun a : MiddleCoordinates.CoefficientIndex m c q → K =>
      GeneralF13.combined (MiddleCoordinates.decode a).1 (MiddleCoordinates.decode a).2) := by
    intro ell
    exact ⟨polynomialOfLinear (ell.comp coordinateCombined),
      fun a => eval_polynomialOfLinear _ a⟩
  obtain ⟨Dr,hDr,hr⟩ := rank_polynomial_principal_open
    (fun a : MiddleCoordinates.CoefficientIndex m c q → K =>
      GeneralF13.combined (MiddleCoordinates.decode a).1 (MiddleCoordinates.decode a).2) hp a₀
  have hc0 : Function.Injective (CubicGeneric.bilinear.flip (coordinateChild a₀)) := by
    simpa [CubicGeneric.cubicMap, coordinateChild, a₀] using hC
  have hpc : IsPolynomialFamily (fun a : MiddleCoordinates.CoefficientIndex m c q → K =>
      CubicGeneric.bilinear.flip (coordinateChild a)) := by
    intro ell
    exact ⟨polynomialOfLinear (ell.comp ((CubicGeneric.bilinear (K := K) (m := m) (q := q)).flip.comp
      (coordinateChild (K := K) (m := m) (c := c) (q := q)))), fun a => eval_polynomialOfLinear _ a⟩
  obtain ⟨Dc,hDc,hc⟩ := injective_polynomial_principal_open
    (fun a => CubicGeneric.bilinear.flip (coordinateChild a)) hpc a₀ hc0
  have hqpoly (j : Fin q) : IsPolynomialFamily
      (fun a : MiddleCoordinates.CoefficientIndex m c q → K => coordinateChild a j) := by
    intro ell
    exact ⟨polynomialOfLinear (ell.comp ((LinearMap.proj j).comp
      (coordinateChild (K := K) (m := m) (c := c) (q := q)))), fun a => eval_polynomialOfLinear _ a⟩
  have hq0 : LinearIndependent K (fun j => coordinateChild a₀ j) := by
    simpa only [coordinateChild, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, LinearMap.snd_apply, a₀] using hQ
  obtain ⟨Dq,hDq,hq⟩ := independent_polynomial_principal_open
    (fun j a => coordinateChild a j) hqpoly a₀ hq0
  refine ⟨Dq*Dc*Dr, ?_, ?_⟩
  · rw [map_mul, map_mul]
    exact mul_ne_zero (mul_ne_zero hDq hDc) hDr
  · intro a ha
    rw [map_mul, map_mul, mul_ne_zero_iff, mul_ne_zero_iff] at ha
    have hqa := hq a ha.1.1
    have hca := hc a ha.1.2
    have hra := hr a ha.2
    change LinearIndependent K (MiddleCoordinates.decode a).2 at hqa
    change Function.Injective (CubicGeneric.cubicMap (MiddleCoordinates.decode a).2) at hca
    refine ⟨hqa,hca, (GeneralF13.injective_iff_combined_rank _ _ hqa hca).mpr ?_⟩
    have hbase := (GeneralF13.injective_iff_combined_rank E Q hQ hC).mp hF
    have he : MiddleCoordinates.decode a₀ = (E,Q) := LinearEquiv.apply_symm_apply _ _
    rw [he] at hra
    exact hbase.trans hra

end Quartic.GenericF13
