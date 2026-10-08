import Quartic.BilinearGeneric
import Quartic.BilinearImage

/-! Scalar families for any actual bilinear multiplication, with an explicit
strict-shadow criterion for generic injectivity. -/
noncomputable section
namespace Froberg.BilinearScalarFamily
open Module MvPolynomial Quartic.PolynomialBilinearCoordinates
variable {K F V W : Type*} [Field K]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
variable {q : ℕ}

/-- Coefficient tuples and scalar families share the literal sum of products. -/
def tupleBilinear (mu : F →ₗ[K] V →ₗ[K] W) :
    (Fin q → V) →ₗ[K] (Fin q → F) →ₗ[K] W where
  toFun := Quartic.BilinearImage.tupleMap mu
  map_add' x y := by
    apply LinearMap.ext
    intro f
    simp only [Quartic.BilinearImage.tupleMap_apply, Pi.add_apply, map_add,
      Finset.sum_add_distrib, LinearMap.add_apply]
  map_smul' c x := by
    apply LinearMap.ext
    intro f
    simp only [Quartic.BilinearImage.tupleMap_apply, Pi.smul_apply, map_smul,
      Finset.smul_sum, LinearMap.smul_apply, RingHom.id_apply]

/-- The actual multiplication map for an ordered scalar family. -/
def multiplication (mu : F →ₗ[K] V →ₗ[K] W) (Q : Fin q → F) :
    (Fin q → V) →ₗ[K] W := (tupleBilinear mu).flip Q

@[simp] theorem multiplication_apply (mu : F →ₗ[K] V →ₗ[K] W)
    (Q : Fin q → F) (x : Fin q → V) : multiplication mu Q x = ∑ i, mu (Q i) (x i) :=
  Quartic.BilinearImage.tupleMap_apply mu x Q

/-- The Grassmannian overhead is bounded by the smaller of dimension and codimension. -/
theorem grassmannian_overhead_le (a r : ℕ) : r*(a-r) ≤ a*min r (a-r) := by
  by_cases hra : r ≤ a
  · rcases le_total r (a-r) with hr | hr
    · rw [min_eq_left hr]
      nlinarith [Nat.sub_le a r]
    · rw [min_eq_right hr]
      nlinarith [Nat.sub_le a r]
  · simp [Nat.sub_eq_zero_of_le (by omega : a ≤ r)]

/-- A uniform actual image bound gives a nonempty principal scalar-parameter open. -/
theorem generic_injective_of_shadow [Infinite K]
    (mu : F →ₗ[K] V →ₗ[K] W)
    (hgrowth : ∀ L : Submodule K V,
      q*finrank K L + finrank K V*min (finrank K L) (finrank K V-finrank K L) ≤
        finrank K (Quartic.BilinearImage.image mu L)) :
    ∃ P : MvPolynomial (Fin (finrank K (Fin q → F))) K,
      (∃ Q : Fin q → F, eval (coordinates K _ Q) P ≠ 0) ∧
      ∀ Q : Fin q → F, eval (coordinates K _ Q) P ≠ 0 →
        Function.Injective (multiplication mu Q) := by
  apply Quartic.BilinearGeneric.generic_injective_actual (tupleBilinear mu)
  intro x _
  dsimp only
  change _ ≤ finrank K (Quartic.BilinearImage.tupleMap mu x).range
  rw [Quartic.BilinearImage.range_tupleMap]
  exact (Nat.add_le_add_right (grassmannian_overhead_le _ _) _).trans
    (by simpa only [Nat.add_comm] using hgrowth (Submodule.span K (Set.range x)))

/-- The manuscript's real-valued strict shadow implies the integer incidence budget. -/
theorem generic_injective_of_strict_shadow [Infinite K]
    (mu : F →ₗ[K] V →ₗ[K] W) (R D : ℝ) (hq : (q : ℝ) ≤ R)
    (hD : (finrank K V : ℝ) ≤ D)
    (hgrowth : ∀ L : Submodule K V,
      R*finrank K L + D*(min (finrank K L) (finrank K V-finrank K L) : ℕ) ≤
        finrank K (Quartic.BilinearImage.image mu L)) :
    ∃ P : MvPolynomial (Fin (finrank K (Fin q → F))) K,
      (∃ Q : Fin q → F, eval (coordinates K _ Q) P ≠ 0) ∧
      ∀ Q : Fin q → F, eval (coordinates K _ Q) P ≠ 0 →
        Function.Injective (multiplication mu Q) := by
  apply generic_injective_of_shadow mu
  intro L
  have hr := hgrowth L
  have h1 := mul_le_mul_of_nonneg_right hq (Nat.cast_nonneg (finrank K L) : (0 : ℝ) ≤ _)
  have h2 := mul_le_mul_of_nonneg_right hD
    (Nat.cast_nonneg (min (finrank K L) (finrank K V-finrank K L)) : (0 : ℝ) ≤ _)
  have hh := (add_le_add h1 h2).trans hr
  exact_mod_cast hh

/-- Every injective scalar-family map has the expected actual quotient dimension. -/
theorem quotient_finrank (mu : F →ₗ[K] V →ₗ[K] W) (Q : Fin q → F)
    (hQ : Function.Injective (multiplication mu Q)) :
    finrank K (W ⧸ (multiplication mu Q).range) = finrank K W-q*finrank K V := by
  have he := Submodule.finrank_quotient_add_finrank (multiplication mu Q).range
  rw [LinearMap.finrank_range_of_inj hQ, Module.finrank_pi_fintype] at he
  simpa using Nat.eq_sub_of_add_eq (by simpa using he)

/-- Injectivity also certifies that the scalar forms themselves are independent
as soon as the source contains a nonzero vector. -/
theorem independent_of_injective (mu : F →ₗ[K] V →ₗ[K] W) (Q : Fin q → F)
    (hQ : Function.Injective (multiplication mu Q)) (x : V) (hx : x ≠ 0) :
    LinearIndependent K Q := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  have hz : multiplication mu Q (fun j => c j • x) = 0 := by
    have hh := congrArg (fun f => mu f x) hc
    simpa only [multiplication_apply,map_sum,LinearMap.sum_apply,map_smul,
      LinearMap.smul_apply,map_zero,LinearMap.zero_apply] using hh
  have ht : (fun j => c j • x) = 0 := hQ (hz.trans (map_zero _).symm)
  exact (smul_eq_zero.mp (congrFun ht i)).resolve_right hx

end Froberg.BilinearScalarFamily
