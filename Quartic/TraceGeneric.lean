import Quartic.SplitMiddle31
import Quartic.RankOpen

/-!
# A nonempty coefficient open for the actual (3,1) trace

All mixed generators are parametrized by their homogeneous monomial
coefficients. Their multiplication map is linear in those parameters. The
separated witness supplies a determinant condition preserving both generator
independence and injectivity of mixed multiplication. The already proved
trace injection and uniform quotient rank bound then hold on that same open.
-/
noncomputable section
namespace Quartic.TraceGeneric
open Module MvPolynomial SplitMiddle31
variable {K : Type*} [Field K] {m c : ℕ}

/-- Actual coefficients of the ordered mixed generators, by generator,
child variable, and degree-one monomial in the three new variables. -/
abbrev CoefficientIndex (m c : ℕ) := Fin c × Fin m × Sym (Fin 3) 1

/-- Monomial coordinates parametrize every actual mixed coefficient family. -/
def decode : (CoefficientIndex m c → K) ≃ₗ[K] Mixed K m c where
  toFun a j l := (formsBasis K 3 1).equivFun.symm (fun b => a (j, l, b))
  invFun g s := (formsBasis K 3 1).equivFun (g s.1 s.2.1) s.2.2
  left_inv a := by
    funext s
    exact congrFun ((formsBasis K 3 1).equivFun.apply_symm_apply
      (fun b => a (s.1, s.2.1, b))) s.2.2
  right_inv g := by
    funext j l
    exact (formsBasis K 3 1).equivFun.symm_apply_apply (g j l)
  map_add' a b := by
    funext j l
    exact (formsBasis K 3 1).equivFun.symm.map_add _ _
  map_smul' s a := by
    funext j l
    exact (formsBasis K 3 1).equivFun.symm.map_smul s _

/-- Actual quadratic-coefficient multiplication varies linearly with the mixed
generators themselves. -/
def mixedMultiplicationLinear : Mixed K m c →ₗ[K]
    ((Fin c → Forms K 3 2) →ₗ[K] Target K m) where
  toFun := mixedMultiplication
  map_add' g h := by
    apply LinearMap.ext
    intro a
    funext l
    apply Subtype.ext
    simp [mixedMultiplication, mul_add, Finset.sum_add_distrib]
  map_smul' s g := by
    apply LinearMap.ext
    intro a
    funext l
    apply Subtype.ext
    simp [mixedMultiplication, ← Finset.smul_sum]

/-- The linear parameter family retains the actual polynomial multiplication. -/
def coordinateMap : (CoefficientIndex m c → K) →ₗ[K]
    ((Fin c → Forms K 3 2) →ₗ[K] Target K m) :=
  mixedMultiplicationLinear.comp decode.toLinearMap

@[simp] theorem coordinateMap_apply (a : CoefficientIndex m c → K) :
    coordinateMap a = mixedMultiplication (decode a) := rfl

/-- The full actual trace properties, including every further quotient of the
four coefficient coordinates. -/
def TraceProperties (g : Mixed K m c) : Prop :=
  LinearIndependent K g ∧ Function.Injective (mixedMultiplication g) ∧
    Function.Injective (trace g) ∧
    ∀ D : Submodule K ((Fin m → Forms K 3 1) ⧸ mixedSpace g),
      2 * m + 2 * c ≤ finrank K (LinearMap.range (traceModulo g D)) + 4 * finrank K D

/-- A concrete nonempty determinant open, nonvanishing at the coordinates of
`g_j = x y_j`, on which independence and every trace conclusion hold. -/
theorem trace_principal_open (hcm : c ≤ m) :
    ∃ P : MvPolynomial (CoefficientIndex m c) K,
      eval (decode.symm (separatedMixed (K := K) hcm)) P ≠ 0 ∧
      ∀ a, eval a P ≠ 0 → TraceProperties (decode a) := by
  classical
  let g₀ : Mixed K m c := separatedMixed hcm
  let a₀ : CoefficientIndex m c → K := decode.symm g₀
  let G : Fin c → (CoefficientIndex m c → K) →ₗ[K] (Fin m → Forms K 3 1) :=
    fun j => (LinearMap.proj j).comp decode.toLinearMap
  have hg₀ : LinearIndependent K (fun j => G j a₀) := by
    simpa [G, a₀, g₀] using separatedMixed_independent (K := K) hcm
  obtain ⟨Pg, hPg, hopenG⟩ := independent_principal_open G a₀ hg₀
  obtain ⟨Pr, hPr, hopenR⟩ := rank_principal_open
    (coordinateMap (K := K) (m := m) (c := c)) a₀
  have hinj₀ : Function.Injective (coordinateMap a₀) := by
    simpa [coordinateMap_apply, a₀, g₀] using separatedMixed_injective (K := K) hcm
  refine ⟨Pg * Pr, ?_, ?_⟩
  · change eval a₀ (Pg * Pr) ≠ 0
    rw [map_mul]
    exact mul_ne_zero hPg hPr
  · intro a ha
    have hparts : eval a Pg ≠ 0 ∧ eval a Pr ≠ 0 := by
      simpa only [map_mul, mul_ne_zero_iff] using ha
    have hinj : Function.Injective (mixedMultiplication (decode a)) := by
      have hr := hopenR a hparts.2
      rw [LinearMap.finrank_range_of_inj hinj₀] at hr
      have hk := LinearMap.finrank_range_add_finrank_ker (coordinateMap a)
      simp only [coordinateMap_apply] at hr hk
      apply LinearMap.ker_eq_bot.mp
      apply Submodule.finrank_eq_zero.mp
      apply Nat.eq_zero_of_le_zero
      apply Nat.le_of_add_le_add_left
      exact hk.le.trans hr
    exact ⟨by simpa [G] using hopenG a hparts.1, hinj,
      trace_injective _ hinj, fun D => traceModulo_rank_bound _ hinj D⟩

/-- Generic trace injectivity means a nonempty principal open of the actual
mixed coefficient space, rather than an assumed genericity predicate. -/
def GenericTrace (K : Type*) [Field K] (m c : ℕ) : Prop :=
  ∃ P : MvPolynomial (CoefficientIndex m c) K,
    (∃ a₀, eval a₀ P ≠ 0) ∧ ∀ a, eval a P ≠ 0 → TraceProperties (decode a)

/-- The complete actual (3,1) trace and its quotient rank-loss estimate hold
on a nonempty coefficient open for every `c ≤ m`. -/
theorem generic_trace (hcm : c ≤ m) : GenericTrace K m c := by
  obtain ⟨P, hP, hgood⟩ := trace_principal_open (K := K) hcm
  exact ⟨P, ⟨decode.symm (separatedMixed hcm), hP⟩, hgood⟩

end Quartic.TraceGeneric
