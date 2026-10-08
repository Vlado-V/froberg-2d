import Quartic.SimultaneousMiddle
import Quartic.TraceGeneric

/-!
# Simultaneous middle, augmented, and trace conditions on the same coefficients

The trace coordinates group the mixed coefficients by child variable; the
middle coordinates group them by pure variable. Their degree-one monomial
indices are explicitly transposed using `Sym.oneEquiv`. The three nonempty
principal opens therefore intersect in one full coefficient space. This does
not assert an assembled split complex or any endpoint/incidence condition.
-/
noncomputable section
namespace Quartic.SimultaneousBlockConditions
open MvPolynomial AugmentedGeneric SimultaneousMiddle
set_option maxHeartbeats 400000
variable {K : Type*} [Field K] {m c q : ℕ}

/-- Exchange the pure and child degree-one monomial positions. -/
def mixedIndexEquiv : TraceGeneric.CoefficientIndex m c ≃
    (Fin c × Fin 3 × Sym (Fin m) 1) where
  toFun s := (s.1, (Sym.oneEquiv (α := Fin 3)).symm s.2.2, Sym.oneEquiv (α := Fin m) s.2.1)
  invFun s := (s.1, (Sym.oneEquiv (α := Fin m)).symm s.2.2, Sym.oneEquiv (α := Fin 3) s.2.1)
  left_inv s := by rcases s with ⟨j, l, b⟩; simp only [Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  right_inv s := by rcases s with ⟨j, i, b⟩; simp only [Equiv.symm_apply_apply, Equiv.apply_symm_apply]

/-- Embed every trace coefficient into the full mixed/child/motion parameter space. -/
def traceIndex : TraceGeneric.CoefficientIndex m c → ParameterIndex m c q :=
  fun s => Sum.inl (Sum.inl (mixedIndexEquiv s))

theorem traceIndex_injective : Function.Injective (traceIndex (m := m) (c := c) (q := q)) := by
  intro a b h
  exact mixedIndexEquiv.injective (Sum.inl.inj (Sum.inl.inj h))

def traceCoefficients (a : ParameterIndex m c q → K) : TraceGeneric.CoefficientIndex m c → K :=
  fun s => a (traceIndex s)

/-- A trace point extends with zero child generators and zero pure motions. -/
def traceExtension (a : TraceGeneric.CoefficientIndex m c → K) : ParameterIndex m c q → K :=
  Sum.elim (Sum.elim (fun s => a (mixedIndexEquiv.symm s)) (fun _ => 0)) (fun _ => 0)

@[simp] theorem traceCoefficients_extension (a : TraceGeneric.CoefficientIndex m c → K) :
    traceCoefficients (traceExtension (q := q) a) = a := by
  funext s
  simp [traceCoefficients, traceExtension, traceIndex]

/-- The actual mixed family in the trace's child-first polynomial coordinates. -/
def traceFamily (a : ParameterIndex m c q → K) : SplitMiddle31.Mixed K m c :=
  TraceGeneric.decode (traceCoefficients a)

/-- Explicit transposition of actual homogeneous linear-form coefficients. -/
def transposeMixed (g : Fin c → MiddleCoordinates.Mixed K m) : SplitMiddle31.Mixed K m c :=
  TraceGeneric.decode (fun s => (formsBasis K m 1).equivFun
    (g s.1 ((Sym.oneEquiv (α := Fin 3)).symm s.2.2)) (Sym.oneEquiv (α := Fin m) s.2.1))

theorem middleCoefficient (a : ParameterIndex m c q → K) (j : Fin c) (i : Fin 3)
    (b : Sym (Fin m) 1) :
    (formsBasis K m 1).equivFun (coefficientMixed a j i) b = a (Sum.inl (Sum.inl (j, i, b))) := by
  change (formsBasis K m 1).equivFun ((formsBasis K m 1).equivFun.symm
    (fun s => a (Sum.inl (Sum.inl (j, i, s))))) b = _
  exact congrFun (LinearEquiv.apply_symm_apply _ _) b

/-- The trace family is exactly the transposition of the same actual mixed generators. -/
theorem traceFamily_eq_transpose (a : ParameterIndex m c q → K) :
    traceFamily a = transposeMixed (coefficientMixed a) := by
  apply congrArg TraceGeneric.decode
  funext s
  exact (middleCoefficient a s.1 ((Sym.oneEquiv (α := Fin 3)).symm s.2.2)
    (Sym.oneEquiv (α := Fin m) s.2.1)).symm

/-- The equality reads actual degree-one polynomial coefficients in both orientations. -/
theorem transposed_coefficients (a : ParameterIndex m c q → K)
    (j : Fin c) (l : Fin m) (i : Fin 3) :
    (formsBasis K 3 1).equivFun (traceFamily a j l) (Sym.oneEquiv (α := Fin 3) i) =
      (formsBasis K m 1).equivFun (coefficientMixed a j i) (Sym.oneEquiv (α := Fin m) l) := by
  change (formsBasis K 3 1).equivFun ((formsBasis K 3 1).equivFun.symm
    (fun b => traceCoefficients a (j, l, b))) (Sym.oneEquiv (α := Fin 3) i) = _
  rw [LinearEquiv.apply_symm_apply, middleCoefficient]
  change a (Sum.inl (Sum.inl (j, (Sym.oneEquiv (α := Fin 3)).symm
    (Sym.oneEquiv i), Sym.oneEquiv l))) = _
  rw [Equiv.symm_apply_apply]

/-- Rename the trace determinant into the shared full coefficient space. -/
def tracePullback (P : MvPolynomial (TraceGeneric.CoefficientIndex m c) K) :
    MvPolynomial (ParameterIndex m c q) K := MvPolynomial.rename traceIndex P

@[simp] theorem eval_tracePullback (a : ParameterIndex m c q → K)
    (P : MvPolynomial (TraceGeneric.CoefficientIndex m c) K) :
    eval a (tracePullback P) = eval (traceCoefficients a) P := eval_rename _ _ _

/-- All three actual component conditions, with a checked coordinate transposition. -/
def BlockConditions (a : ParameterIndex m c q → K) : Prop :=
  Both a ∧ TraceGeneric.TraceProperties (transposeMixed (coefficientMixed a))

def GenericBlockConditions (K : Type*) [Field K] (m c q : ℕ) : Prop :=
  ∃ D : MvPolynomial (ParameterIndex m c q) K,
    (∃ a₀, eval a₀ D ≠ 0) ∧ ∀ a, eval a D ≠ 0 → BlockConditions a

/-- Intersect the trace open with the already common middle/augmented open. -/
theorem genericBlockConditions_of_generic [Infinite K]
    (hboth : GenericBoth K m c q) (htrace : TraceGeneric.GenericTrace K m c) :
    GenericBlockConditions K m c q := by
  classical
  obtain ⟨Db, ⟨ab, hab⟩, hb⟩ := hboth
  obtain ⟨Dt, ⟨aₜ, hat⟩, ht⟩ := htrace
  have hDb : Db ≠ 0 := by intro h; simp [h] at hab
  have hDt : tracePullback (q := q) Dt ≠ 0 := by
    intro h
    have he : eval (traceExtension (q := q) aₜ) (tracePullback Dt) ≠ 0 := by
      simpa only [eval_tracePullback, traceCoefficients_extension] using hat
    simp [h] at he
  obtain ⟨a₀, h₀⟩ := nonempty_principal_intersection
    (![Db, tracePullback Dt] : Fin 2 → MvPolynomial (ParameterIndex m c q) K)
    (by intro i; fin_cases i <;> assumption)
  refine ⟨Db * tracePullback Dt, ⟨a₀, ?_⟩, ?_⟩
  · rw [map_mul]
    exact mul_ne_zero (h₀ 0) (h₀ 1)
  · intro a ha
    rw [map_mul] at ha
    obtain ⟨hab, hat⟩ := mul_ne_zero_iff.mp ha
    rw [eval_tracePullback] at hat
    refine ⟨hb a hab, ?_⟩
    rw [← traceFamily_eq_transpose]
    exact ht (traceCoefficients a) hat

/-- The full three component conditions hold on one nonempty principal open
under exactly the source middle/augmented budgets and `c ≤ m`. -/
theorem genericBlockConditions_of_budgets [Infinite K] (hc : c ≤ m)
    (haug : q + (c + 1).choose 2 + 3 ≤ (m + 1).choose 2)
    (hmid : ((m + 1) / 2 ≤ c ∧ c ≤ 3*m) ∨
      (2*c ≤ m ∧ c*(m-2*c) + (m-2*c+1).choose 2 ≤ q))
    (h2 : (2 : K) ≠ 0) : GenericBlockConditions K m c q :=
  genericBlockConditions_of_generic (genericBoth_of_budgets hc haug hmid h2)
    (TraceGeneric.generic_trace hc)

theorem exists_blockConditions_of_budgets [Infinite K] (hc : c ≤ m)
    (haug : q + (c + 1).choose 2 + 3 ≤ (m + 1).choose 2)
    (hmid : ((m + 1) / 2 ≤ c ∧ c ≤ 3*m) ∨
      (2*c ≤ m ∧ c*(m-2*c) + (m-2*c+1).choose 2 ≤ q))
    (h2 : (2 : K) ≠ 0) : ∃ a : ParameterIndex m c q → K, BlockConditions a := by
  obtain ⟨D, ⟨a, ha⟩, h⟩ := genericBlockConditions_of_budgets hc haug hmid h2
  exact ⟨a, h a ha⟩

end Quartic.SimultaneousBlockConditions
