module

public import Quartic.SubspaceCharts
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Tactic

@[expose] public section

/-!
# Polynomial charts for tuples up to a common nonzero scalar

A rank-d tuple is expressed in a graph chart for its span. One nonzero selected
tuple coordinate is normalized to one; all remaining selected coordinates and
the graph coefficients are free parameters. The resulting tuple coordinates
are literal multivariate polynomials. This is a covering and parameter-count
statement, without a geometric dimension or incidence assertion.
-/
noncomputable section
namespace Quartic.ProjectiveTupleCharts
open Module MvPolynomial SubspaceCharts
variable {K : Type*} [Field K] {a q d : ℕ}

/-- A graph coordinate selector and the tuple entry normalized to one. -/
abbrev ChartType (a q d : ℕ) := (Fin d ↪ Fin a) × (Fin q × Fin d)

/-- Graph coefficients and every selected tuple entry except the normalized one. -/
abbrev ParameterIndex (c : ChartType a q d) :=
  (Outside c.1 × Fin d) ⊕ {p : Fin q × Fin d // p ≠ c.2}

instance chartTypeFinite (a q d : ℕ) : Finite (ChartType a q d) := inferInstance

/-- There are exactly d(a-d)+qd-1 scalar parameters, including the normalization. -/
theorem parameter_count (c : ChartType a q d) :
    Fintype.card (ParameterIndex c) = d * (a - d) + q * d - 1 := by
  classical
  have hqd : 0 < q * d := Nat.mul_pos (Fin.pos c.2.1) (Fin.pos c.2.2)
  have hother : Fintype.card {p : Fin q × Fin d // p ≠ c.2} = q * d - 1 := by
    rw [Fintype.card_subtype_compl]
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_subtype_eq]
  rw [Fintype.card_sum, card_coefficient_positions, hother]
  omega

/-- Selected tuple coordinates: the distinguished coordinate is the constant
one, and each other coordinate is its own parameter variable. -/
def selectedPolynomial (c : ChartType a q d) (p : Fin q × Fin d) :
    MvPolynomial (ParameterIndex c) K :=
  if h : p = c.2 then 1 else X (Sum.inr ⟨p, h⟩)

/-- Literal polynomial coordinates of the normalized tuple. Outside the
selected coordinates they are the graph coefficient times coordinate sums. -/
def tuplePolynomial (c : ChartType a q d) (i : Fin q) (k : Fin a) :
    MvPolynomial (ParameterIndex c) K := by
  classical
  exact if hk : k ∈ Set.range c.1 then selectedPolynomial c (i, Classical.choose hk)
    else ∑ b : Fin d, X (Sum.inl (⟨k, hk⟩, b)) * selectedPolynomial c (i, b)

/-- The actual evaluated polynomial tuple chart. -/
def tupleMap (c : ChartType a q d) (p : ParameterIndex c → K) : Fin q → Fin a → K :=
  fun i k => eval p (tuplePolynomial c i k)

/-- The graph coefficient array read from the chart parameters. -/
def graphParameters (c : ChartType a q d) (p : ParameterIndex c → K) : Parameters K c.1 :=
  fun k b => p (Sum.inl (k, b))

/-- Evaluated chart vectors are actual lifts in the selected graph chart. -/
theorem tupleMap_eq_chartLift (c : ChartType a q d) (p : ParameterIndex c → K) (i : Fin q) :
    tupleMap c p i = chartLift c.1 (graphParameters c p)
      (fun b => eval p (selectedPolynomial c (i, b))) := by
  classical
  funext k
  by_cases hk : k ∈ Set.range c.1
  · obtain ⟨b, rfl⟩ := hk
    have hb : c.1 b ∈ Set.range c.1 := ⟨b, rfl⟩
    have he : Classical.choose hb = b := c.1.injective (Classical.choose_spec hb)
    simp only [tupleMap, tuplePolynomial, dite_eq_left hb, he, chartLift_selected]
  · rw [chartLift_outside c.1 _ _ ⟨k, hk⟩, parameterMap_apply]
    simp [tupleMap, tuplePolynomial, hk, graphParameters]

/-- The chosen tuple coordinate really is normalized to one for all parameters. -/
theorem normalized_entry (c : ChartType a q d) (p : ParameterIndex c → K) :
    tupleMap c p c.2.1 (c.1 c.2.2) = 1 := by
  rw [tupleMap_eq_chartLift, chartLift_selected]
  simp [selectedPolynomial]

/-- Every chart tuple lies in its d-dimensional graph subspace; its span may
have smaller dimension unless the selected tuple coordinates have full rank. -/
theorem tupleMap_mem_graph (c : ChartType a q d) (p : ParameterIndex c → K) (i : Fin q) :
    tupleMap c p i ∈ chartSubspace c.1 (graphParameters c p) := by
  rw [tupleMap_eq_chartLift]
  exact chartLift_mem _ _ _

/-- Every tuple chart has span dimension at most the selected graph dimension. -/
theorem tupleMap_rank_le (c : ChartType a q d) (p : ParameterIndex c → K) :
    finrank K (Submodule.span K (Set.range (tupleMap c p))) ≤ d := by
  have hle : Submodule.span K (Set.range (tupleMap c p)) ≤
      chartSubspace c.1 (graphParameters c p) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact tupleMap_mem_graph c p i
  have h := Submodule.finrank_mono hle
  rw [chartSubspace_finrank] at h
  exact h

/-- Encode a graph array and a selected tuple coordinate array whose pivot is one. -/
def encode (c : ChartType a q d) (A : Parameters K c.1) (U : Fin q → Fin d → K) :
    ParameterIndex c → K :=
  Sum.elim (fun z => A z.1 z.2) (fun z => U z.val.1 z.val.2)

@[simp] theorem graphParameters_encode (c : ChartType a q d) (A : Parameters K c.1)
    (U : Fin q → Fin d → K) : graphParameters c (encode c A U) = A := rfl

/-- Encoding preserves all selected coordinates after normalizing the distinguished one. -/
theorem selectedPolynomial_encode (c : ChartType a q d) (A : Parameters K c.1)
    (U : Fin q → Fin d → K) (hU : U c.2.1 c.2.2 = 1) (i : Fin q) (b : Fin d) :
    eval (encode c A U) (selectedPolynomial c (i, b)) = U i b := by
  classical
  by_cases h : (i, b) = c.2
  · have hi : i = c.2.1 := congrArg Prod.fst h
    have hb : b = c.2.2 := congrArg Prod.snd h
    simp [selectedPolynomial, hi, hb, hU]
  · simp [selectedPolynomial, h, encode]

/-- Encoding and evaluating recovers the graph lifts of the prescribed selected entries. -/
theorem tupleMap_encode (c : ChartType a q d) (A : Parameters K c.1)
    (U : Fin q → Fin d → K) (hU : U c.2.1 c.2.2 = 1) (i : Fin q) :
    tupleMap c (encode c A U) i = chartLift c.1 A (U i) := by
  rw [tupleMap_eq_chartLift, graphParameters_encode]
  congr 1
  funext b
  exact selectedPolynomial_encode c A U hU i b

/-- Every tuple of positive span dimension is a common nonzero scalar multiple
of a value of one of the finitely many polynomial tuple charts. -/
theorem cover_rank_tuple (F : Fin q → Fin a → K) (hd : 0 < d)
    (hrank : finrank K (Submodule.span K (Set.range F)) = d) :
    ∃ c : ChartType a q d, ∃ p : ParameterIndex c → K, ∃ s : K,
      s ≠ 0 ∧ F = s • tupleMap c p := by
  classical
  let S : Submodule K (Fin a → K) := Submodule.span K (Set.range F)
  obtain ⟨j, A, hA⟩ := exists_chart S hrank
  have hF (i : Fin q) : F i ∈ chartSubspace j A := by
    rw [hA]
    exact Submodule.subset_span ⟨i, rfl⟩
  have hrec (i : Fin q) : chartLift j A (fun b => F i (j b)) = F i := by
    exact congrArg Subtype.val ((chartEquiv j A).symm_apply_apply ⟨F i, hF i⟩)
  obtain ⟨i₀, b₀, hnonzero⟩ : ∃ i b, F i (j b) ≠ 0 := by
    by_contra! hzero
    have hFzero : F = 0 := by
      funext i
      rw [← hrec i]
      have hz : (fun b => F i (j b)) = 0 := funext (hzero i)
      rw [hz, map_zero]
      rfl
    have hSzero : S = ⊥ := by simp [S, hFzero]
    change finrank K S = d at hrank
    rw [hSzero, finrank_bot] at hrank
    omega
  let c : ChartType a q d := (j, i₀, b₀)
  let s : K := F i₀ (j b₀)
  let U : Fin q → Fin d → K := fun i b => s⁻¹ * F i (j b)
  have hU : U c.2.1 c.2.2 = 1 := inv_mul_cancel₀ hnonzero
  refine ⟨c, encode c A U, s, hnonzero, ?_⟩
  funext i
  change F i = s • tupleMap c (encode c A U) i
  rw [tupleMap_encode c A U hU]
  have hUi : U i = s⁻¹ • (fun b => F i (j b)) := rfl
  rw [hUi, map_smul, hrec, smul_smul, mul_inv_cancel₀ hnonzero, one_smul]

end Quartic.ProjectiveTupleCharts
