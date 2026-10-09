module

public import Quartic.SubspaceCharts

@[expose] public section

/-! Affine polynomial charts for fixed-rank row tuples. These retain all row
coordinates because the partial-last-row chart is already normalized elsewhere.
Adapted from the projective charts in the user's earlier Quartic project. -/
noncomputable section
namespace Froberg.PrefixAffineCharts
open Module MvPolynomial Quartic.SubspaceCharts
variable {K : Type*} [Field K] {N q k : ℕ}

abbrev ParameterIndex (j : Fin k ↪ Fin N) :=
  (Outside j × Fin k) ⊕ (Fin q × Fin k)

theorem parameter_count (j : Fin k ↪ Fin N) :
    Fintype.card (ParameterIndex (q := q) j) = k * (N - k) + q * k := by
  classical
  rw [Fintype.card_sum, card_coefficient_positions, Fintype.card_prod]
  simp

/-- Literal polynomial coordinates of the affine tuple chart. -/
def tuplePolynomial (j : Fin k ↪ Fin N) (i : Fin q) (l : Fin N) :
    MvPolynomial (ParameterIndex (q := q) j) K := by
  classical
  exact if hl : l ∈ Set.range j then X (Sum.inr (i, Classical.choose hl))
    else ∑ b : Fin k, X (Sum.inl (⟨l, hl⟩, b)) * X (Sum.inr (i, b))

def tupleMap (j : Fin k ↪ Fin N) (p : ParameterIndex (q := q) j → K) :
    Fin q → Fin N → K := fun i l => eval p (tuplePolynomial j i l)

def graphParameters (j : Fin k ↪ Fin N) (p : ParameterIndex (q := q) j → K) :
    Parameters K j := fun l b => p (Sum.inl (l, b))

theorem tupleMap_eq_chartLift (j : Fin k ↪ Fin N) (p : ParameterIndex (q := q) j → K)
    (i : Fin q) : tupleMap j p i = chartLift j (graphParameters j p)
      (fun b => p (Sum.inr (i, b))) := by
  classical
  funext l
  by_cases hl : l ∈ Set.range j
  · obtain ⟨b, rfl⟩ := hl
    have hb : j b ∈ Set.range j := ⟨b, rfl⟩
    have he : Classical.choose hb = b := j.injective (Classical.choose_spec hb)
    simp only [tupleMap, tuplePolynomial, dite_eq_left hb, he, chartLift_selected, eval_X]
  · rw [chartLift_outside j _ _ ⟨l, hl⟩, parameterMap_apply]
    simp [tupleMap, tuplePolynomial, hl, graphParameters]

def encode (j : Fin k ↪ Fin N) (A : Parameters K j) (U : Fin q → Fin k → K) :
    ParameterIndex (q := q) j → K :=
  Sum.elim (fun lb => A lb.1 lb.2) (fun ib => U ib.1 ib.2)

theorem tupleMap_encode (j : Fin k ↪ Fin N) (A : Parameters K j)
    (U : Fin q → Fin k → K) (i : Fin q) :
    tupleMap j (encode j A U) i = chartLift j A (U i) := by
  rw [tupleMap_eq_chartLift]
  rfl

theorem tupleMap_rank_le (j : Fin k ↪ Fin N) (p : ParameterIndex (q := q) j → K) :
    finrank K (Submodule.span K (Set.range (tupleMap j p))) ≤ k := by
  have hle : Submodule.span K (Set.range (tupleMap j p)) ≤
      chartSubspace j (graphParameters j p) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    rw [tupleMap_eq_chartLift]
    exact chartLift_mem _ _ _
  have h := Submodule.finrank_mono hle
  rwa [chartSubspace_finrank] at h

/-- Every rank-`k` tuple occurs in a finite affine polynomial chart, including
rank zero. No rank or spanning premise is hidden in the parameterization. -/
theorem cover_rank_tuple (F : Fin q → Fin N → K)
    (hrank : finrank K (Submodule.span K (Set.range F)) = k) :
    ∃ j : Fin k ↪ Fin N, ∃ p : ParameterIndex (q := q) j → K, F = tupleMap j p := by
  let S : Submodule K (Fin N → K) := Submodule.span K (Set.range F)
  obtain ⟨j, A, hA⟩ := exists_chart S hrank
  have hF (i : Fin q) : F i ∈ chartSubspace j A := by
    rw [hA]
    exact Submodule.subset_span ⟨i, rfl⟩
  have hrec (i : Fin q) : chartLift j A (fun b => F i (j b)) = F i :=
    congrArg Subtype.val ((chartEquiv j A).symm_apply_apply ⟨F i, hF i⟩)
  refine ⟨j, encode j A (fun i b => F i (j b)), ?_⟩
  funext i
  rw [tupleMap_encode, hrec]

end Froberg.PrefixAffineCharts
