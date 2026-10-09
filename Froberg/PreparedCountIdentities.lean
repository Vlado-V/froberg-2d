module

public import Froberg.TargetLayerAssembly
public import Froberg.ConcreteCounts
public import Froberg.UpperEndpointConvolution

@[expose] public section

/-! Literal label cardinalities and the critical scalar density of the
prepared family, including any fixed number of appended private slots. -/
noncomputable section
namespace Froberg
open Filter Finset Polynomial
open scoped Topology

theorem preparedLabel_card (q : ℕ) (J : Finset ℕ) (counts : ℕ → ℕ) :
    Fintype.card (PreparedParameters.Label q J counts)=q+∑ j∈J,counts j := by
  simp [PreparedParameters.Label,ProductRows.LayerLabel,Fintype.card_sigma,Finset.sum_attach]

theorem preparedTargetLabel_card (q f u : ℕ) (J : Finset ℕ) (counts : ℕ → ℕ) :
    Fintype.card (PreparedTarget.Label q f u J counts)=q+(∑ j∈J,counts j)+f+u := by
  change Fintype.card (PreparedParameters.Label q J counts ⊕ (Fin f ⊕ Fin u))=
    q+(∑ j∈J,counts j)+f+u
  rw [Fintype.card_sum,preparedLabel_card,Fintype.card_sum,Fintype.card_fin,Fintype.card_fin]
  omega

theorem activeEven_eq_insert_higher {d : ℕ} (hd : 3≤d) :
    activeEvenIndices d=insert 2 (activeHigherIndices d) := by
  ext j
  simp only [mem_insert]
  constructor
  · intro hj
    by_cases h2 : j=2
    · exact Or.inl h2
    · right
      obtain ⟨hj2,hjd,k,hk⟩ := activeEvenIndices_bounds hd hj
      exact mem_filter.mpr ⟨hj,by omega⟩
  · rintro (rfl | hj)
    · exact two_mem_activeEvenIndices hd
    · exact (mem_filter.mp hj).1

theorem sum_targetLayerCount {d : ℕ} (hd : 3≤d) (h m e : ℕ) :
    (∑ j∈activeEvenIndices d,targetLayerCount d h m e j)=
      e+∑ j∈activeHigherIndices d,higherGeneratorCount d h m j := by
  rw [activeEven_eq_insert_higher hd,Finset.sum_insert]
  · congr 1
    apply Finset.sum_congr rfl
    intro j hj
    have hj4 := (mem_filter.mp hj).2
    simp only [targetLayerCount,if_neg (show j≠2 by omega)]
  · intro hj
    have := (mem_filter.mp hj).2
    omega

theorem exact_preparedTarget_card {d k h lo m a f e : ℕ} {upper : Bool}
    (hd : 3≤d) (hc : ExactCountConditions d k h lo m a f e upper) :
    Fintype.card (PreparedTarget.Label (upperCount m d) f (tailGeneratorCount d h)
      (activeEvenIndices d) (targetLayerCount d h m e))=adjacentCriticalCount upper (m+h) d := by
  rw [preparedTargetLabel_card,sum_targetLayerCount hd]
  have ht := hc.total
  unfold auxiliaryGeneratorCount at ht
  omega

def preparedScalarCount (d h m e : ℕ) : ℕ :=
  upperCount m d+e+∑ j∈activeHigherIndices d,higherGeneratorCount d h m j

theorem preparedScalarCount_eq_card {d : ℕ} (hd : 3≤d) (h m e : ℕ) :
    preparedScalarCount d h m e=
      Fintype.card (PreparedParameters.Label (upperCount m d) (activeEvenIndices d)
        (targetLayerCount d h m e)) := by
  rw [preparedLabel_card,sum_targetLayerCount hd]
  unfold preparedScalarCount
  omega

theorem quadraticCount_lower_order {d : ℕ} (hd : 3≤d) (h : ℕ) (e : ℕ → ℕ)
    (he : ∀ᶠ m : ℕ in atTop,(e m : ℝ)<countBeta d*(h : ℝ)^2*(m : ℝ)^(d-2)) :
    Tendsto (fun m : ℕ => (e m : ℝ)/(m : ℝ)^d) atTop (𝓝 0) := by
  let P : Polynomial ℝ := monomial (d-2) (countBeta d*(h : ℝ)^2)
  have hp : P.natDegree<d := (natDegree_monomial_le _).trans_lt (by omega)
  have hlim : Tendsto (fun m : ℕ =>
      (countBeta d*(h : ℝ)^2*(m : ℝ)^(d-2))/(m : ℝ)^d) atTop (𝓝 0) := by
    simpa only [P,eval_monomial,coeff_eq_zero_of_natDegree_lt hp] using
      polynomial_div_pow_nat_tendsto P d hp.le
  apply squeeze_zero' (Eventually.of_forall fun _ => by positivity) _ hlim
  exact he.mono fun m hm => div_le_div_of_nonneg_right hm.le (by positivity)

theorem preparedScalarCount_normalized_limit {d : ℕ} (hd : 3≤d) (h extra : ℕ)
    (e : ℕ → ℕ)
    (he : ∀ᶠ m : ℕ in atTop,(e m : ℝ)<countBeta d*(h : ℝ)^2*(m : ℝ)^(d-2)) :
    Tendsto (fun m : ℕ => ((preparedScalarCount d h m (e m)+extra : ℕ) : ℝ)/(m : ℝ)^d)
      atTop (𝓝 (criticalRatio d/(d.factorial : ℝ))) := by
  have hs : Tendsto (fun m : ℕ =>
      ((extra+∑ j∈activeHigherIndices d,higherGeneratorCount d h m j : ℕ) : ℝ)/(m : ℝ)^d)
      atTop (𝓝 0) := by
    apply auxiliary_counts_lower_order (activeHigherIndices d) (by omega)
      (fun j => (101/100 : ℝ)*higherCountGamma d j*(h : ℝ)^j)
      (fun j => d-j) extra
    · intro j _
      exact mul_nonneg (mul_nonneg (by norm_num) (higherCountGamma_pos d j).le) (by positivity)
    · intro j hj
      have := (mem_filter.mp hj).2
      omega
  have ht := ((upperCount_normalized_limit (by omega : 2≤d)).add
    (quadraticCount_lower_order hd h e he)).add hs
  simp only [add_zero] at ht
  apply ht.congr'
  exact Eventually.of_forall fun m => by
    simp only [preparedScalarCount,Nat.cast_add,Nat.cast_sum]
    ring

end Froberg
