module

public import Quartic.ProjectiveTupleCharts
public import Quartic.PolynomialKernelAvoidance
public import Quartic.PolynomialRankOpen

@[expose] public section

/-!
# Generic injectivity from projective relation charts

A bilinear family has a generically injective specialization if every nonzero
relation tuple imposes at least d(a-d)+qd conditions, where d is its span
dimension. The proof constructs finite polynomial relation charts and rational
kernel charts, then uses algebraic independence to avoid their images.
-/
noncomputable section
namespace Quartic.ProjectiveKernelIncidence
open Module Matrix MvPolynomial ProjectiveTupleCharts KernelPolynomialCharts
open scoped Pointwise
variable {K : Type*} [Field K] {a q n b : ℕ}

abbrev Tuple (K : Type*) (a q : ℕ) := Fin q → Fin a → K

def tupleSpan (F : Tuple K a q) := Submodule.span K (Set.range F)

 theorem tuple_expansion (F : Tuple K a q) :
    F = ∑ i : Fin q, ∑ j : Fin a, F i j • Pi.single i (Pi.single j 1) := by
  classical
  ext i j
  simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, ite_apply]

 theorem tupleSpan_smul (F : Tuple K a q) (s : K) (hs : s ≠ 0) :
    tupleSpan (s • F) = tupleSpan F := by
  have hr : Set.range (s • F) = s • Set.range F := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨F i, ⟨i, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
  unfold tupleSpan
  rw [hr]
  exact Submodule.span_smul_eq_of_isUnit (Set.range F) s (isUnit_iff_ne_zero.mpr hs)

 theorem tupleSpan_pos (F : Tuple K a q) (hF : F ≠ 0) :
    0 < finrank K (tupleSpan F) := by
  by_contra h
  have hzero : tupleSpan F = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
  apply hF
  funext i
  have hi : F i ∈ tupleSpan F := Submodule.subset_span ⟨i, rfl⟩
  simpa [hzero] using hi

/-- Polynomial matrix of the relation equation on a normalized tuple chart. -/
def chartMatrix (B : Tuple K a q →ₗ[K] (Fin n → K) →ₗ[K] (Fin b → K))
    {d : ℕ} (c : ChartType a q d) :
    Matrix (Fin b) (Fin n) (MvPolynomial (ParameterIndex c) K) :=
  fun j k => ∑ i : Fin q, ∑ h : Fin a,
    tuplePolynomial c i h * C (B (Pi.single i (Pi.single h 1)) (Pi.single k 1) j)

 theorem eval_chartMatrix (B : Tuple K a q →ₗ[K] (Fin n → K) →ₗ[K] (Fin b → K))
    {d : ℕ} (c : ChartType a q d) (p : ParameterIndex c → K) :
    evaluated (chartMatrix B c) p = LinearMap.toMatrix' (B (tupleMap c p)) := by
  classical
  ext j k
  change eval p (chartMatrix B c j k) = _
  rw [LinearMap.toMatrix'_apply]
  conv_rhs => rw [tuple_expansion (tupleMap c p)]
  simp [chartMatrix, tupleMap, map_sum, map_smul, LinearMap.sum_apply,
    LinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

 theorem chart_mulVec (B : Tuple K a q →ₗ[K] (Fin n → K) →ₗ[K] (Fin b → K))
    {d : ℕ} (c : ChartType a q d) (p : ParameterIndex c → K) (x : Fin n → K) :
    evaluated (chartMatrix B c) p *ᵥ x = B (tupleMap c p) x := by
  rw [eval_chartMatrix, LinearMap.toMatrix'_mulVec]

 theorem chart_rank (B : Tuple K a q →ₗ[K] (Fin n → K) →ₗ[K] (Fin b → K))
    {d : ℕ} (c : ChartType a q d) (p : ParameterIndex c → K) :
    (evaluated (chartMatrix B c) p).rank = finrank K (LinearMap.range (B (tupleMap c p))) := by
  have he : (evaluated (chartMatrix B c) p).mulVecLin = B (tupleMap c p) := by
    apply LinearMap.ext
    intro x
    exact chart_mulVec B c p x
  rw [Matrix.rank, he]

/-- Actual incidence exclusion on each projective rank stratum yields a
nonempty principal open of injective specializations, simultaneously for all
relation tuples. -/
theorem generic_injective [Infinite K]
    (B : Tuple K a q →ₗ[K] (Fin n → K) →ₗ[K] (Fin b → K))
    (hbound : ∀ F : Tuple K a q, F ≠ 0 →
      let d := finrank K (tupleSpan F)
      d * (a - d) + q * d ≤ finrank K (LinearMap.range (B F))) :
    ∃ P : MvPolynomial (Fin n) K, (∃ x : Fin n → K, eval x P ≠ 0) ∧
      ∀ x, eval x P ≠ 0 → Function.Injective (B.flip x) := by
  classical
  let Charts := (d : Fin (a + 1)) × ChartType a q d.val
  have hchart (c : Charts) :
      ∃ P : MvPolynomial (Fin n) K, (∃ x : Fin n → K, eval x P ≠ 0) ∧
        ∀ x, eval x P ≠ 0 → ∀ p : ParameterIndex c.2 → K,
          finrank K (tupleSpan (tupleMap c.2 p)) = c.1.val → B (tupleMap c.2 p) x ≠ 0 := by
    have hpos : 0 < q * c.1.val := Nat.mul_pos (Fin.pos c.2.2.1) (Fin.pos c.2.2.2)
    have hparam : Fintype.card (ParameterIndex c.2) < c.1.val * (a - c.1.val) + q * c.1.val := by
      rw [parameter_count]
      omega
    obtain ⟨P, hP, hp⟩ := PolynomialKernelAvoidance.principal_open_avoids_kernels (chartMatrix B c.2) hparam
    refine ⟨P, hP, ?_⟩
    intro x hx p hrank
    have hnz : tupleMap c.2 p ≠ 0 := by
      intro hz
      have he := normalized_entry c.2 p
      rw [hz] at he
      simp at he
    have hb := hbound (tupleMap c.2 p) hnz
    dsimp only at hb
    rw [hrank] at hb
    have h := hp x hx p (by rwa [chart_rank])
    rwa [chart_mulVec] at h
  choose P hP hprop using hchart
  have hne (c : Charts) : P c ≠ 0 := by
    obtain ⟨x, hx⟩ := hP c
    intro hz
    simp [hz] at hx
  obtain ⟨x₀, hx₀⟩ := nonempty_principal_intersection P hne
  refine ⟨∏ c, P c, ⟨x₀, ?_⟩, ?_⟩
  · simpa only [map_prod] using Finset.prod_ne_zero_iff.mpr (fun c _ => hx₀ c)
  intro x hx
  have hxP : ∀ c : Charts, eval x (P c) ≠ 0 := by
    simpa only [map_prod, Finset.prod_ne_zero_iff, Finset.mem_univ, forall_const] using hx
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro F hF
  by_contra hnz
  let d := finrank K (tupleSpan F)
  have hd : 0 < d := tupleSpan_pos F hnz
  have hda : d ≤ a := by
    have h := Submodule.finrank_le (tupleSpan F)
    simpa using h
  obtain ⟨c, p, s, hs, hFchart⟩ := cover_rank_tuple F hd rfl
  let c' : Charts := ⟨⟨d, by omega⟩, c⟩
  have hrank : finrank K (tupleSpan (tupleMap c p)) = d := by
    have he := congrArg (fun G : Tuple K a q => finrank K (tupleSpan G)) hFchart
    rw [tupleSpan_smul _ s hs] at he
    exact he.symm
  have hnonzero := hprop c' x (hxP c') p hrank
  apply hnonzero
  change B F x = 0 at hF
  rw [hFchart, map_smul, LinearMap.smul_apply] at hF
  exact (smul_eq_zero.mp hF).resolve_left hs

end Quartic.ProjectiveKernelIncidence
