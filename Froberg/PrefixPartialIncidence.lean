module

public import Froberg.PrefixPartialCharts
public import Quartic.ProjectiveKernelIncidence

@[expose] public section

/-! Incidence avoidance for a rectangular array with a partially filled last
row. The sharp chart count handles the surjective side of generic prefix rank. -/
noncomputable section
namespace Froberg.PrefixPartialIncidence
open Module Matrix MvPolynomial Quartic.KernelPolynomialCharts
open PrefixPartialCharts
variable {K : Type*} [Field K] {N q v w : ℕ}

abbrev Relations (K : Type*) (N q : ℕ) :=
  (Fin q → Fin N → K) × (Fin N → K)

def rowSpan (R : Relations K N q) : Submodule K (Fin N → K) :=
  Submodule.span K (Set.range R.1) ⊔ K ∙ R.2

theorem relation_expansion (R : Relations K N q) :
    R = (∑ i : Fin q, ∑ j : Fin N, R.1 i j • (Pi.single i (Pi.single j 1), 0)) +
      ∑ j : Fin N, R.2 j • (0, Pi.single j 1) := by
  classical
  apply Prod.ext
  · funext i j
    simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, ite_apply]
  · funext j
    simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, ite_apply]

/-- Matrix of the bilinear relation equation on a normalized partial-row chart. -/
def chartMatrix (B : Relations K N q →ₗ[K] (Fin v → K) →ₗ[K] (Fin w → K))
    (T : Finset (Fin N)) {k : ℕ} (p : Fin N) (j : Fin k ↪ Fin (N - 1)) :
    Matrix (Fin w) (Fin v) (MvPolynomial (ParameterIndex (q := q) T p j) K) :=
  fun h l => (∑ i : Fin q, ∑ a : Fin N,
    rowPolynomial T p j i a * C (B (Pi.single i (Pi.single a 1), 0) (Pi.single l 1) h)) +
    ∑ a : Fin N, lastPolynomial T p j a * C (B (0, Pi.single a 1) (Pi.single l 1) h)

theorem eval_chartMatrix (B : Relations K N q →ₗ[K] (Fin v → K) →ₗ[K] (Fin w → K))
    (T : Finset (Fin N)) {k : ℕ} (p : Fin N) (j : Fin k ↪ Fin (N - 1))
    (a : ParameterIndex (q := q) T p j → K) :
    evaluated (chartMatrix B T p j) a =
      LinearMap.toMatrix' (B (rowMap T p j a, lastMap T p j a)) := by
  classical
  have hleft (c : K) (F : Fin q → Fin N → K) : B (c • F, 0) = c • B (F, 0) := by
    simpa using B.map_smul c (F, 0)
  have hright (c : K) (z : Fin N → K) : B (0, c • z) = c • B (0, z) := by
    simpa using B.map_smul c (0, z)
  ext h l
  change eval a (chartMatrix B T p j h l) = _
  rw [LinearMap.toMatrix'_apply]
  conv_rhs => rw [relation_expansion (rowMap T p j a, lastMap T p j a)]
  simp [chartMatrix, rowMap, lastMap, map_sum, map_smul, hleft, hright,
    LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem chart_mulVec (B : Relations K N q →ₗ[K] (Fin v → K) →ₗ[K] (Fin w → K))
    (T : Finset (Fin N)) {k : ℕ} (p : Fin N) (j : Fin k ↪ Fin (N - 1))
    (a : ParameterIndex (q := q) T p j → K) (x : Fin v → K) :
    evaluated (chartMatrix B T p j) a *ᵥ x = B (rowMap T p j a, lastMap T p j a) x := by
  rw [eval_chartMatrix, LinearMap.toMatrix'_mulVec]

theorem chart_rank (B : Relations K N q →ₗ[K] (Fin v → K) →ₗ[K] (Fin w → K))
    (T : Finset (Fin N)) {k : ℕ} (p : Fin N) (j : Fin k ↪ Fin (N - 1))
    (a : ParameterIndex (q := q) T p j → K) :
    (evaluated (chartMatrix B T p j) a).rank =
      finrank K (B (rowMap T p j a, lastMap T p j a)).range := by
  have he : (evaluated (chartMatrix B T p j) a).mulVecLin =
      B (rowMap T p j a, lastMap T p j a) :=
    LinearMap.ext (chart_mulVec B T p j a)
  rw [Matrix.rank, he]

/-- A principal open excludes every supported relation with nonzero last row. -/
theorem principal_open_avoids_nonzero_last_row [Infinite K]
    (B : Relations K N q →ₗ[K] (Fin v → K) →ₗ[K] (Fin w → K))
    (T : Finset (Fin N))
    (hbound : ∀ R : Relations K N q, R.2 ≠ 0 →
      (∀ l, l ∉ T → R.2 l = 0) →
      let r := finrank K (rowSpan R)
      q * r + (r - 1) * (N - r) + T.card ≤ finrank K (B R).range) :
    ∃ P : MvPolynomial (Fin v) K, (∃ x, eval x P ≠ 0) ∧
      ∀ x, eval x P ≠ 0 → ∀ R : Relations K N q,
        R.2 ≠ 0 → (∀ l, l ∉ T → R.2 l = 0) → B R x ≠ 0 := by
  classical
  let Charts := (k : Fin N) × (p : ↑T) × (Fin k.val ↪ Fin (N - 1))
  have hchart (c : Charts) :
      ∃ P : MvPolynomial (Fin v) K, (∃ x, eval x P ≠ 0) ∧
        ∀ x, eval x P ≠ 0 → ∀ a : ParameterIndex (q := q) T c.2.1.val c.2.2 → K,
          finrank K (rowSpan (rowMap T c.2.1.val c.2.2 a,
            lastMap T c.2.1.val c.2.2 a)) = c.1.val + 1 →
          B (rowMap T c.2.1.val c.2.2 a, lastMap T c.2.1.val c.2.2 a) x ≠ 0 := by
    have hs : 0 < T.card := Finset.card_pos.mpr ⟨c.2.1.val, c.2.1.property⟩
    have hparam : Fintype.card (ParameterIndex (q := q) T c.2.1.val c.2.2) <
        q * (c.1.val + 1) + c.1.val * (N - (c.1.val + 1)) + T.card := by
      rw [parameter_count T c.2.1.val c.2.1.property]
      have hsub : (N - 1) - c.1.val = N - (c.1.val + 1) := by omega
      rw [hsub]
      have hs1 : T.card - 1 + 1 = T.card := by omega
      nlinarith
    obtain ⟨P, hP, hp⟩ := Quartic.PolynomialKernelAvoidance.principal_open_avoids_kernels
      (chartMatrix B T c.2.1.val c.2.2) hparam
    refine ⟨P, hP, ?_⟩
    intro x hx a hrank
    have hnz : lastMap (K := K) (q := q) T c.2.1.val c.2.2 a ≠ 0 := by
      intro hz
      have h := lastMap_pivot T c.2.1.val c.2.2 a
      rw [hz] at h
      simp at h
    have hb := hbound (rowMap T c.2.1.val c.2.2 a,
      lastMap T c.2.1.val c.2.2 a) hnz
      (lastMap_support T c.2.1.val c.2.1.property c.2.2 a)
    dsimp only at hb
    rw [hrank, Nat.add_sub_cancel] at hb
    have h := hp x hx a (by rwa [chart_rank])
    rwa [chart_mulVec] at h
  choose P hP hgood using hchart
  have hne (c : Charts) : P c ≠ 0 := by
    obtain ⟨x, hx⟩ := hP c
    intro hz
    simp [hz] at hx
  obtain ⟨x₀, hx₀⟩ := Quartic.nonempty_principal_intersection P hne
  refine ⟨∏ c, P c, ⟨x₀, ?_⟩, ?_⟩
  · simpa only [map_prod] using Finset.prod_ne_zero_iff.mpr (fun c _ => hx₀ c)
  intro x hx R hnz hsupp hzero
  have hxP : ∀ c : Charts, eval x (P c) ≠ 0 := by
    simpa only [map_prod, Finset.prod_ne_zero_iff, Finset.mem_univ, forall_const] using hx
  let r := finrank K (rowSpan R)
  have hr : 0 < r := by
    by_contra h
    have hz : rowSpan R = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
    have hm : R.2 ∈ rowSpan R := (show K ∙ R.2 ≤ rowSpan R from le_sup_right) (Submodule.mem_span_singleton_self R.2)
    rw [hz] at hm
    exact hnz hm
  have hrN : r ≤ N := by simpa [r] using Submodule.finrank_le (rowSpan R)
  obtain ⟨p, hp, j, a, c, hc, hF, hz⟩ := cover_nonzero_last_row
    T R.1 R.2 hnz hsupp (k := r - 1) (by change r = r - 1 + 1; omega)
  let chart : Charts := ⟨⟨r - 1, by omega⟩, ⟨p, hp⟩, j⟩
  have hrelation : R = c • (rowMap T p j a, lastMap T p j a) := Prod.ext hF hz
  have hRank : finrank K (rowSpan (rowMap T p j a, lastMap T p j a)) = r - 1 + 1 := by
    have he := congrArg (fun z : Relations K N q => finrank K (rowSpan z)) hrelation
    change r = finrank K (Submodule.span K (Set.range (c • rowMap T p j a)) ⊔
      K ∙ (c • lastMap T p j a) : Submodule K (Fin N → K)) at he
    rw [rowSpan_smul _ _ c hc] at he
    change finrank K (Submodule.span K (Set.range (rowMap T p j a)) ⊔
      K ∙ lastMap T p j a : Submodule K (Fin N → K)) = r - 1 + 1
    omega
  have hnonzero := hgood chart x (hxP chart) a hRank
  apply hnonzero
  rw [hrelation, map_smul, LinearMap.smul_apply] at hzero
  exact (smul_eq_zero.mp hzero).resolve_left hc

/-- Combining the zero and nonzero last-row strata excludes every nontrivial
supported relation at one actual parameter value. -/
theorem exists_injective_on_supported [Infinite K]
    (B : Relations K N q →ₗ[K] (Fin v → K) →ₗ[K] (Fin w → K))
    (T : Finset (Fin N))
    (hzero : ∀ F : Fin q → Fin N → K, F ≠ 0 →
      let r := finrank K (Submodule.span K (Set.range F))
      r * (N - r) + q * r ≤ finrank K (B (F, 0)).range)
    (hlast : ∀ R : Relations K N q, R.2 ≠ 0 →
      (∀ l, l ∉ T → R.2 l = 0) →
      let r := finrank K (rowSpan R)
      q * r + (r - 1) * (N - r) + T.card ≤ finrank K (B R).range) :
    ∃ x : Fin v → K, ∀ R : Relations K N q,
      (∀ l, l ∉ T → R.2 l = 0) → B R x = 0 → R = 0 := by
  classical
  let B₀ := B.comp (LinearMap.inl K (Fin q → Fin N → K) (Fin N → K))
  obtain ⟨P₀, hP₀, hgood₀⟩ := Quartic.ProjectiveKernelIncidence.generic_injective B₀ hzero
  obtain ⟨P₁, hP₁, hgood₁⟩ := principal_open_avoids_nonzero_last_row B T hlast
  have hne₀ : P₀ ≠ 0 := by
    obtain ⟨x, hx⟩ := hP₀
    intro h
    simp [h] at hx
  have hne₁ : P₁ ≠ 0 := by
    obtain ⟨x, hx⟩ := hP₁
    intro h
    simp [h] at hx
  obtain ⟨x, hx⟩ := Quartic.nonempty_principal_intersection
    (fun b : Bool => if b then P₀ else P₁) (by intro b; cases b <;> assumption)
  have hx₀ : eval x P₀ ≠ 0 := by simpa using hx true
  have hx₁ : eval x P₁ ≠ 0 := by simpa using hx false
  refine ⟨x, ?_⟩
  intro R hsupp hR
  by_cases hz : R.2 = 0
  · have hR' : B (R.1, 0) x = 0 := by
      have he : (R.1, 0) = R := Prod.ext rfl hz.symm
      rw [he]
      exact hR
    have hF : R.1 = 0 := (hgood₀ x hx₀) (by
      change B (R.1, 0) x = B (0, 0) x
      simpa only [show ((0 : Fin q → Fin N → K), (0 : Fin N → K)) = 0 from rfl,
        map_zero, LinearMap.zero_apply] using hR')
    exact Prod.ext hF hz
  · exact False.elim (hgood₁ x hx₁ R hz hsupp hR)

end Froberg.PrefixPartialIncidence
