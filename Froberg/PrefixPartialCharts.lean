module

public import Froberg.PrefixCharts
public import Froberg.PrefixAffineCharts

@[expose] public section

/-! Polynomial charts for a normalized nonzero last row with prescribed support,
and arbitrary other rows whose rank modulo the last row is fixed. -/
noncomputable section
namespace Froberg.PrefixPartialCharts
open Module MvPolynomial PrefixCharts
variable {K : Type*} [Field K] {N q k : ℕ}

abbrev Deleted (p : Fin N) := {l : Fin N // l ≠ p}

def deletedEquiv (p : Fin N) : Deleted p ≃ Fin (N - 1) :=
  Fintype.equivFinOfCardEq (by
    rw [Fintype.card_subtype_compl]
    simp)

def deletedCoordinates (p : Fin N) :
    (Deleted p → K) ≃ₗ[K] (Fin (N - 1) → K) :=
  LinearEquiv.funCongrLeft K K (deletedEquiv p).symm

abbrev ParameterIndex (T : Finset (Fin N)) (p : Fin N) (j : Fin k ↪ Fin (N - 1)) :=
  {l : Fin N // l ∈ T.erase p} ⊕ (Fin q ⊕ PrefixAffineCharts.ParameterIndex (q := q) j)

theorem parameter_count (T : Finset (Fin N)) (p : Fin N) (hp : p ∈ T)
    (j : Fin k ↪ Fin (N - 1)) :
    Fintype.card (ParameterIndex (q := q) T p j) =
      (T.card - 1) + q + k * ((N - 1) - k) + q * k := by
  simp only [ParameterIndex, Fintype.card_sum, Fintype.card_coe, Fintype.card_fin,
    Quartic.SubspaceCharts.card_outside, Fintype.card_prod, Nat.mul_comm,
    Finset.card_erase_of_mem hp]
  omega

def lastPolynomial (T : Finset (Fin N)) (p : Fin N) (j : Fin k ↪ Fin (N - 1))
    (l : Fin N) : MvPolynomial (ParameterIndex (q := q) T p j) K :=
  if l = p then 1 else if hl : l ∈ T.erase p then X (Sum.inl ⟨l, hl⟩) else 0

def rowPolynomial (T : Finset (Fin N)) (p : Fin N) (j : Fin k ↪ Fin (N - 1))
    (i : Fin q) (l : Fin N) : MvPolynomial (ParameterIndex (q := q) T p j) K :=
  if hl : l = p then X (Sum.inr (Sum.inl i)) else
    rename (fun z => Sum.inr (Sum.inr z))
      (PrefixAffineCharts.tuplePolynomial j i (deletedEquiv p ⟨l, hl⟩)) +
        X (Sum.inr (Sum.inl i)) * lastPolynomial T p j l

def lastMap (T : Finset (Fin N)) (p : Fin N) (j : Fin k ↪ Fin (N - 1))
    (a : ParameterIndex (q := q) T p j → K) : Fin N → K :=
  fun l => eval a (lastPolynomial T p j l)

def rowMap (T : Finset (Fin N)) (p : Fin N) (j : Fin k ↪ Fin (N - 1))
    (a : ParameterIndex (q := q) T p j → K) : Fin q → Fin N → K :=
  fun i l => eval a (rowPolynomial T p j i l)

@[simp] theorem lastMap_pivot (T : Finset (Fin N)) (p : Fin N) (j : Fin k ↪ Fin (N - 1))
    (a : ParameterIndex (q := q) T p j → K) : lastMap T p j a p = 1 := by
  simp [lastMap, lastPolynomial]

theorem lastMap_support (T : Finset (Fin N)) (p : Fin N) (hp : p ∈ T)
    (j : Fin k ↪ Fin (N - 1)) (a : ParameterIndex (q := q) T p j → K)
    (l : Fin N) (hl : l ∉ T) : lastMap T p j a l = 0 := by
  have hlp : l ≠ p := by rintro rfl; contradiction
  simp [lastMap, lastPolynomial, hlp, Finset.mem_erase, hl]

def encode (T : Finset (Fin N)) (p : Fin N) (j : Fin k ↪ Fin (N - 1))
    (z : Fin N → K) (c : Fin q → K) (a : PrefixAffineCharts.ParameterIndex (q := q) j → K) :
    ParameterIndex (q := q) T p j → K :=
  Sum.elim (fun l => z l.val) (Sum.elim c a)

theorem lastMap_encode (T : Finset (Fin N)) (p : Fin N) (j : Fin k ↪ Fin (N - 1))
    (z : Fin N → K) (hz : z p = 1) (hsupp : ∀ l, l ∉ T → z l = 0)
    (c : Fin q → K) (a : PrefixAffineCharts.ParameterIndex (q := q) j → K) :
    lastMap T p j (encode T p j z c a) = z := by
  ext l
  by_cases hlp : l = p
  · subst l; simp [hz]
  · by_cases hlT : l ∈ T
    · simp [lastMap, lastPolynomial, hlp, Finset.mem_erase.mpr ⟨hlp, hlT⟩, encode]
    · simp [lastMap, lastPolynomial, hlp, Finset.mem_erase, hlT, hsupp l hlT]

theorem rowMap_encode (T : Finset (Fin N)) (p : Fin N) (j : Fin k ↪ Fin (N - 1))
    (z : Fin N → K) (hz : z p = 1) (hsupp : ∀ l, l ∉ T → z l = 0)
    (c : Fin q → K) (a : PrefixAffineCharts.ParameterIndex (q := q) j → K) (i : Fin q) :
    rowMap T p j (encode T p j z c a) i =
      reconstruct z p (c i)
        ((deletedCoordinates p).symm (PrefixAffineCharts.tupleMap j a i)) := by
  ext l
  by_cases hlp : l = p
  · subst l
    simp [rowMap, rowPolynomial, reconstruct, encode]
  · have hlast := congrFun (lastMap_encode T p j z hz hsupp c a) l
    change eval (encode T p j z c a) (lastPolynomial T p j l) = z l at hlast
    simp only [rowMap, rowPolynomial, map_add, map_mul, eval_X,
      eval_rename, hlast, reconstruct, dite_eq_right hlp]
    rfl

/-- Coverage of every normalized restricted-last-row tuple, classified by the
actual rank of its quotient rows. -/
theorem cover_normalized_tuple (T : Finset (Fin N)) (p : Fin N)
    (F : Fin q → Fin N → K) (z : Fin N → K) (hz : z p = 1)
    (hsupp : ∀ l, l ∉ T → z l = 0)
    (hrank : finrank K (Submodule.span K (Set.range
      (fun i => deletedCoordinates p (deletePivot z p (F i))))) = k) :
    ∃ j : Fin k ↪ Fin (N - 1), ∃ a : ParameterIndex (q := q) T p j → K,
      rowMap T p j a = F ∧ lastMap T p j a = z := by
  let G : Fin q → Fin (N - 1) → K := fun i => deletedCoordinates p (deletePivot z p (F i))
  obtain ⟨j, a, ha⟩ := PrefixAffineCharts.cover_rank_tuple G hrank
  refine ⟨j, encode T p j z (fun i => F i p) a, ?_, lastMap_encode T p j z hz hsupp _ a⟩
  funext i
  rw [rowMap_encode T p j z hz hsupp]
  have hgi : PrefixAffineCharts.tupleMap j a i = deletedCoordinates p (deletePivot z p (F i)) :=
    (congrFun ha i).symm
  rw [hgi, LinearEquiv.symm_apply_apply, reconstruct_deletePivot]

/-- Reindexing the deleted coordinates preserves the rank drop. -/
theorem finrank_deleted_rows (F : Fin q → Fin N → K) (z : Fin N → K)
    (p : Fin N) (hz : z p = 1) :
    finrank K (Submodule.span K (Set.range
      (fun i => deletedCoordinates p (deletePivot z p (F i))))) + 1 =
        finrank K (Submodule.span K (Set.range F) ⊔ K ∙ z : Submodule K (Fin N → K)) := by
  have he := (deletedCoordinates (K := K) p).finrank_map_eq
    (Submodule.span K (Set.range (fun i => deletePivot z p (F i))))
  rw [Submodule.map_span, ← Set.range_comp] at he
  change finrank K (Submodule.span K (Set.range
      (fun i => deletedCoordinates p (deletePivot z p (F i))))) = _ at he
  rw [he]
  exact finrank_eliminated_rows F z p hz

/-- The normalized nonzero-last-row stratum of full rank `k+1` is covered by
polynomial maps with `(s-1)+q+k*(N-1-k)+q*k` parameters, where `s=T.card`. -/
theorem cover_normalized_rank_stratum (T : Finset (Fin N)) (p : Fin N)
    (F : Fin q → Fin N → K) (z : Fin N → K) (hz : z p = 1)
    (hsupp : ∀ l, l ∉ T → z l = 0)
    (hrank : finrank K (Submodule.span K (Set.range F) ⊔ K ∙ z :
      Submodule K (Fin N → K)) = k + 1) :
    ∃ j : Fin k ↪ Fin (N - 1), ∃ a : ParameterIndex (q := q) T p j → K,
      rowMap T p j a = F ∧ lastMap T p j a = z := by
  apply cover_normalized_tuple T p F z hz hsupp
  have h := finrank_deleted_rows F z p hz
  omega

open scoped Pointwise

/-- Simultaneous nonzero scaling does not change the row span. -/
theorem rowSpan_smul (F : Fin q → Fin N → K) (z : Fin N → K) (c : K) (hc : c ≠ 0) :
    Submodule.span K (Set.range (c • F)) ⊔ K ∙ (c • z) =
      Submodule.span K (Set.range F) ⊔ K ∙ z := by
  have hr : Set.range (c • F) = c • Set.range F := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨F i, ⟨i, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
  rw [hr, Submodule.span_smul_eq_of_isUnit _ _ (isUnit_iff_ne_zero.mpr hc),
    Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hc)]

/-- Projective coverage of every nonzero-last-row stratum with the sharp
parameter count. No tail-rank subdivision is required. -/
theorem cover_nonzero_last_row (T : Finset (Fin N))
    (F : Fin q → Fin N → K) (z : Fin N → K) (hz : z ≠ 0)
    (hsupp : ∀ l, l ∉ T → z l = 0)
    (hrank : finrank K (Submodule.span K (Set.range F) ⊔ K ∙ z :
      Submodule K (Fin N → K)) = k + 1) :
    ∃ p ∈ T, ∃ j : Fin k ↪ Fin (N - 1), ∃ a : ParameterIndex (q := q) T p j → K,
      ∃ c : K, c ≠ 0 ∧ F = c • rowMap T p j a ∧ z = c • lastMap T p j a := by
  obtain ⟨p, hp, c, hc, z', hz'p, hzsupp, hzz'⟩ :=
    exists_normalized_supported_row T z hz hsupp
  let F' : Fin q → Fin N → K := c⁻¹ • F
  have hz' : z' = c⁻¹ • z := by rw [hzz', smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hrank' : finrank K (Submodule.span K (Set.range F') ⊔ K ∙ z' :
      Submodule K (Fin N → K)) = k + 1 := by
    rw [hz']
    change finrank K (Submodule.span K (Set.range (c⁻¹ • F)) ⊔ K ∙ (c⁻¹ • z) :
      Submodule K (Fin N → K)) = k + 1
    rw [rowSpan_smul F z c⁻¹ (inv_ne_zero hc)]
    exact hrank
  obtain ⟨j, a, hF, hz''⟩ := cover_normalized_rank_stratum T p F' z' hz'p hzsupp hrank'
  refine ⟨p, hp, j, a, c, hc, ?_, ?_⟩
  · rw [hF]
    change F = c • (c⁻¹ • F)
    rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
  · rw [hz'']
    exact hzz'

/-- The normalized coefficient-ideal Hilbert bound pays for the nonzero-last-row
chart at `M=q*N+s`; the zero-last-row case uses the ordinary injectivity budget. -/
theorem nonzero_last_row_rank_budget {N q s k H : ℕ}
    (hN : 0 < N) (hs : s ≤ N) (hk : 0 < k) (hkN : k ≤ N)
    (hH : N * (H + k * (N - k)) ≤ (N - k) * (q * N + s)) :
    H + q * k + (k - 1) * (N - k) + s ≤ q * N + s := by
  have he : k + (N - k) = N := Nat.add_sub_of_le hkN
  have hek : k - 1 + 1 = k := by omega
  have hstep : N * (H + k * (N - k)) ≤ N * ((N - k) * (q + 1)) := by
    calc
      _ ≤ (N - k) * (q * N + s) := hH
      _ ≤ (N - k) * (q * N + N) := Nat.mul_le_mul_left _ (Nat.add_le_add_left hs _)
      _ = _ := by ring
  have hcancel : H + k * (N - k) ≤ (N - k) * (q + 1) := by nlinarith
  nlinarith

end Froberg.PrefixPartialCharts
