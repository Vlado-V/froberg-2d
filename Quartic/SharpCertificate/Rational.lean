import Quartic.SharpCertificate.Certificate

/-! The certificates cover exactly the manuscript's rational prefix-edge points. -/

namespace Quartic.SharpCertificate

open Quartic.Counts Quartic.FiniteCounts Quartic.ProfileCertificate

/-- The integer formula used in the core shadow is the rational ceiling. -/
theorem half_ceiling (i : ℕ) : (((i + 1) / 2 : ℕ) : ℤ) = ⌈(i : ℚ) / 2⌉ := by
  have h := ceiling_division_formula (i : ℤ) 2 (by decide)
  norm_num only [Nat.cast_ofNat, Int.cast_natCast] at h
  rw [← h]
  have hnum : (i : ℤ) + 2 - 1 = (i : ℤ) + 1 := by omega
  rw [hnum]
  norm_cast


/-- The sharp core count agrees literally with the ceiling/binomial formula. -/
theorem coreShadow_eq_ceiling (c i : ℕ) :
    coreShadow c i = coreB c -
      (((coreP c - (⌈(i : ℚ) / 2⌉).toNat + 1).choose 2 : ℕ) : ℤ) := by
  rw [← half_ceiling, Int.toNat_natCast]
  exact coreShadow_eq_binomial c i

theorem edgeWidth_eq_difference (edge : Fin 6) :
    edgeWidth edge = (edgeRight edge : ℤ) - (edgeLeft edge : ℤ) := by
  fin_cases edge <;> decide

/-- All ordered pairs of distinct prefix ranks occur in the six-edge index. -/
theorem edge_complete (u v : Fin 4) (h : u < v) :
    ∃ edge : Fin 6, edgeLeft edge = u.val ∧ edgeRight edge = v.val := by
  fin_cases u <;> fin_cases v <;> simp only [Fin.lt_def] at h
  all_goals first | omega | decide

/-- The source-range inequalities are exactly feasibility of the intermediate
rational layer in `[0,w]`, with `1 ≤ d < a`. -/
theorem eligible_iff_intermediate (m c i : ℕ) (edge : Fin 6) (d : ℤ) :
    Eligible m c i edge d ↔ 1 ≤ d ∧ d < (totalA m c : ℤ) ∧
      0 ≤ edgeIntermediate (parameters m c i) edge d ∧
      edgeIntermediate (parameters m c i) edge d ≤ (freeW m c : ℚ) := by
  have hK : (0 : ℚ) < edgeWidth edge := by exact_mod_cast edgeWidth_pos edge
  have hKq : (edgeWidth edge : ℚ) = (edgeRight edge : ℚ) - (edgeLeft edge : ℚ) := by
    exact_mod_cast edgeWidth_eq_difference edge
  have hzlo : 0 ≤ edgeIntermediate (parameters m c i) edge d ↔
      (i : ℤ) + (edgeLeft edge : ℤ) * (freeW m c : ℤ) ≤ d := by
    unfold edgeIntermediate parameters
    rw [le_div_iff₀ hK]
    norm_num only [zero_mul, Int.cast_natCast]
    constructor <;> intro h
    · have h' : (i : ℚ) + (edgeLeft edge : ℚ) * (freeW m c : ℚ) ≤ (d : ℚ) := by linarith
      exact_mod_cast h'
    · have h' : (i : ℚ) + (edgeLeft edge : ℚ) * (freeW m c : ℚ) ≤ (d : ℚ) := by exact_mod_cast h
      linarith
  have hzhi : edgeIntermediate (parameters m c i) edge d ≤ (freeW m c : ℚ) ↔
      d ≤ (i : ℤ) + (edgeRight edge : ℤ) * (freeW m c : ℤ) := by
    unfold edgeIntermediate parameters
    rw [div_le_iff₀ hK, hKq]
    norm_num only [Int.cast_natCast]
    constructor <;> intro h
    · have h' : (d : ℚ) ≤ (i : ℚ) + (edgeRight edge : ℚ) * (freeW m c : ℚ) := by nlinarith
      exact_mod_cast h'
    · have h' : (d : ℚ) ≤ (i : ℚ) + (edgeRight edge : ℚ) * (freeW m c : ℚ) := by exact_mod_cast h
      nlinarith
  simp only [Eligible, hzlo, hzhi]

/-- The three rational edge layers have the requested total source dimension. -/
theorem edge_dimension (p : Parameters) (edge : Fin 6) (d : ℤ) :
    let z := edgeIntermediate p edge d
    (p.i : ℚ) + edgeLayer p.w z (edgeLeft edge) (edgeRight edge) 1 +
      edgeLayer p.w z (edgeLeft edge) (edgeRight edge) 2 +
      edgeLayer p.w z (edgeLeft edge) (edgeRight edge) 3 = (d : ℚ) := by
  fin_cases edge <;>
    norm_num [edgeIntermediate, edgeLeft, edgeRight, edgeWidth, edgeLayer] <;> ring

/-- Feasible intermediate values give the ordered three-layer simplex constraints. -/
theorem edge_layers_ordered (w : ℤ) (z : ℚ) (edge : Fin 6)
    (hzlo : 0 ≤ z) (hzhi : z ≤ (w : ℚ)) :
    0 ≤ edgeLayer w z (edgeLeft edge) (edgeRight edge) 3 ∧
    edgeLayer w z (edgeLeft edge) (edgeRight edge) 3 ≤
      edgeLayer w z (edgeLeft edge) (edgeRight edge) 2 ∧
    edgeLayer w z (edgeLeft edge) (edgeRight edge) 2 ≤
      edgeLayer w z (edgeLeft edge) (edgeRight edge) 1 ∧
    edgeLayer w z (edgeLeft edge) (edgeRight edge) 1 ≤ (w : ℚ) := by
  have hw : (0 : ℚ) ≤ w := le_trans hzlo hzhi
  fin_cases edge <;> simp_all [edgeLeft, edgeRight, edgeLayer]

end Quartic.SharpCertificate
