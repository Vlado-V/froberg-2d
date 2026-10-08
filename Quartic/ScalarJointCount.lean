import Quartic.UniformScalar

/-!
# Scalar incidence bounds imply the strict joint chart budget

The joint parameter count includes one shared child tuple, the auxiliary
cokernel columns, and both successive groups of motions. Natural-number
subtraction expresses the clipped codimensions exactly. This is an arithmetic
bridge, not an assertion of generic fiber dimensions or motion rank.
-/
namespace Quartic.ScalarJointCount
open UniformScalar

 theorem cast_sub_max (u v : ℕ) : ((u-v : ℕ) : ℝ) = max ((u : ℝ)-v) 0 := by
  by_cases h : v ≤ u
  · rw [Nat.cast_sub h,max_eq_left]
    exact sub_nonneg.mpr (by exact_mod_cast h)
  · have h' : u ≤ v := by omega
    rw [Nat.sub_eq_zero_of_le h',Nat.cast_zero,max_eq_right]
    exact sub_nonpos.mpr (by exact_mod_cast h')

/-- The two scalar alternatives both imply the strict dimension inequality
needed by the three successive actual kernel constraints. -/
theorem strict_joint_budget (a T q d E k h c : ℕ)
    (hd : d ≤ a) (hE : E < T) (hqa : q*a ≤ T)
    (hscalar :
      covectorR ((T-q*a : ℕ) : ℝ) E q a d < 0 ∨
      covectorR ((T-q*a : ℕ) : ℝ) E q a d - codimensionR k h c d ≤
        max (((T-q*a : ℕ) : ℝ) - ((k+h : ℕ) : ℝ)) 0 - 1) :
    d*(a-d)+(T-E)-1 < q*(a-d) + (k-4*d) + (h-c*d) + (T-q*a-(k+h)) := by
  have hpos : 1 ≤ d*(a-d)+(T-E) := by omega
  have hcov : covectorR ((T-q*a : ℕ) : ℝ) E q a d =
      ((d*(a-d)+(T-E)-1 : ℕ) : ℝ) - ((q*(a-d) : ℕ) : ℝ) := by
    rw [Nat.cast_sub hpos,Nat.cast_add,Nat.cast_mul,Nat.cast_sub hd,
      Nat.cast_sub hE.le,Nat.cast_one,Nat.cast_mul,Nat.cast_sub hd,Nat.cast_sub hqa]
    push_cast
    unfold covectorR
    ring
  have hcod : codimensionR k h c d = ((k-4*d : ℕ) : ℝ) + ((h-c*d : ℕ) : ℝ) := by
    rw [cast_sub_max,cast_sub_max]
    push_cast
    rfl
  have he : max (((T-q*a : ℕ) : ℝ) - ((k+h : ℕ) : ℝ)) 0 =
      ((T-q*a-(k+h) : ℕ) : ℝ) := (cast_sub_max _ _).symm
  rw [hcov,hcod,he] at hscalar
  have hreal : ((d*(a-d)+(T-E)-1 : ℕ) : ℝ) <
      ((q*(a-d) + (k-4*d) + (h-c*d) + (T-q*a-(k+h)) : ℕ) : ℝ) := by
    simp only [Nat.cast_add]
    have hk0 : (0 : ℝ) ≤ ((k-4*d : ℕ) : ℝ) := Nat.cast_nonneg _
    have hh0 : (0 : ℝ) ≤ ((h-c*d : ℕ) : ℝ) := Nat.cast_nonneg _
    have he0 : (0 : ℝ) ≤ ((T-q*a-(k+h) : ℕ) : ℝ) := Nat.cast_nonneg _
    rcases hscalar with hn | hc
    · linarith
    · linarith
  exact_mod_cast hreal

end Quartic.ScalarJointCount
