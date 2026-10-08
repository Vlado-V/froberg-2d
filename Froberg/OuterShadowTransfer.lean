import Froberg.OuterProfileDimensions
import Froberg.OuterModel

/-! Applying the numerical monomial shadow bound to all actual subspaces
of the attached polynomial quotient. -/
noncomputable section
set_option maxHeartbeats 1200000
namespace Froberg
open Module Finset MonomialExpansion OuterInjection
open Quartic.HomogeneousCoefficientCoordinates

/-- The two degree conventions used by the geometric and counting files agree. -/
def outerTargetExponentEquiv (n s : ℕ) : Degree n (2*s+1) ≃ Exponent n (s+(s+1)) where
  toFun β := ⟨β.val, by have h := degree_val β; omega⟩
  invFun β := ⟨β.val, mem_exponents.mpr (by have h := β.property; omega)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem actual_outer_growth_of_exponent_shadow {K : Type*} [Field K]
    {k a z s h : ℕ} (hh : h=k*(2*s+1).choose s) (hn : 0 < a+z)
    (v : Labels k a s → Fin h → K)
    (hv : ∀ U : Finset (Labels k a s), U.card ≤ h → LinearIndependent K (fun i : U => v i.val))
    (hm : MixedExterior.UniversalMixedPosition v) (R g : ℝ)
    (hbase : ∀ (ell : Degree (a+z) s → ℝ) (b : Degree (a+z) (2*s+1) → ℝ),
      (∀ α, 0 ≤ ell α ∧ ell α ≤ (k : ℝ)*(profileAmbientCapacity s-
        if (corePart α.val).degree=s then 1 else 0)) →
      (∀ β, 0 ≤ b β) →
      (∀ α β, α.val ≤ β.val →
        min ((k : ℝ)*(profileAmbientCapacity s-((corePart β.val).degree.choose s : ℝ))) (ell α) ≤ b β) →
      R*(∑ α, ell α)+g*min (∑ α, ell α)
        ((k : ℝ)*(∑ i, finiteSourceProfile (profileAmbientCapacity s) s a z i)-∑ α, ell α) ≤ ∑ β, b β) :
    ∀ L : Submodule K ((Fin h → Forms K (a+z) s) ⧸
      AttachedMultiplication.relationSpace (d := 0) (coreExponent z) v (coreExponent_degree z)),
      R*(finrank K L : ℝ)+(g-(h : ℝ)*((h*2^h)*(a+z+s-1).choose s))*
        min (finrank K L : ℝ)
          ((finrank K ((Fin h → Forms K (a+z) s) ⧸
            AttachedMultiplication.relationSpace (d := 0) (coreExponent z) v (coreExponent_degree z)) : ℝ)-finrank K L) ≤
        (finrank K (AttachedMultiplication.outerImage (d := s+1) (coreExponent z) v (coreExponent_degree z) L) : ℝ) := by
  classical
  have hbound (C : (α : Exponent (a+z) s) →
      Submodule K ((Fin h → K) ⧸ AttachedMultiplication.relationFiber (coreExponent z) v α.val)) :
      R*(∑ α, finrank K (C α) : ℕ)+g*
        (min (∑ α, finrank K (C α))
          (finrank K ((Fin h → Forms K (a+z) s) ⧸
            AttachedMultiplication.relationSpace (d := 0) (coreExponent z) v (coreExponent_degree z))-
            ∑ α, finrank K (C α)) : ℕ) ≤
        (∑ β, AttachedMultiplication.idealShadow (coreExponent z) v C β : ℕ) := by
    let ell := fun α : Degree (a+z) s => (finrank K (C (degreeExponentEquiv (a+z) s α)) : ℝ)
    let b := fun β : Degree (a+z) (2*s+1) =>
      (AttachedMultiplication.idealShadow (coreExponent z) v C (outerTargetExponentEquiv (a+z) s β) : ℝ)
    have hl (α : Degree (a+z) s) : 0 ≤ ell α ∧ ell α ≤
        (k : ℝ)*(profileAmbientCapacity s-if (corePart α.val).degree=s then 1 else 0) := by
      refine ⟨Nat.cast_nonneg _, ?_⟩
      rw [← source_capacity_real hh v hv α]
      dsimp only [ell]
      exact_mod_cast Submodule.finrank_le (C (degreeExponentEquiv (a+z) s α))
    have hb (β : Degree (a+z) (2*s+1)) : 0 ≤ b β := Nat.cast_nonneg _
    have hmin (α : Degree (a+z) s) (β : Degree (a+z) (2*s+1)) (hab : α.val ≤ β.val) :
        min ((k : ℝ)*(profileAmbientCapacity s-((corePart β.val).degree.choose s : ℝ))) (ell α) ≤ b β := by
      have hminNat := AttachedMultiplication.min_le_idealShadow (coreExponent z) v C
        (degreeExponentEquiv (a+z) s α) (outerTargetExponentEquiv (a+z) s β) hab
      have hr : min (ell α)
          (finrank K ((Fin h → K) ⧸ AttachedMultiplication.relationFiber (coreExponent z) v β.val) : ℝ) ≤ b β := by
        dsimp only [ell,b]
        exact_mod_cast hminNat
      rw [min_comm]
      exact (min_le_min_left (ell α) (target_capacity_real_lower hh v hv β)).trans hr
    have hbnd := hbase ell b hl hb hmin
    have hs : (∑ α : Degree (a+z) s, ell α) = (∑ α, finrank K (C α) : ℕ) := by
      rw [Nat.cast_sum]
      exact (degreeExponentEquiv (a+z) s).sum_comp (fun α => (finrank K (C α) : ℝ))
    have ht : (∑ β : Degree (a+z) (2*s+1), b β) =
        (∑ β, AttachedMultiplication.idealShadow (coreExponent z) v C β : ℕ) := by
      rw [Nat.cast_sum]
      exact (outerTargetExponentEquiv (a+z) s).sum_comp (fun β =>
        (AttachedMultiplication.idealShadow (coreExponent z) v C β : ℝ))
    have hle : (∑ α, finrank K (C α)) ≤ finrank K ((Fin h → Forms K (a+z) s) ⧸
        AttachedMultiplication.relationSpace (d := 0) (coreExponent z) v (coreExponent_degree z)) := by
      rw [← AttachedMultiplication.sum_source_fiber_finrank (coreExponent z) v (coreExponent_degree z)]
      exact sum_le_sum fun α _ => Submodule.finrank_le (C α)
    rw [hs,ht,← outer_source_dimension_profile hh v hv] at hbnd
    simpa only [Nat.cast_min,Nat.cast_sub hle] using hbnd
  have hsize (β : Exponent (a+z) (s+(s+1))) :
      (AttachedMultiplication.labelsBelow (coreExponent (k := k) (s := s) z) β.val).card ≤ h := by
    apply (core_labelsBelow_card_le β.val).trans
    rw [β.property,show s+(s+1)=2*s+1 by omega,← hh]
  have hactual := AttachedMultiplication.uniform_outer_growth_of_ideal_bound
    (coreExponent z) v (coreExponent_degree z) hn hv hm hsize R
    (g-(h : ℝ)*((h*2^h)*(a+z+s-1).choose s)) (fun C => by
      convert hbound C using 1 <;> ring)
  intro L
  have hL := hactual L
  have hle := Submodule.finrank_le L
  simpa only [Nat.cast_min,Nat.cast_sub hle] using hL

end Froberg
