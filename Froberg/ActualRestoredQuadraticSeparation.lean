module

public import Froberg.RestoredCountedQuadraticSeparation
public import Froberg.ActualRestoredSlots
public import Froberg.ExactOuterLimit

@[expose] public section

/-! The exact manuscript counts, including restored pure slots and any
fixed extra columns, attain the genuine full-parameter C.2 row open. -/
noncomputable section
namespace Froberg.PreparedParameters
open Froberg Module Filter MvPolynomial
open scoped Topology
variable {K : Type} [Field K] [Infinite K]

theorem exact_counts_restored_quadratic_open {d k h lo : ℕ}
    (hd : 3≤d) (hh : 0<h) (upper : Bool) (a f e : ℕ → ℕ) (extra : ℕ)
    (hc : ∀ᶠ n in atTop,ExactCountConditions d k h lo n (a n) (f n) (e n) upper) :
    ∀ᶠ n : ℕ in atTop, ∀ (O : ℕ → Submodule K (Poly K h))
      (hO : ∀ j∈allEvenIndices d,O j≤Forms K h j) (c : ℕ)
      (T : Poly K h →ₗ[K] (Fin c → K))
      (o : Fin (outerColumnCount d h) → Forms K h 1),
      LinearIndependent K (fun p => T (pairProducts (fun i => (o i).val) p)) →
      letI : Module.Finite K (Space n d (upperCount n d) (allEvenIndices d)
        (actualRestoredCounts K d h n (e n) extra) O) := finite_space hO
      ∃ D : MvPolynomial (Fin (finrank K (RestoredOuterSpace n d (upperCount n d) (f n)
        (allEvenIndices d) (actualRestoredCounts K d h n (e n) extra) O))) K,
        (∃ p : RestoredOuterSpace n d (upperCount n d) (f n)
          (allEvenIndices d) (actualRestoredCounts K d h n (e n) extra) O,
          eval ((Module.finBasis K _).equivFun p) D≠0) ∧
        ∀ p : RestoredOuterSpace n d (upperCount n d) (f n)
          (allEvenIndices d) (actualRestoredCounts K d h n (e n) extra) O,
          eval ((Module.finBasis K _).equivFun p) D≠0 →
            QuadraticSeparated T (restoredC2Projection
              (actualRestoredIndex K d h n (e n) extra) p) := by
  have hS := allEvenLabel_count_limit hd h (actualRestoredPureCount K d h+extra) e
    (hc.mono fun n hn => hn.quadratic_upper)
  have hS' : Tendsto (fun n : ℕ => (actualRestoredSize K d h n (e n) extra : ℝ)/(n : ℝ)^d)
      atTop (𝓝 (criticalRatio d/(d.factorial : ℝ))) := by
    simpa only [actualRestoredSize,ActualRestoredLabel,actualRestoredCounts,Nat.add_assoc] using hS
  have hF := exact_conditions_outer_limit hd upper a f e hc
  filter_upwards [eventually_restored_counted_quadratic_separation (K := K) hd hh
    (fun n => actualRestoredSize K d h n (e n) extra) f hS' hF] with n hn
  intro O hO c T o ho
  exact hn (upperCount n d) c (allEvenIndices d)
    (actualRestoredCounts K d h n (e n) extra) O hO
    (actualRestoredIndex K d h n (e n) extra) (Fin (outerColumnCount d h))
    (Fintype.card_fin _) T o ho

end Froberg.PreparedParameters
