module

public import Froberg.UniformRestoredCountedQuadratic
public import Froberg.ActualRestoredSlots
public import Froberg.ExactOuterLimit

@[expose] public section

/-! The exact manuscript counts, including restored pure slots and any
fixed extra columns, attain the genuine full-parameter C.2 row open. -/
noncomputable section
namespace Froberg.PreparedParameters
open Froberg Module Filter MvPolynomial
open scoped Topology

theorem uniform_exact_counts_restored_quadratic_open {d k h lo : ℕ}
    (hd : 3≤d) (hh : 0<h) (upper : Bool) (a f e : ℕ → ℕ) (extra : ℕ)
    (hc : ∀ᶠ n in atTop,ExactCountConditions d k h lo n (a n) (f n) (e n) upper) :
    ∀ᶠ n : ℕ in atTop, ∀ (K : Type) [Field K] [Infinite K], ∀ (O : ℕ → Submodule K (Poly K h))
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
  let u := (h+d-1).choose d
  let r := fun n => Fintype.card (Label (upperCount n d) (allEvenIndices d)
    (allEvenCount d h n (e n+u+extra)))
  have hS : Tendsto (fun n : ℕ => (r n : ℝ)/(n : ℝ)^d)
      atTop (𝓝 (criticalRatio d/(d.factorial : ℝ))) := by
    simpa only [r,Nat.add_assoc] using
      allEvenLabel_count_limit hd h (u+extra) e (hc.mono fun n hn => hn.quadratic_upper)
  have hF := exact_conditions_outer_limit hd upper a f e hc
  filter_upwards [eventually_uniform_restored_counted_quadratic_separation hd hh r f hS hF]
    with n hn
  intro K _ _ O hO c T o ho
  have H := hn K (upperCount n d) c (allEvenIndices d)
    (allEvenCount d h n (e n+u+extra)) O hO
    (Fintype.equivFin _).symm (Fin (outerColumnCount d h)) (Fintype.card_fin _) T o ho
  let P : ℕ → Prop := fun v =>
    letI : Module.Finite K (Space n d (upperCount n d) (allEvenIndices d)
      (allEvenCount d h n (e n+v+extra)) O) := finite_space hO
    ∃ D : MvPolynomial (Fin (finrank K (RestoredOuterSpace n d (upperCount n d) (f n)
      (allEvenIndices d) (allEvenCount d h n (e n+v+extra)) O))) K,
      (∃ p : RestoredOuterSpace n d (upperCount n d) (f n)
        (allEvenIndices d) (allEvenCount d h n (e n+v+extra)) O,
        eval ((Module.finBasis K _).equivFun p) D≠0) ∧
      ∀ p : RestoredOuterSpace n d (upperCount n d) (f n)
        (allEvenIndices d) (allEvenCount d h n (e n+v+extra)) O,
        eval ((Module.finBasis K _).equivFun p) D≠0 →
          QuadraticSeparated T (restoredC2Projection (Fintype.equivFin _).symm p)
  have hu : u=actualRestoredPureCount K d h := (finrank_forms K h d hh).symm
  exact Eq.mp (congrArg P hu) (show P u from H)

end Froberg.PreparedParameters
