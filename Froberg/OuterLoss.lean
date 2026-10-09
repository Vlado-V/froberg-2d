module

public import Froberg.OuterShadow
public import Froberg.ProjectionEndpoints
public import Froberg.ExceptionBudget

@[expose] public section

/-! The uniform exceptional loss for the actual outer-module shadow. -/
noncomputable section
namespace Froberg.AttachedMultiplication
open Module Finset Quartic.HomogeneousCoefficientCoordinates
variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I] {n s h : ℕ}
variable (e : I → Fin n →₀ ℕ) (v : I → Fin h → K)

/-- Targets where the canonical projection of one source-fiber subspace is deficient. -/
def deficientTargets
    (C : (a : Exponent n s) → Submodule K ((Fin h → K) ⧸ relationFiber e v a.val))
    (a : Exponent n s) : Finset (Exponent n (s+(s+1))) := by
  classical
  exact univ.filter (fun b => ∃ hab : a.val ≤ b.val,
    finrank K ((C a).map (fiberProjection e v hab)) <
      min (finrank K (C a)) (finrank K ((Fin h → K) ⧸ relationFiber e v b.val)))

theorem card_deficientTargets_le (hn : 0 < n) (he : ∀ i, (e i).degree = s)
    (hv : ∀ S : Finset I, S.card ≤ h → LinearIndependent K (fun i : S => v i.val))
    (hm : MixedExterior.UniversalMixedPosition v)
    (hsize : ∀ b : Exponent n (s+(s+1)), (labelsBelow e b.val).card ≤ h)
    (C : (a : Exponent n s) → Submodule K ((Fin h → K) ⧸ relationFiber e v a.val))
    (a : Exponent n s) :
    (deficientTargets e v C a).card ≤ (h*2^h)*(n+s-1).choose s := by
  classical
  let E := deficientTargets e v C a
  have hc : (E.image Subtype.val).card = E.card :=
    card_image_of_injOn (fun _ _ _ _ hh => Subtype.ext hh)
  rw [← hc]
  have hE : ∀ b ∈ E.image Subtype.val, b.degree = 2*s+1 ∧ a.val ≤ b := by
    intro b hb
    obtain ⟨c,hc,rfl⟩ := mem_image.mp hb
    obtain ⟨hab,_⟩ := (mem_filter.mp hc).2
    exact ⟨by have hh := c.property; omega,hab⟩
  apply card_deficient_quotient_projections_le hn e he v hv hm a.val a.property
    (C a) (E.image Subtype.val) hE
  · intro b hb
    obtain ⟨c,hc,rfl⟩ := mem_image.mp hb
    exact hsize c
  · intro b hb
    obtain ⟨c,hc,rfl⟩ := mem_image.mp hb
    obtain ⟨hab,hfail⟩ := (mem_filter.mp hc).2
    exact hfail

/-- The ideal maximal-rank shadow in one target fiber. -/
def idealShadow
    (C : (a : Exponent n s) → Submodule K ((Fin h → K) ⧸ relationFiber e v a.val))
    (b : Exponent n (s+(s+1))) : ℕ := by
  classical
  exact univ.sup (fun a : Exponent n s => if a.val ≤ b.val then
    min (finrank K (C a)) (finrank K ((Fin h → K) ⧸ relationFiber e v b.val)) else 0)

/-- Every divisible source contributes its maximal possible projection rank
to the ideal shadow. -/
theorem min_le_idealShadow
    (C : (a : Exponent n s) → Submodule K ((Fin h → K) ⧸ relationFiber e v a.val))
    (a : Exponent n s) (b : Exponent n (s+(s+1))) (hab : a.val ≤ b.val) :
    min (finrank K (C a)) (finrank K ((Fin h → K) ⧸ relationFiber e v b.val)) ≤
      idealShadow e v C b := by
  classical
  have hh := Finset.le_sup (f := fun a : Exponent n s => if a.val ≤ b.val then
    min (finrank K (C a)) (finrank K ((Fin h → K) ⧸ relationFiber e v b.val)) else 0)
      (Finset.mem_univ a)
  unfold idealShadow
  simpa only [ite_eq_left hab] using hh

/-- Coarse target capacities are valid in the same ideal lower bound. -/
theorem coarse_min_le_idealShadow
    (C : (a : Exponent n s) → Submodule K ((Fin h → K) ⧸ relationFiber e v a.val))
    (a : Exponent n s) (b : Exponent n (s+(s+1))) (hab : a.val ≤ b.val)
    (c : ℕ) (hc : c ≤ finrank K ((Fin h → K) ⧸ relationFiber e v b.val)) :
    min (finrank K (C a)) c ≤ idealShadow e v C b :=
  (min_le_min_left _ hc).trans (min_le_idealShadow e v C a b hab)

theorem idealShadow_le (C : (a : Exponent n s) → Submodule K
    ((Fin h → K) ⧸ relationFiber e v a.val)) (b : Exponent n (s+(s+1))) :
    idealShadow e v C b ≤ h := by
  classical
  apply Finset.sup_le_iff.mpr
  intro a _
  split_ifs
  · exact (min_le_right _ _).trans (by simpa using (relationFiber e v b.val).finrank_quotient_le)
  · exact Nat.zero_le _

/-- Away from the union of the proper source-fiber exceptions, the actual
shadow dominates the ideal one. -/
theorem idealShadow_le_actual_of_no_exceptions
    (C : (a : Exponent n s) → Submodule K ((Fin h → K) ⧸ relationFiber e v a.val))
    (b : Exponent n (s+(s+1)))
    (hgood : ∀ a, 0 < finrank K (C a) →
      finrank K (C a) < finrank K ((Fin h → K) ⧸ relationFiber e v a.val) →
      b ∉ deficientTargets e v C a) :
    idealShadow e v C b ≤ finrank K (fiberShadow e v C b) := by
  classical
  apply Finset.sup_le_iff.mpr
  intro a _
  split_ifs with hab
  · apply le_trans _ (projection_finrank_le_shadow e v C a b hab)
    by_contra hn
    have hfail := lt_of_not_ge hn
    have hproper := deficient_projection_implies_proper (fiberProjection e v hab)
      (Submodule.factor_surjective (relationFiber_mono e v hab)) (C a) hfail
    exact hgood a hproper.1 hproper.2 (mem_filter.mpr ⟨mem_univ _,hab,hfail⟩)
  · exact Nat.zero_le _

/-- Summing the actual uniform exception bound gives the required smaller-of-
dimension-and-codimension loss. All shadows and images are actual quotient spaces. -/
theorem idealShadow_sum_le_actual_image_add_loss (hn : 0 < n)
    (he : ∀ i, (e i).degree = s)
    (hv : ∀ S : Finset I, S.card ≤ h → LinearIndependent K (fun i : S => v i.val))
    (hm : MixedExterior.UniversalMixedPosition v)
    (hsize : ∀ b : Exponent n (s+(s+1)), (labelsBelow e b.val).card ≤ h)
    (C : (a : Exponent n s) → Submodule K ((Fin h → K) ⧸ relationFiber e v a.val)) :
    (∑ b, idealShadow e v C b) ≤
      finrank K (Quartic.BilinearImage.image (fiberMultiply (d := s+1) e v he)
        (Submodule.pi Set.univ C)) +
      h * ((h*2^h)*(n+s-1).choose s) *
        min (∑ a, finrank K (C a))
          ((∑ a : Exponent n s, finrank K ((Fin h → K) ⧸ relationFiber e v a.val)) -
            ∑ a, finrank K (C a)) := by
  have hbudget := ExceptionBudget.sum_loss_le
    (fun a : Exponent n s => finrank K ((Fin h → K) ⧸ relationFiber e v a.val))
    (fun a => finrank K (C a)) (fun a => Submodule.finrank_le (C a))
    (deficientTargets e v C) ((h*2^h)*(n+s-1).choose s) h
    (fun a _ _ => card_deficientTargets_le e v hn he hv hm hsize C a)
    (idealShadow e v C) (fun b => finrank K (fiberShadow e v C b))
    (idealShadow_le e v C) (idealShadow_le_actual_of_no_exceptions e v C)
  exact hbudget.trans (Nat.add_le_add_right
    (sum_shadow_finrank_le_image (d := s+1) e v he C) _)

end Froberg.AttachedMultiplication
