import Froberg.GeneralExceptionalCount
import Froberg.WeightedProjectionGrowth
import Froberg.ExponentWeights
import Froberg.OuterInitialFibers
import Froberg.OuterShadow

/-! The uniform intermediate-layer shadow B.11 in actual attached polynomial
quotients, for arbitrary source and multiplier degrees. -/
noncomputable section
namespace Froberg.AttachedMultiplication
open Module Finset Quartic.HomogeneousCoefficientCoordinates
variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I] {n s d h : ℕ}
variable (e : I → Fin n →₀ ℕ) (v : I → Fin h → K)

def generalDeficientTargets
    (C : (a : Exponent n s) → Submodule K ((Fin h → K) ⧸ relationFiber e v a.val))
    (a : Exponent n s) : Finset (Exponent n (s+d)) := by
  classical
  exact univ.filter (fun b => ∃ hab : a.val ≤ b.val,
    finrank K ((C a).map (fiberProjection e v hab)) <
      min (finrank K (C a)) (finrank K ((Fin h → K) ⧸ relationFiber e v b.val)))

theorem card_generalDeficientTargets_le (hn : 0 < n) (he : ∀ i, (e i).degree = s)
    (hv : ∀ S : Finset I, S.card ≤ h → LinearIndependent K (fun i : S => v i.val))
    (hm : MixedExterior.UniversalMixedPosition v)
    (hsize : ∀ b : Exponent n (s+d), (labelsBelow e b.val).card ≤ h)
    (C : (a : Exponent n s) → Submodule K ((Fin h → K) ⧸ relationFiber e v a.val))
    (a : Exponent n s) :
    (generalDeficientTargets (d := d) e v C a).card ≤
      (h*2^h)*(n+(d-1)-1).choose (d-1) := by
  classical
  let E := generalDeficientTargets (d := d) e v C a
  have hc : (E.image Subtype.val).card = E.card :=
    card_image_of_injOn (fun _ _ _ _ hh => Subtype.ext hh)
  rw [← hc]
  have hE : ∀ b ∈ E.image Subtype.val, b.degree = s+d ∧ a.val ≤ b := by
    intro b hb
    obtain ⟨c,hc,rfl⟩ := mem_image.mp hb
    obtain ⟨hab,_⟩ := (mem_filter.mp hc).2
    exact ⟨c.property,hab⟩
  apply card_deficient_quotient_projections_general hn e he v hv hm a.val a.property
    (C a) (E.image Subtype.val) hE
  · intro b hb
    obtain ⟨c,hc,rfl⟩ := mem_image.mp hb
    exact hsize c
  · intro b hb
    obtain ⟨c,hc,rfl⟩ := mem_image.mp hb
    obtain ⟨hab,hfail⟩ := (mem_filter.mp hc).2
    exact hfail

/-- Weighted incidence on the actual quotient fibers gives the intermediate
shadow, with an explicit O(n^(d-1)) error per source dimension. -/
theorem general_fiber_shadow (hn : 0 < n) (he : ∀ i, (e i).degree = s)
    (hv : ∀ S : Finset I, S.card ≤ h → LinearIndependent K (fun i : S => v i.val))
    (hm : MixedExterior.UniversalMixedPosition v) (B : ℕ) (hB : B ≤ h)
    (hsize : ∀ b : Exponent n (s+d), (labelsBelow e b.val).card ≤ B)
    (C : (a : Exponent n s) → Submodule K ((Fin h → K) ⧸ relationFiber e v a.val)) :
    (h-B)*(n+s+d-1).choose d*(∑ a, finrank K (C a)) ≤
      h*(s+d).choose s*(finrank K (Quartic.BilinearImage.image (fiberMultiply (d := d) e v he)
        (Submodule.pi Set.univ C)) +
        ((h*2^h)*(n+(d-1)-1).choose (d-1))*(∑ a, finrank K (C a))) := by
  classical
  have hh := WeightedProjectionGrowth.weighted_sum
    (fun (a : Exponent n s) (b : Exponent n (s+d)) => MonomialExpansion.weight b.val a.val)
    (fun a => finrank K (C a)) (fun b => finrank K (fiberShadow e v C b))
    (generalDeficientTargets (d := d) e v C) h B ((n+s+d-1).choose d) ((s+d).choose s)
    ((h*2^h)*(n+(d-1)-1).choose (d-1))
    (MonomialExpansion.target_weight_sum_exponent hn)
    (fun b => MonomialExpansion.source_weight_sum_exponent b s)
    (card_generalDeficientTargets_le e v hn he hv hm (fun b => (hsize b).trans hB) C) ?_
  · exact hh.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right
      (sum_shadow_finrank_le_image (d := d) e v he C) _))
  intro a b hb
  by_cases hw : MonomialExpansion.weight b.val a.val = 0
  · simp [hw]
  have hab := (MonomialExpansion.weight_ne_zero_iff b.val a.val).mp hw
  have hmin : min (finrank K (C a)) (finrank K ((Fin h → K) ⧸ relationFiber e v b.val)) ≤
      finrank K ((C a).map (fiberProjection e v hab)) := by
    by_contra hbad
    apply hb
    exact mem_filter.mpr ⟨mem_univ _,hab,lt_of_not_ge hbad⟩
  have hc : h-B ≤ finrank K ((Fin h → K) ⧸ relationFiber e v b.val) := by
    rw [Submodule.finrank_quotient,relationFiber_eq_blockSpan,
      MixedExterior.blockSpan_finrank v _ (hv _ ((hsize b).trans hB)),Module.finrank_fin_fun]
    exact Nat.sub_le_sub_left (hsize b) h
  have hell : finrank K (C a) ≤ h := (C a).finrank_le.trans (by
    simpa using (relationFiber e v a.val).finrank_quotient_le)
  have hfrac := WeightedProjectionGrowth.capacity_fraction hell hc
    (hmin.trans (projection_finrank_le_shadow e v C a b hab))
  have hm := Nat.mul_le_mul_left (MonomialExpansion.weight b.val a.val) hfrac
  simpa only [mul_assoc,mul_comm,mul_left_comm] using hm

/-- The full B.11 estimate for every actual source subspace. In divided form
its main term is (h-B)/h times the usual normalized monomial growth. -/
theorem general_outer_shadow (hn : 0 < n) (he : ∀ i, (e i).degree = s)
    (hv : ∀ S : Finset I, S.card ≤ h → LinearIndependent K (fun i : S => v i.val))
    (hm : MixedExterior.UniversalMixedPosition v) (B : ℕ) (hB : B ≤ h)
    (hsize : ∀ b : Exponent n (s+d), (labelsBelow e b.val).card ≤ B)
    (L : Submodule K ((Fin h → Forms K n s) ⧸ relationSpace (d := 0) e v he)) :
    (h-B)*(n+s+d-1).choose d*finrank K L ≤
      h*(s+d).choose s*(finrank K (outerImage (d := d) e v he L) +
        ((h*2^h)*(n+(d-1)-1).choose (d-1))*finrank K L) := by
  obtain ⟨C,hCdim,hCimage⟩ := exists_initial_monomial_fibers (d := d) e v he L
  have hh := general_fiber_shadow (d := d) e v hn he hv hm B hB hsize C
  rw [hCdim] at hh
  exact hh.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right hCimage _))

end Froberg.AttachedMultiplication
