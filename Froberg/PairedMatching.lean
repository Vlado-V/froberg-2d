import Froberg.PairedFibers

/-! Matching targets and their concrete factorizations in each paired-variable fiber. -/
noncomputable section
namespace Froberg.PairedMonomials.ProductFiber
open Finset ProductFibers
variable {X : Type*} [Fintype X] [DecidableEq X] {s : ℕ}

/-- A matched target scheme, including the xy doubled indices. -/
structure Targets (F : ProductFiber X s) (a : ℕ) where
  xy : Finset X
  xy_subset : xy ⊆ F.doubled
  size : ℕ
  total : size + xy.card = 2*a
  matchTo : F.Columns → SizedSubset F.single size
  injective : Function.Injective matchTo
  bounds : ∀ p,
    ((matchTo p).1 ∩ p.out.1).card ≤ a ∧ ((matchTo p).1 ∩ p.out.1ᶜ).card ≤ a

private theorem adj_out {R : Type*} [Fintype R] [DecidableEq R] {t m : ℕ}
    (hR : Fintype.card R = 2*t) (allowed : ℕ → Prop)
    (p : Partition hR) (D : SizedSubset R m) :
    Adj hR allowed p D ↔
      allowed (D.1 ∩ p.out.1).card ∧ allowed (D.1 ∩ p.out.1ᶜ).card := by
  simpa only [Quotient.out_eq] using adj_mk hR allowed p.out D

/-- All three parity cases of Lemma 4.1, uniformly packaged as concrete targets. -/
theorem targets_nonempty (F : ProductFiber X s) : Nonempty (Targets F (s / 2)) := by
  let a := s / 2
  by_cases hs : s % 2 = 0
  · obtain ⟨g,hg,hb⟩ := even_fiber_matching (a := a) (i := F.doubled.card) F.card_indices
      (by have := F.degree; simp only [a] at *; omega)
    refine ⟨⟨F.doubled, subset_rfl, F.halfSize, ?_, g, hg, ?_⟩⟩
    · have := F.degree
      simp only [a] at *
      omega
    · intro p
      have h := (adj_out F.card_indices _ p (g p)).mp (hb p)
      exact ⟨h.1.2,h.2.2⟩
  · have hodd : s = 2*a+1 := by simp only [a] at *; omega
    by_cases hi : F.doubled.card = 0
    · obtain ⟨g,hg,hb⟩ := odd_disjoint_fiber_matching (a := a) F.card_indices
        (by have := F.degree; omega)
      refine ⟨⟨∅, empty_subset _, F.halfSize-1, ?_, g, hg, ?_⟩⟩
      · have := F.degree
        simp only [card_empty]
        simp only [a] at *
        omega
      · intro p
        have h := (adj_out F.card_indices _ p (g p)).mp (hb p)
        exact ⟨h.1.le,h.2.le⟩
    · obtain ⟨x,hx⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hi)
      obtain ⟨g,hg,hb⟩ := odd_doubled_fiber_matching (a := a) (i := F.doubled.card) F.card_indices
        (by have := F.degree; omega) (by omega)
      refine ⟨⟨F.doubled.erase x, erase_subset _ _, F.halfSize, ?_, g, hg, ?_⟩⟩
      · rw [card_erase_of_mem hx]
        have := F.degree
        simp only [a] at *
        omega
      · intro p
        have h := (adj_out F.card_indices _ p (g p)).mp (hb p)
        exact ⟨h.1.2,h.2.2⟩

/-- The ambient target subset matched to a source column. -/
def Targets.subset {F : ProductFiber X s} {a : ℕ} (T : Targets F a) (p : F.Columns) : Finset X :=
  liftPart F.single (T.matchTo p).1

theorem Targets.subset_subset {F : ProductFiber X s} {a : ℕ} (T : Targets F a) (p : F.Columns) :
    T.subset p ⊆ F.single := liftPart_subset _ _

theorem Targets.subset_injective {F : ProductFiber X s} {a : ℕ} (T : Targets F a) :
    Function.Injective T.subset := by
  intro p q h
  apply T.injective
  apply Subtype.ext
  exact liftPart_injective F.single h

/-- Distinct matched source columns have distinct concrete product monomials. -/
theorem Targets.target_injective {F : ProductFiber X s} {a : ℕ} (T : Targets F a) :
    Function.Injective (fun p => targetExponent F.doubled T.xy F.single (T.subset p)) := by
  intro p q h
  apply T.subset_injective
  exact targetExponent_inj F.disjoint (T.subset_subset p) (T.subset_subset q) h

private theorem union_lift_compl (R : Finset X) (P : Finset R) :
    liftPart R P ∪ liftPart R Pᶜ = R := by
  rw [liftPart_compl]
  exact Finset.union_sdiff_of_subset (liftPart_subset R P)

/-- Explicit choices of allowed terms whose product is the matched monomial. -/
structure Factors {F : ProductFiber X s} {a : ℕ} (T : Targets F a) (p : F.Columns) where
  leftX : Finset X
  rightX : Finset X
  left_subset : leftX ⊆ (F.label (p,false)).1
  right_subset : rightX ⊆ (F.label (p,true)).1
  left_card : leftX.card = a
  right_card : rightX.card = a
  product : pairedExponent (F.label (p,false)).1 leftX +
      pairedExponent (F.label (p,true)).1 rightX =
    targetExponent F.doubled T.xy F.single (T.subset p)

/-- Each graph edge factors into actual permitted monomials. -/
theorem factors_nonempty {F : ProductFiber X s} {a : ℕ} (T : Targets F a)
    (p : F.Columns) : Nonempty (Factors T p) := by
  let P := liftPart F.single p.out.1
  let Q := liftPart F.single p.out.1ᶜ
  let D := T.subset p
  obtain ⟨E₀, hleft, hright⟩ := allocate_doubled_indices (J := T.xy)
    (T.matchTo p).1 p.out.1 a
    (by simpa only [Fintype.card_coe, (T.matchTo p).2] using T.total)
    (T.bounds p).1 (T.bounds p).2
  let E := liftPart T.xy E₀
  have hEJ : E ⊆ T.xy := liftPart_subset _ _
  have hEI : E ⊆ F.doubled := hEJ.trans T.xy_subset
  have hPI : Disjoint F.doubled P := F.disjoint.mono_right (liftPart_subset _ _)
  have hQI : Disjoint F.doubled Q := F.disjoint.mono_right (liftPart_subset _ _)
  have hPQ : Disjoint P Q := by
    dsimp [P,Q]
    rw [liftPart_compl]
    exact Finset.disjoint_left.mpr (fun _ hp hq => (Finset.mem_sdiff.mp hq).2 hp)
  have hPUQ : P ∪ Q = F.single := union_lift_compl _ _
  have hDU : D ⊆ P ∪ Q := by rw [hPUQ]; exact T.subset_subset p
  have hDP : (D ∩ P).card = ((T.matchTo p).1 ∩ p.out.1).card := by
    dsimp [D,P,Targets.subset]
    rw [← liftPart_inter, card_liftPart]
  have hDQ : (D ∩ Q).card = ((T.matchTo p).1 ∩ p.out.1ᶜ).card := by
    dsimp [D,Q,Targets.subset]
    rw [← liftPart_inter, card_liftPart]
  have hEc : E.card = E₀.card := card_liftPart _ _
  have hJEc : (T.xy \ E).card = E₀ᶜ.card := by
    dsimp [E]
    rw [← liftPart_compl, card_liftPart]
  refine ⟨⟨E ∪ (D ∩ P), (T.xy \ E) ∪ (D ∩ Q), ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact Finset.union_subset_union hEI Finset.inter_subset_right
  · exact Finset.union_subset_union (Finset.sdiff_subset.trans T.xy_subset)
      Finset.inter_subset_right
  · rw [Finset.card_union_of_disjoint (hPI.mono hEI Finset.inter_subset_right), hEc, hDP]
    exact hleft
  · rw [Finset.card_union_of_disjoint
      (hQI.mono (Finset.sdiff_subset.trans T.xy_subset) Finset.inter_subset_right), hJEc, hDQ]
    exact hright
  · change pairedExponent (F.doubled ∪ P) _ + pairedExponent (F.doubled ∪ Q) _ = _
    rw [paired_factorization hPI hQI hPQ T.xy_subset hEJ hDU, hPUQ]

/-- The selected term in each of the two source forms. -/
def chosenFactors {F : ProductFiber X s} {a : ℕ} (T : Targets F a) (p : F.Columns) : Factors T p :=
  Classical.choice (factors_nonempty T p)

def choices {F : ProductFiber X s} {a : ℕ} (T : Targets F a)
    (z : F.Columns × Bool) : (X × Bool) →₀ ℕ :=
  if z.2 then pairedExponent (F.label z).1 (chosenFactors T z.1).rightX
  else pairedExponent (F.label z).1 (chosenFactors T z.1).leftX

theorem choices_mem {F : ProductFiber X s} {a : ℕ} (T : Targets F a)
    (z : F.Columns × Bool) : choices T z ∈ allowedExponents a (F.label z).1 := by
  rcases z with ⟨p,b⟩
  cases b
  · exact mem_allowedExponents (chosenFactors T p).left_subset (chosenFactors T p).left_card
  · exact mem_allowedExponents (chosenFactors T p).right_subset (chosenFactors T p).right_card

theorem choices_product {F : ProductFiber X s} {a : ℕ} (T : Targets F a) (p : F.Columns) :
    choices T (p,false) + choices T (p,true) =
      targetExponent F.doubled T.xy F.single (T.subset p) :=
  (chosenFactors T p).product

/-- The actual coefficient-polynomial minor for every non-diagonal fiber is nonzero. -/
theorem non_diagonal_minor {K : Type*} [CommRing K] [Nontrivial K]
    (F : ProductFiber X s) (T : Targets F (s/2)) (ht : 0 < F.halfSize) :
    (ProductMinors.productMinor (K := K) (fun S : SizedSubset X s => allowedExponents (s/2) S.1)
      (fun p => F.label (p,false)) (fun p => F.label (p,true))
      (fun p => targetExponent F.doubled T.xy F.single (T.subset p))).det ≠ 0 := by
  classical
  have h := ProductMinors.disjoint_productMinor_ne_zero (K := K)
    (fun S : SizedSubset X s => allowedExponents (s/2) S.1) F.label (F.label_injective ht)
    (choices T) (choices_mem T)
    (by simpa only [choices_product] using T.target_injective)
  simpa only [choices_product] using h

end Froberg.PairedMonomials.ProductFiber
