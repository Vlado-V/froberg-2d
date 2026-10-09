module

public import Froberg.MixedPrefix
public import Froberg.ExceptionalFamilies

@[expose] public section

/-! Uniform bounds on pairwise disjoint defective added-relation blocks. -/
noncomputable section
namespace Froberg.MixedExterior
open Module
variable {K α T : Type*} [Field K] [DecidableEq α] [DecidableEq T]

/-- The actual span of the attached vectors whose labels belong to a block. -/
def blockSpan {h : ℕ} (v : α → Fin h → K) (S : Finset α) :
    Submodule K (Fin h → K) := Submodule.span K (v '' (S : Set α))

/-- A generic mixed-position family has fewer disjoint deficient blocks than
there are coordinates of the exterior power of the lifted subspace. -/
theorem card_disjoint_deficient_lt {h : ℕ}
    (v : α → Fin h → K) (hv : UniversalMixedPosition v)
    (U : Submodule K (Fin h → K)) (sets : T → Finset α) (B : Finset T)
    (hdis : ∀ i ∈ B, ∀ j ∈ B, i ≠ j → Disjoint (sets i) (sets j))
    (hfail : ∀ i ∈ B, finrank K ↥(U ⊔ blockSpan v (sets i)) <
      min (finrank K U + (sets i).card) h) :
    B.card < Fintype.card (Set.powersetCard
      (Fin (finrank K U + (h-finrank K U))) (finrank K U)) := by
  classical
  let r : ℕ := finrank K U
  let l : ℕ := h-r
  have hrle : r ≤ h := by simpa [r] using (Submodule.finrank_le U)
  have hr : r+l=h := Nat.add_sub_of_le hrle
  let Idx := Set.powersetCard (Fin (r+l)) r
  by_contra hn
  have hc : Fintype.card Idx ≤ Fintype.card B := by simpa [Idx,r,l] using (Nat.le_of_not_gt hn)
  let row : Idx ↪ B := Classical.choice (Function.Embedding.nonempty_of_card_le hc)
  let t : Idx → Fin (l+1) := fun I => ⟨min (sets (row I).val).card l,by omega⟩
  have hpick (I : Idx) : Nonempty (Fin (t I).val ↪ sets (row I).val) :=
    Function.Embedding.nonempty_of_card_le (by
      simp only [Fintype.card_fin, Fintype.card_coe]
      exact min_le_left _ _)
  let pick (I : Idx) : Fin (t I).val ↪ sets (row I).val := Classical.choice (hpick I)
  let label : (Σ I, Fin (t I).val) ↪ α :=
    { toFun := fun p => (pick p.1 p.2).val
      inj' := by
        rintro ⟨I,i⟩ ⟨J,j⟩ he
        change (pick I i).val = (pick J j).val at he
        have hIJ : I=J := by
          by_contra hne
          have hij : (row I).val ≠ (row J).val := fun hij =>
            hne (row.injective (Subtype.ext hij))
          have hd := hdis (row I).val (row I).property (row J).val (row J).property hij
          exact Finset.disjoint_left.mp hd (pick I i).property
            (he.symm ▸ (pick J j).property)
        subst J
        have hij : i=j := (pick I).injective (Subtype.ext he)
        subst j
        rfl }
  let coord : (Fin h → K) →ₗ[K] (Fin (r+l) → K) :=
    LinearMap.pi (fun j => LinearMap.proj (Fin.cast hr j))
  have hcoord : Function.Injective coord := by
    intro f g he
    funext j
    have hh := congrFun he (Fin.cast hr.symm j)
    simpa [coord] using hh
  let a : Fin r → Fin h → K := fun i => (Module.finBasis K U i).val
  have ha : LinearIndependent K a :=
    (Module.finBasis K U).linearIndependent.map' U.subtype
      (LinearMap.ker_eq_bot.mpr U.injective_subtype)
  have hac : LinearIndependent K (coord ∘ a) :=
    ha.map' coord (LinearMap.ker_eq_bot.mpr hcoord)
  obtain ⟨I,hI⟩ := universal_exists_independent_prefix v hv ⟨r,by omega⟩ t label (coord ∘ a) hac
  let S := U ⊔ blockSpan v (sets (row I).val)
  let b : Fin (t I).val → Fin h → K := fun j => v (pick I j).val
  let w := Fin.append a b
  have hw : ∀ j, w j ∈ S := by
    intro j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp only [w,Fin.append_left]
      exact (le_sup_left : U ≤ S) (Module.finBasis K U j).property
    · simp only [w,Fin.append_right]
      exact (le_sup_right : blockSpan v (sets (row I).val) ≤ S)
        (Submodule.subset_span ⟨(pick I j).val,(pick I j).property,rfl⟩)
  have hwi : LinearIndependent K w := by
    apply LinearIndependent.of_comp coord
    convert hI using 1
    funext j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp only [Function.comp_apply,w,Fin.append_left]
    · simp only [Function.comp_apply,w,Fin.append_right]
      rfl
  have hws : LinearIndependent K (fun j => (⟨w j,hw j⟩ : S)) :=
    LinearIndependent.of_comp S.subtype hwi
  have hd := hws.fintype_card_le_finrank
  simp only [Fintype.card_fin] at hd
  have hf := hfail (row I).val (row I).property
  change r + min (sets (row I).val).card l ≤ finrank K S at hd
  change finrank K S < min (r + (sets (row I).val).card) h at hf
  omega

/-- A convenient exterior-degree-independent bound for the exceptional packing. -/
theorem card_disjoint_deficient_le {h : ℕ}
    (v : α → Fin h → K) (hv : UniversalMixedPosition v)
    (U : Submodule K (Fin h → K)) (sets : T → Finset α) (B : Finset T)
    (hdis : ∀ i ∈ B, ∀ j ∈ B, i ≠ j → Disjoint (sets i) (sets j))
    (hfail : ∀ i ∈ B, finrank K ↥(U ⊔ blockSpan v (sets i)) <
      min (finrank K U + (sets i).card) h) : B.card ≤ 2^h := by
  have hr : finrank K U ≤ h := by simpa using Submodule.finrank_le U
  have hc := card_disjoint_deficient_lt v hv U sets B hdis hfail
  have he : Fintype.card (Set.powersetCard
      (Fin (finrank K U + (h-finrank K U))) (finrank K U)) ≤ 2^h := by
    calc
      _ ≤ Fintype.card (Finset (Fin (finrank K U + (h-finrank K U)))) :=
        Fintype.card_le_of_injective Subtype.val Subtype.val_injective
      _ = 2^h := by simp [Nat.add_sub_of_le hr]
  omega

/-- Uniform deficient blocks are all hit by a set of at most `h*2^h` labels. -/
theorem exists_deficient_hitting_set {h : ℕ}
    (v : α → Fin h → K) (hv : UniversalMixedPosition v)
    (U : Submodule K (Fin h → K)) (sets : T → Finset α) (E : Finset T)
    (hsize : ∀ i ∈ E, (sets i).card ≤ h)
    (hfail : ∀ i ∈ E, finrank K ↥(U ⊔ blockSpan v (sets i)) <
      min (finrank K U + (sets i).card) h) :
    ∃ L : Finset α, L.card ≤ h*2^h ∧ ∀ i ∈ E, ∃ a ∈ L, a ∈ sets i := by
  apply ExceptionalFamilies.exists_hitting_set sets E h (2^h) hsize
  · intro i hi
    by_contra hn
    have he : sets i = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have hf := hfail i hi
    rw [he] at hf
    have hEmpty : blockSpan v (∅ : Finset α) = ⊥ := by
      have heq : v '' ((∅ : Finset α) : Set α) = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro x ⟨y,hy,rfl⟩
        exact Finset.notMem_empty y hy
      rw [blockSpan,heq,Submodule.span_empty]
    rw [hEmpty,sup_bot_eq,Finset.card_empty,add_zero] at hf
    exact (not_lt_of_ge (min_le_left _ _)) hf
  · intro B hBE hdis
    exact card_disjoint_deficient_le v hv U sets B hdis (fun i hi => hfail i (hBE hi))

end Froberg.MixedExterior
