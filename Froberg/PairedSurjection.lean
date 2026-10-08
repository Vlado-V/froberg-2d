import Froberg.PairedFibers

/-! Every unordered pair of degree-s supports occurs in its doubled/single-index fiber. -/
noncomputable section
namespace Froberg.PairedMonomials
open Finset ProductFibers
variable {X : Type*} [Fintype X] [DecidableEq X] {s : ℕ}

namespace ProductFiber

theorem column_of_representative (F : ProductFiber X s) (P : SizedSubset F.single F.halfSize) :
    Sym2.map Subtype.val (F.column ⟦P⟧) =
      s(F.doubled ∪ liftPart F.single P.1, F.doubled ∪ liftPart F.single P.1ᶜ) := by
  let p : F.Columns := ⟦P⟧
  have hr : p.out = P ∨ p.out = halfCompl F.card_indices P :=
    Quotient.exact (Quotient.out_eq p)
  change s((F.label (p,false)).1,(F.label (p,true)).1) = _
  rw [label_false,label_true]
  rcases hr with hr | hr
  · rw [hr]
  · rw [hr]
    simp only [halfCompl, compl_compl]
    exact Sym2.eq_swap

end ProductFiber

def allColumns (z : Σ F : ProductFiber X s, F.Columns) : Sym2 (SizedSubset X s) :=
  z.1.column z.2

/-- Exhaustion of unordered support pairs by the finite family of product fibers. -/
theorem allColumns_surjective : Function.Surjective (allColumns (X := X) (s := s)) := by
  intro z
  induction z using Sym2.inductionOn with | _ S T =>
    let I := S.1 ∩ T.1
    let R := (S.1 ∪ T.1) \ I
    have hIS : I ⊆ S.1 := Finset.inter_subset_left
    have hIT : I ⊆ T.1 := Finset.inter_subset_right
    have hIU : I ⊆ S.1 ∪ T.1 := hIS.trans Finset.subset_union_left
    have hle : I.card ≤ s := (Finset.card_le_card hIS).trans_eq S.2
    have hdisj : Disjoint I R := by
      exact Finset.disjoint_left.mpr (fun _ hi hr => (Finset.mem_sdiff.mp hr).2 hi)
    have hcard : R.card = 2 * (s - I.card) := by
      have hu := Finset.card_union_add_card_inter S.1 T.1
      rw [S.2,T.2] at hu
      change (S.1 ∪ T.1).card + I.card = s+s at hu
      dsimp [R]
      rw [Finset.card_sdiff_of_subset hIU]
      omega
    let F : ProductFiber X s := ⟨(I,R),hdisj,hle,hcard⟩
    have hSR : S.1 \ I ⊆ R := by
      intro x hx
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ (Finset.mem_sdiff.mp hx).1,
        (Finset.mem_sdiff.mp hx).2⟩
    let P₀ : Finset F.single := (S.1 \ I).subtype (fun x => x ∈ R)
    have hPcard : P₀.card = F.halfSize := by
      change ((S.1 \ I).subtype (fun x => x ∈ R)).card = s - I.card
      rw [Finset.card_subtype, Finset.filter_true_of_mem (fun x hx => hSR hx),
        Finset.card_sdiff_of_subset hIS, S.2]
    let P : SizedSubset F.single F.halfSize := ⟨P₀,hPcard⟩
    have hlift : liftPart F.single P.1 = S.1 \ I := by
      exact Finset.subtype_map_of_mem (fun x hx => hSR hx)
    have hother : liftPart F.single P.1ᶜ = T.1 \ I := by
      rw [liftPart_compl,hlift]
      change R \ (S.1 \ I) = T.1 \ I
      ext x
      simp only [R,I,Finset.mem_sdiff,Finset.mem_union,Finset.mem_inter]
      tauto
    refine ⟨⟨F,⟦P⟧⟩,?_⟩
    apply Sym2.map.injective Subtype.val_injective
    change Sym2.map Subtype.val (F.column ⟦P⟧) = s(S.1,T.1)
    rw [F.column_of_representative P,hlift,hother]
    change s(I ∪ (S.1 \ I),I ∪ (T.1 \ I)) = s(S.1,T.1)
    rw [Finset.union_sdiff_of_subset hIS,Finset.union_sdiff_of_subset hIT]

end Froberg.PairedMonomials
