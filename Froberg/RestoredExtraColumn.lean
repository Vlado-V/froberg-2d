module

public import Froberg.PreparedCountCompatibility
public import Froberg.PreparedPositiveBackground
public import Froberg.PositiveExtraColumn

@[expose] public section

/-! Restricting one enlarged restored family keeps all base positive
columns literally and separates its single extra positive column. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace Froberg
open Module MvPolynomial
variable {K : Type} [Field K]

theorem span_range_one_extra {V I I' : Type*} [AddCommGroup V] [Module K V]
    (g : I' → V) (b : I → I') (a : I')
    (hcover : ∀ j,j=a ∨ ∃ i,b i=j) :
    Submodule.span K (Set.range g)=
      Submodule.span K (Set.range (g ∘ b)) ⊔ Submodule.span K {g a} := by
  have hrange : Set.range g=Set.range (g ∘ b) ∪ {g a} := by
    ext x
    constructor
    · rintro ⟨j,rfl⟩
      rcases hcover j with rfl | ⟨i,rfl⟩
      · exact Or.inr rfl
      · exact Or.inl ⟨i,rfl⟩
    · rintro (⟨i,rfl⟩ | rfl)
      · exact ⟨b i,rfl⟩
      · exact ⟨a,rfl⟩
  rw [hrange,Submodule.span_union]

namespace PreparedParameters
variable {J : Finset ℕ} {c c' : ℕ → ℕ}

def countPositiveIndexMap (hc : ∀ j∈J,c j≤c' j) :
    Fin (Fintype.card (ProductRows.LayerLabel J c)) →
      Fin (Fintype.card (ProductRows.LayerLabel J c')) :=
  fun i => Fintype.equivFin _ (countLayerMap hc ((Fintype.equivFin _).symm i))

theorem countPositiveIndexMap_injective (hc : ∀ j∈J,c j≤c' j) :
    Function.Injective (countPositiveIndexMap hc) :=
  (Fintype.equivFin _).injective.comp
    ((countLayerMap_injective hc).comp (Fintype.equivFin _).symm.injective)

theorem countPositiveIndexMap_ne (hc : ∀ j∈J,c j≤c' j)
    (a : ProductRows.LayerLabel J c') (ha : ∀ i,countLayerMap hc i≠a)
    (i : Fin (Fintype.card (ProductRows.LayerLabel J c))) :
    countPositiveIndexMap hc i≠Fintype.equivFin _ a := by
  intro h
  exact ha _ ((Fintype.equivFin _).injective h)

theorem countPositiveIndexMap_cover (hc : ∀ j∈J,c j≤c' j)
    (a : ProductRows.LayerLabel J c') (ha : ∀ j,j=a ∨ ∃ i,countLayerMap hc i=j)
    (j : Fin (Fintype.card (ProductRows.LayerLabel J c'))) :
    j=Fintype.equivFin _ a ∨ ∃ i,countPositiveIndexMap hc i=j := by
  obtain rfl | ⟨i,hi⟩ := ha ((Fintype.equivFin _).symm j)
  · exact Or.inl ((Fintype.equivFin _).apply_symm_apply j).symm
  · right
    refine ⟨Fintype.equivFin _ i,?_⟩
    simp only [countPositiveIndexMap,Equiv.symm_apply_apply,hi,Equiv.apply_symm_apply]

/-- Append a single last column at the specified positive layer. -/
def oneExtraCounts (c : ℕ → ℕ) (j : ℕ) : ℕ → ℕ :=
  Function.update c j (c j+1)

theorem le_oneExtraCounts (c : ℕ → ℕ) (j k : ℕ) : c k≤oneExtraCounts c j k := by
  classical
  by_cases hk : k=j
  · subst k
    simp [oneExtraCounts]
  · simp [oneExtraCounts,hk]

def oneExtraLayer (c : ℕ → ℕ) (j : J) : ProductRows.LayerLabel J (oneExtraCounts c j) :=
  ⟨j,⟨c j,by simp [oneExtraCounts]⟩⟩

theorem oneExtraLayer_not_old (c : ℕ → ℕ) (j : J)
    (i : ProductRows.LayerLabel J c) :
    countLayerMap (fun k _ => le_oneExtraCounts c j k) i≠oneExtraLayer c j := by
  intro he
  have hj : i.1=j := congrArg Sigma.fst he
  rcases i with ⟨k,i⟩
  dsimp at hj
  subst k
  have hv : i.val=c j := congrArg (fun a => a.2.val) he
  exact (Nat.ne_of_lt i.isLt) hv

theorem oneExtraLayer_cover (c : ℕ → ℕ) (j : J)
    (i : ProductRows.LayerLabel J (oneExtraCounts c j)) :
    i=oneExtraLayer c j ∨
      ∃ k,countLayerMap (fun k _ => le_oneExtraCounts c j k) k=i := by
  classical
  rcases i with ⟨k,i⟩
  by_cases hi : i.val<c k
  · right
    refine ⟨⟨k,⟨i.val,hi⟩⟩,?_⟩
    congr 1
  · left
    have hk : k=j := by
      apply Subtype.ext
      by_contra hne
      have hlt := i.isLt
      simp only [oneExtraCounts,Function.update_of_ne hne] at hlt
      exact hi hlt
    subst k
    have hlt : i.val<c j+1 := by simpa [oneExtraCounts] using i.isLt
    have hv : i.val=c j := by omega
    congr 1
    exact Fin.ext hv

variable [Infinite K] {h m d q r r' : ℕ}
variable {O : ℕ → Submodule K (Poly K h)}

theorem restoredPositiveBiform_restrictCounts (hd : d%2=0)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (hc : ∀ j∈J,c j≤c' j)
    (idx : Fin r ≃ Label q J c) (idx' : Fin r' ≃ Label q J c')
    (slot : Fin (finrank K (Forms K h d)) → Fin r)
    (p : RestoredSpace m d q J c' O)
    (i : Fin (Fintype.card (ProductRows.LayerLabel J c))) :
    restoredPositiveBiform hd hO hJ heven idx slot (restrictCounts hc p.1,p.2) i=
      restoredPositiveBiform hd hO hJ heven idx' (countIndexMap hc idx idx' ∘ slot) p
        (countPositiveIndexMap hc i) := by
  apply Subtype.ext
  have hh := congrArg Subtype.val (restoredFamilyLinear_restrictCounts hd hO hJ heven hc
    idx idx' slot p (idx.symm (Sum.inr ((Fintype.equivFin _).symm i))))
  simpa only [restoredPositiveBiform,restoredBiformFamily,countPositiveIndexMap,countIndexMap,
    countLabelMap,countLayerMap,Equiv.apply_symm_apply,Equiv.symm_apply_apply,Sum.elim_inr] using hh

/-- The retained restored positive family and the distinguished extra
column span exactly the enlarged restored positive family. -/
theorem restoredPositiveBiform_extra_span (hd : d%2=0)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (hc : ∀ j∈J,c j≤c' j)
    (a : ProductRows.LayerLabel J c')
    (hcover : ∀ j,j=a ∨ ∃ i,countLayerMap hc i=j)
    (idx : Fin r ≃ Label q J c) (idx' : Fin r' ≃ Label q J c')
    (slot : Fin (finrank K (Forms K h d)) → Fin r)
    (p : RestoredSpace m d q J c' O) :
    Submodule.span K (Set.range (fun i => evenPolynomialToForms
      (restoredPositiveBiform hd hO hJ heven idx'
        (countIndexMap hc idx idx' ∘ slot) p i)))=
      Submodule.span K (Set.range (fun i => evenPolynomialToForms
        (restoredPositiveBiform hd hO hJ heven idx slot (restrictCounts hc p.1,p.2) i))) ⊔
      Submodule.span K {(evenPolynomialToForms
        (restoredPositiveBiform hd hO hJ heven idx'
          (countIndexMap hc idx idx' ∘ slot) p (Fintype.equivFin _ a)))} := by
  have hb := span_range_one_extra (K := K)
    (fun i => evenPolynomialToForms (restoredPositiveBiform hd hO hJ heven idx'
      (countIndexMap hc idx idx' ∘ slot) p i))
    (countPositiveIndexMap hc) (Fintype.equivFin _ a)
    (countPositiveIndexMap_cover hc a hcover)
  convert hb using 1
  congr 3
  funext i
  exact congrArg evenPolynomialToForms
    (restoredPositiveBiform_restrictCounts hd hO hJ heven hc idx idx' slot p i)

/-- The same separation with an unchanged odd background appended. -/
theorem restoredPositiveBiform_extra_background_span {u : ℕ} (hd : d%2=0)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (hc : ∀ j∈J,c j≤c' j)
    (a : ProductRows.LayerLabel J c')
    (hcover : ∀ j,j=a ∨ ∃ i,countLayerMap hc i=j)
    (idx : Fin r ≃ Label q J c) (idx' : Fin r' ≃ Label q J c')
    (slot : Fin (finrank K (Forms K h d)) → Fin r)
    (p : RestoredSpace m d q J c' O)
    (G : Fin u → biformParitySpace K h m d 1) :
    Submodule.span K (Set.range (backgroundPositiveForms
      (restoredPositiveBiform hd hO hJ heven idx'
        (countIndexMap hc idx idx' ∘ slot) p) G))=
      Submodule.span K (Set.range (backgroundPositiveForms
        (restoredPositiveBiform hd hO hJ heven idx slot (restrictCounts hc p.1,p.2)) G)) ⊔
      Submodule.span K {(evenPolynomialToForms (restoredPositiveBiform hd hO hJ heven idx'
        (countIndexMap hc idx idx' ∘ slot) p (Fintype.equivFin _ a)))} := by
  simp only [backgroundPositiveForms,Set.Sum.elim_range,Submodule.span_union]
  rw [restoredPositiveBiform_extra_span hd hO hJ heven hc a hcover idx idx' slot p]
  ac_rfl

/-- Joint quotient independence after separating one enlarged positive label.
The quotient is arbitrary; in the application it is the pure-scalar quotient. -/
theorem restoredPositiveBiform_extra_quotient_independent {u : ℕ} (hd : d%2=0)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (hc : ∀ j∈J,c j≤c' j)
    (a : ProductRows.LayerLabel J c') (haway : ∀ i,countLayerMap hc i≠a)
    (idx : Fin r ≃ Label q J c) (idx' : Fin r' ≃ Label q J c')
    (slot : Fin (finrank K (Forms K h d)) → Fin r)
    (p : RestoredSpace m d q J c' O)
    (G : Fin u → biformParitySpace K h m d 1)
    (A : Submodule K (Forms K (h+m) d))
    (hi : LinearIndependent K (fun i => A.mkQ
      (backgroundPositiveForms (restoredPositiveBiform hd hO hJ heven idx'
        (countIndexMap hc idx idx' ∘ slot) p) G i))) :
    LinearIndependent K (fun i : Option
      (Fin (Fintype.card (ProductRows.LayerLabel J c)) ⊕ Fin u) =>
      A.mkQ (i.elim (evenPolynomialToForms
        (restoredPositiveBiform hd hO hJ heven idx'
          (countIndexMap hc idx idx' ∘ slot) p (Fintype.equivFin _ a)))
        (backgroundPositiveForms
          (restoredPositiveBiform hd hO hJ heven idx slot (restrictCounts hc p.1,p.2)) G))) := by
  let b : Fin (Fintype.card (ProductRows.LayerLabel J c)) ⊕ Fin u →
      Fin (Fintype.card (ProductRows.LayerLabel J c')) ⊕ Fin u :=
    Sum.map (countPositiveIndexMap hc) id
  have hb : Function.Injective b :=
    Function.Injective.sumMap (countPositiveIndexMap_injective hc) Function.injective_id
  have ha : ∀ i,b i≠Sum.inl (Fintype.equivFin _ a) := by
    intro i
    cases i with
    | inl j => exact fun he => countPositiveIndexMap_ne hc a haway j (Sum.inl.inj he)
    | inr j => intro he; cases he
  have hh := independent_extra_reindex _ hi (Sum.inl (Fintype.equivFin _ a)) b hb ha
  convert hh using 1
  funext i
  cases i with
  | none => rfl
  | some i =>
    cases i with
    | inl j =>
      exact congrArg (fun x => A.mkQ (evenPolynomialToForms x))
        (restoredPositiveBiform_restrictCounts hd hO hJ heven hc idx idx' slot p j)
    | inr j => rfl

/-- The even-only specialization derives quotient independence directly
from the enlarged parameter's independent prepared rows. -/
theorem restoredPositiveBiform_extra_scalar_independent (hd : d%2=0)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (hpos : ∀ j∈J,0<j) (hJlt : ∀ j∈J,0<c' j → j<d)
    (hc : ∀ j∈J,c j≤c' j)
    (a : ProductRows.LayerLabel J c') (haway : ∀ i,countLayerMap hc i≠a)
    (idx : Fin r ≃ Label q J c) (idx' : Fin r' ≃ Label q J c')
    (slot : Fin (finrank K (Forms K h d)) → Fin r)
    (p : RestoredSpace m d q J c' O) (hp : ∀ j,LinearIndependent K (p.1.2 j)) :
    LinearIndependent K (fun i : Option
      (Fin (Fintype.card (ProductRows.LayerLabel J c)) ⊕ Fin 0) =>
      (renameForm (K := K) (d := d) (Fin.natAdd h : Fin m → Fin (h+m))).range.mkQ
        (i.elim (evenPolynomialToForms
          (restoredPositiveBiform hd hO hJ heven idx'
            (countIndexMap hc idx idx' ∘ slot) p (Fintype.equivFin _ a)))
          (backgroundPositiveForms
            (restoredPositiveBiform hd hO hJ heven idx slot (restrictCounts hc p.1,p.2))
            (fun i : Fin 0 => Fin.elim0 i)))) := by
  apply restoredPositiveBiform_extra_quotient_independent hd hO hJ heven hc a haway
    idx idx' slot p (fun i : Fin 0 => Fin.elim0 i)
  let b : Fin (Fintype.card (ProductRows.LayerLabel J c')) ⊕ Fin 0 →
      Fin (Fintype.card (ProductRows.LayerLabel J c')) := Sum.elim id Fin.elim0
  have hb : Function.Injective b := by
    intro i j he
    cases i with
    | inl i =>
      cases j with
      | inl j => exact congrArg Sum.inl he
      | inr j => exact Fin.elim0 j
    | inr i => exact Fin.elim0 i
  have hh := (PreparedTarget.restored_positive_biform_scalar_independent hd hO hJ heven
    hpos hJlt idx' (countIndexMap hc idx idx' ∘ slot) p hp).comp b hb
  convert hh using 1
  funext i
  cases i with
  | inl i => rfl
  | inr i => exact Fin.elim0 i

end PreparedParameters
end Froberg
