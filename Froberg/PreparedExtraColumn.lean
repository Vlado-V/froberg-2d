import Froberg.PreparedCountCompatibility
import Froberg.PreparedPositiveBackground
import Froberg.PositiveExtraColumn

/-! The temporary extra positive generator and the retained prepared family
are restrictions of one parameter point. -/
noncomputable section
set_option maxHeartbeats 600000
namespace Froberg
open Module MvPolynomial
variable {K : Type} {V I J : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem span_range_eq_sup_extra (g : J → V) (b : I → J) (k : J)
    (hcover : ∀ j,(∃ i,b i=j) ∨ j=k) :
    Submodule.span K (Set.range g)=
      Submodule.span K (Set.range (g ∘ b)) ⊔ Submodule.span K {g k} := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    rcases hcover j with ⟨i,rfl⟩ | rfl
    · exact Submodule.mem_sup_left (Submodule.subset_span ⟨i,rfl⟩)
    · exact Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton _))
  · apply sup_le
    · apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact Submodule.subset_span ⟨b i,rfl⟩
    · apply Submodule.span_le.mpr
      rintro _ (rfl : _=g k)
      exact Submodule.subset_span ⟨k,rfl⟩

namespace PreparedParameters
variable [Infinite K] {h m d q f u : ℕ}
variable {J : Finset ℕ} {c c' : ℕ → ℕ} {O : ℕ → Submodule K (Poly K h)}

def countPositiveIndex (hc : ∀ j∈J,c j≤c' j) :
    Fin (Fintype.card (ProductRows.LayerLabel J c)) →
      Fin (Fintype.card (ProductRows.LayerLabel J c')) :=
  fun i => Fintype.equivFin _ (countLayerMap hc ((Fintype.equivFin _).symm i))

theorem countPositiveIndex_injective (hc : ∀ j∈J,c j≤c' j) :
    Function.Injective (countPositiveIndex hc) :=
  (Fintype.equivFin _).injective.comp
    ((countLayerMap_injective hc).comp (Fintype.equivFin _).symm.injective)

def countBackgroundIndex (hc : ∀ j∈J,c j≤c' j) :
    Fin (Fintype.card (ProductRows.LayerLabel J c)) ⊕ Fin u →
      Fin (Fintype.card (ProductRows.LayerLabel J c')) ⊕ Fin u :=
  Sum.map (countPositiveIndex hc) id

theorem countBackgroundIndex_injective (hc : ∀ j∈J,c j≤c' j) :
    Function.Injective (countBackgroundIndex (u := u) hc) :=
  (countPositiveIndex_injective hc).sumMap Function.injective_id

def quadraticExtraLayer {d : ℕ} (hd : 3≤d) (h m e : ℕ) :
    ProductRows.LayerLabel (allEvenIndices d) (allEvenCount d h m (e+1)) :=
  ⟨⟨2,mem_allEvenIndices.mpr ⟨le_rfl,by omega,by decide⟩⟩,
    ⟨e,by simp only [allEvenCount_active h m _ (two_mem_activeEvenIndices hd),
      targetLayerCount,ite_true]; omega⟩⟩

theorem quadraticExtraLayer_not_old {d : ℕ} (hd : 3≤d) (h m e : ℕ)
    (i : ProductRows.LayerLabel (allEvenIndices d) (allEvenCount d h m e)) :
    countLayerMap (allEvenCount_le_append hd h m e 1) i≠quadraticExtraLayer hd h m e := by
  intro hi
  have hs : quadraticTailSlot hd 0 h m e 1 0=
      countLabelMap (q := 0) (allEvenCount_le_append hd h m e 1) (Sum.inr i) := by
    change Sum.inr (quadraticExtraLayer hd h m e)=
      Sum.inr (countLayerMap (allEvenCount_le_append hd h m e 1) i)
    exact congrArg Sum.inr hi.symm
  exact quadraticTailSlot_ne_old hd h m e 1 0 (Sum.inr i) hs

theorem quadraticExtraLayer_cover {d : ℕ} (hd : 3≤d) (h m e : ℕ)
    (i : ProductRows.LayerLabel (allEvenIndices d) (allEvenCount d h m (e+1))) :
    (∃ j,countLayerMap (allEvenCount_le_append hd h m e 1) j=i) ∨
      i=quadraticExtraLayer hd h m e := by
  rcases i with ⟨⟨j,hjmem⟩,i⟩
  by_cases hi : i.val<allEvenCount d h m e j
  · left
    refine ⟨⟨⟨j,hjmem⟩,⟨i.val,hi⟩⟩,?_⟩
    congr 1
  · right
    have hcount : allEvenCount d h m (e+1) j=
        allEvenCount d h m e j+if j=2 then 1 else 0 := by
      rw [allEvenCount_append hd]
      rfl
    have hil : i.val<allEvenCount d h m e j+if j=2 then 1 else 0 :=
      lt_of_lt_of_eq i.isLt hcount
    have hj : j=2 := by
      by_contra hj
      rw [if_neg hj] at hil
      omega
    subst j
    have he : allEvenCount d h m e 2=e := by
      simp only [allEvenCount_active h m _ (two_mem_activeEvenIndices hd),targetLayerCount,ite_true]
    have hv : i.val=e := by
      rw [if_pos rfl,he] at hil
      rw [he] at hi
      omega
    congr 1
    exact Fin.ext hv

end PreparedParameters

namespace PreparedTarget
open PreparedParameters
variable [Infinite K] {h m d q f u : ℕ}
variable {J : Finset ℕ} {c c' : ℕ → ℕ} {O : ℕ → Submodule K (Poly K h)}

theorem preparedPositiveBiform_restrictCounts
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (hc : ∀ j∈J,c j≤c' j) (p : PreparedParameters.Space m d q J c' O)
    (i : Fin (Fintype.card (ProductRows.LayerLabel J c))) :
    preparedPositiveBiform hO hJ heven (restrictCounts hc p) i=
      preparedPositiveBiform hO hJ heven p (countPositiveIndex hc i) := by
  unfold preparedPositiveBiform countPositiveIndex
  rw [Equiv.symm_apply_apply,preparedEvenBiform_restrictCounts]
  rfl

theorem preparedBackground_restrictCounts
    (hd : 0<d) (ho : d%2=1)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (hc : ∀ j∈J,c j≤c' j) (p : PreparedParameters.Space m d q J c' O)
    (U : Fin u → Forms K h d) (P : OuterSpace K (Fin h) m d u)
    (F : OuterSpace K (Fin h) m d f) :
    backgroundPositiveForms (preparedPositiveBiform hO hJ heven p)
      (fun j => preparedOddBiform hd ho U P F (Sum.inr j)) ∘ countBackgroundIndex hc=
    backgroundPositiveForms (preparedPositiveBiform hO hJ heven (restrictCounts hc p))
      (fun j => preparedOddBiform hd ho U P F (Sum.inr j)) := by
  funext i
  cases i with
  | inl i =>
    change evenPolynomialToForms (preparedPositiveBiform hO hJ heven p (countPositiveIndex hc i))=_
    rw [←preparedPositiveBiform_restrictCounts]
    rfl
  | inr i => rfl

theorem prepared_extra_positive_independent
    (hd : 0<d) (ho : d%2=1)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (hc : ∀ j∈J,c j≤c' j) (p : PreparedParameters.Space m d q J c' O)
    (U : Fin u → Forms K h d) (P : OuterSpace K (Fin h) m d u)
    (F : OuterSpace K (Fin h) m d f) (extra : ProductRows.LayerLabel J c')
    (hmiss : ∀ i,countLayerMap hc i≠extra)
    (hi : LinearIndependent K (fun i =>
      (renameForm (K := K) (d := d) (Fin.natAdd h : Fin m → Fin (h+m))).range.mkQ
        (backgroundPositiveForms (preparedPositiveBiform hO hJ heven p)
          (fun j => preparedOddBiform hd ho U P F (Sum.inr j)) i))) :
    LinearIndependent K (fun i : Option (Fin (Fintype.card (ProductRows.LayerLabel J c)) ⊕ Fin u) =>
      (renameForm (K := K) (d := d) (Fin.natAdd h : Fin m → Fin (h+m))).range.mkQ
        (i.elim (evenPolynomialToForms (preparedEvenBiform hO hJ heven p (Sum.inr extra)))
          (backgroundPositiveForms (preparedPositiveBiform hO hJ heven (restrictCounts hc p))
            (fun j => preparedOddBiform hd ho U P F (Sum.inr j))))) := by
  have hm : ∀ i,countBackgroundIndex (u := u) hc i≠Sum.inl (Fintype.equivFin _ extra) := by
    intro i hi
    cases i with
    | inl i =>
      exact hmiss _ ((Fintype.equivFin _).injective (Sum.inl.inj hi))
    | inr i => cases hi
  have hh := independent_extra_reindex _ hi (Sum.inl (Fintype.equivFin _ extra))
    (countBackgroundIndex hc) (countBackgroundIndex_injective hc) hm
  convert hh using 1
  funext i
  cases i with
  | none => simp only [Option.elim_none,backgroundPositiveForms,Sum.elim_inl,
      preparedPositiveBiform,Equiv.symm_apply_apply]
  | some i =>
    simp only [Option.elim_some]
    congr 1
    exact (congrFun (preparedBackground_restrictCounts hd ho hO hJ heven hc p U P F) i).symm

theorem prepared_extra_background_span
    (hd : 0<d) (ho : d%2=1)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (hc : ∀ j∈J,c j≤c' j) (p : PreparedParameters.Space m d q J c' O)
    (U : Fin u → Forms K h d) (P : OuterSpace K (Fin h) m d u)
    (F : OuterSpace K (Fin h) m d f) (extra : ProductRows.LayerLabel J c')
    (hcover : ∀ j,(∃ i,countLayerMap hc i=j) ∨ j=extra) :
    Submodule.span K (Set.range (backgroundPositiveForms (preparedPositiveBiform hO hJ heven p)
      (fun j => preparedOddBiform hd ho U P F (Sum.inr j))))=
    Submodule.span K (Set.range (backgroundPositiveForms
      (preparedPositiveBiform hO hJ heven (restrictCounts hc p))
      (fun j => preparedOddBiform hd ho U P F (Sum.inr j)))) ⊔
      Submodule.span K {evenPolynomialToForms (preparedEvenBiform hO hJ heven p (Sum.inr extra))} := by
  have hc' : ∀ j,(∃ i,countBackgroundIndex (u := u) hc i=j) ∨
      j=Sum.inl (Fintype.equivFin _ extra) := by
    intro j
    cases j with
    | inl j =>
      rcases hcover ((Fintype.equivFin _).symm j) with ⟨i,hi⟩ | hi
      · left
        refine ⟨Sum.inl (Fintype.equivFin _ i),?_⟩
        simp only [countBackgroundIndex,Sum.map_inl,countPositiveIndex,Equiv.symm_apply_apply,hi,
          Equiv.apply_symm_apply]
      · right
        exact congrArg Sum.inl ((Equiv.eq_symm_apply _).mp hi.symm).symm
    | inr j => exact Or.inl ⟨Sum.inr j,rfl⟩
  have hh := span_range_eq_sup_extra (K := K)
    (backgroundPositiveForms (preparedPositiveBiform hO hJ heven p)
      (fun j => preparedOddBiform hd ho U P F (Sum.inr j)))
    (countBackgroundIndex hc) (Sum.inl (Fintype.equivFin _ extra)) hc'
  rw [preparedBackground_restrictCounts hd ho hO hJ heven hc p U P F] at hh
  simpa only [backgroundPositiveForms,Sum.elim_inl,preparedPositiveBiform,Equiv.symm_apply_apply] using hh

end PreparedTarget
end Froberg
