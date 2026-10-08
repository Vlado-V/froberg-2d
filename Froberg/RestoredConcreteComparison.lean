import Froberg.RestoredBackgroundData
import Froberg.BackgroundChildDeletion
import Froberg.RestoredCertificateRelations
import Froberg.RestoredEndpointSpan
import Froberg.RestoredExtraColumn
import Froberg.ConcreteBackgroundComparison

/-! A base restored certificate, its one-column enlargement, and the
actual thin and separation conditions give the critical local comparison. -/
noncomputable section
set_option maxHeartbeats 2200000
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial BilinearScalarFamily VectorExpansionOpen
variable {K : Type} [Field K] [Infinite K] [IsAlgClosed K]
variable {h m d f r r' : ℕ} {J : Finset ℕ} {c c' : ℕ → ℕ}
variable {O : ℕ → Submodule K (Poly K h)}

private theorem positive_empty_span (E : Fin r → biformParitySpace K h m d 0) :
    Submodule.span K (Set.range (backgroundPositiveForms E (emptyOddFamily (K := K))))=
      Submodule.span K (Set.range (fun i => evenPolynomialToForms (E i))) := by
  apply congrArg (Submodule.span K)
  ext x
  constructor
  · rintro ⟨i,rfl⟩
    cases i with
    | inl i => exact ⟨i,rfl⟩
    | inr i => exact Fin.elim0 i
  · rintro ⟨i,rfl⟩
    exact ⟨Sum.inl i,rfl⟩

theorem exists_critical_comparison_of_restored_background
    (htwo : (2 : K)≠0) (hm : 0 < m) (hdp : 1≤d) (hd : d%2=0) (upper : Bool)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (hpos : ∀ j∈J,0<j) (hJlt : ∀ j∈J,0<c' j → j<d)
    (hc : ∀ j∈J,c j≤c' j)
    (extra : ProductRows.LayerLabel J c') (haway : ∀ i,countLayerMap hc i≠extra)
    (hcover : ∀ i,i=extra ∨ ∃ j,countLayerMap hc j=i)
    (idx : Fin r ≃ Label (upperCount m d) J c)
    (idx' : Fin r' ≃ Label (upperCount m d) J c')
    (slot : Fin (finrank K (Forms K h d)) → Fin r)
    (hslot : ∀ k,0<degree (idx (slot k)))
    (p : RestoredOuterSpace m d (upperCount m d) f J c' O)
    (hbase : RestoredCertificate hdp hd hO hJ heven idx slot (restoredRestrictCounts hc p))
    (hlarge : RestoredCertificate hdp hd hO hJ heven idx'
      (countIndexMap hc idx idx' ∘ slot) p)
    (hleading : ∀ j,LinearIndependent K (p.1.1.2 j))
    (hcard : upperCount m d+Fintype.card (ProductRows.LayerLabel J c)+f=
      adjacentCriticalCount upper (h+m) d)
    (Cchild : ℝ)
    (hchild : ChildFlagCondition
      (quotientMultiplication (fun i => PreparedTarget.outerVectorEquiv.symm (p.2 i)) d)
      (outerScalarDeficit (fun i => PreparedTarget.outerVectorEquiv.symm (p.2 i))) Cchild
      (coefficientCoordinates (fun i => p.1.1.1 (Sum.inl i))))
    (C : ℝ) (hC : (f : ℝ)≤C)
    (hthin : HasClosedKernelSlices (oddEndpointScalarAction
      (Fin.append (fun i => scalarEvenBiform (h := h) (p.1.1.1 (Sum.inl i)))
        (restoredPositiveBiform hd hO hJ heven idx slot (restoredRestrictCounts hc p).1))
      (fun i => linearOddForm hdp (PreparedTarget.outerVectorEquiv.symm (p.2 i))) emptyOddFamily)
      (BilinearCovectorStrata.thinSlices (backgroundOddTargetDimension
        (Fin.append (fun i => scalarEvenBiform (h := h) (p.1.1.1 (Sum.inl i)))
          (restoredPositiveBiform hd hO hJ heven idx slot (restoredRestrictCounts hc p).1))
        (fun i => linearOddForm hdp (PreparedTarget.outerVectorEquiv.symm (p.2 i))) emptyOddFamily) C))
    (hsep : ∀ D : Submodule K (Forms K (h+m) (2*d)),
      D≤(renameForm (K := K) (d := 2*d) (Fin.natAdd h : Fin m → Fin (h+m))).range →
      formalSquare (Submodule.span K (Set.range (fun i => oddPolynomialToForms
        (linearOddForm hdp (PreparedTarget.outerVectorEquiv.symm (p.2 i)))))) ⊓
        ((formalMixed (Submodule.span K (Set.range (restoredEndpointFamily hd hO hJ heven idx'
          (countIndexMap hc idx idx' ∘ slot) p.1)))).map
          (D.mkQ.comp formalPolynomialMultiplication)).comap
          (D.mkQ.comp (formalPolynomialMultiplication (K := K) (n := h+m) (d := d)))=⊥) :
    Nonempty (LocalComparisonData K (h+m) d
      (adjacentCriticalCount upper (h+m) d) (criticalDefect K m d)) := by
  classical
  let base := restoredRestrictCounts hc p
  let Q := fun i => p.1.1.1 (Sum.inl i)
  let E := restoredPositiveBiform hd hO hJ heven idx slot base.1
  let F := fun i => linearOddForm hdp (PreparedTarget.outerVectorEquiv.symm (p.2 i))
  let slots := countIndexMap hc idx idx' ∘ slot
  let M := restoredPositiveBiform hd hO hJ heven idx' slots p.1 (Fintype.equivFin _ extra)
  have hslots : ∀ k,0<degree (idx' (slots k)) := by
    have hdeg (i : Label (upperCount m d) J c) : degree (countLabelMap hc i)=degree i := by
      cases i <;> rfl
    intro k
    simpa only [slots,countIndexMap,Function.comp_apply,Equiv.apply_symm_apply,hdeg] using hslot k
  have hdata := restored_certificate_background hdp hd hO hJ heven idx slot hslot base hbase
  change LinearIndependent K (backgroundEnumeratedForms (Fin.append (fun i => scalarEvenBiform (h := h) (Q i)) E) F emptyOddFamily) ∧
    OddSplitExact (Fin.append (fun i => scalarEvenBiform (h := h) (Q i)) E) (Fin.append F emptyOddFamily) ∧
    Function.Surjective (upperTargetMap (backgroundEnumeratedForms
      (Fin.append (fun i => scalarEvenBiform (h := h) (Q i)) E) F emptyOddFamily)) at hdata
  have hQdata := childFlag_scalar_properties _ _ _ Q hchild
  obtain ⟨D,hDdim,hD,hinj,hcoverage⟩ := exists_background_child_deletion Q E F emptyOddFamily
    hQdata.2.1 hdata.2.2
  have hpositive := restoredPositiveBiform_extra_scalar_independent hd hO hJ heven hpos hJlt
    hc extra haway idx idx' slot p.1 hleading
  have hspan : Submodule.span K (Set.range (restoredEndpointFamily hd hO hJ heven idx' slots p.1))=
      (embeddedFlagSpace (renameForm (Fin.natAdd h)) Q ⊔
        Submodule.span K (Set.range (backgroundPositiveForms E emptyOddFamily))) ⊔
          Submodule.span K {evenPolynomialToForms M} := by
    rw [restoredEndpointFamily_span hd hO hJ heven idx' slots hslots p.1]
    simp only [Function.comp_def]
    rw [restoredPositiveBiform_extra_span hd hO hJ heven hc extra hcover idx idx' slot p.1]
    rw [positive_empty_span]
    exact (sup_assoc _ _ _).symm
  have hbackground := restored_certificate_formal_relations htwo hdp hd hO hJ heven hpos
    idx' slots hslots p hlarge D hD
  rw [hspan] at hbackground
  have hseparation := hsep D hD
  rw [hspan] at hseparation
  exact exists_critical_comparison_of_concrete_background htwo hm upper
    (by simpa only [Nat.add_zero] using hcard) D hD Q hQdata.1 E F emptyOddFamily M
    hpositive hbackground hseparation hdata.1 hdata.2.1 hdata.2.2 hcoverage C hC hthin
    hQdata.2.2 hinj hDdim

end Froberg.PreparedParameters
