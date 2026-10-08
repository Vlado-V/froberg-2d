import Froberg.PreparedPrivateFormalRelations
import Froberg.OddSplitRestriction

/-! The private background inherits independence and odd exactness from
the complete prepared family, after removing the outer F columns. -/
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial PreparedTarget
variable {K : Type} [Field K] [Infinite K]
variable {h m d q r f b : ℕ} {J : Finset ℕ} {counts : ℕ → ℕ}
variable {O : ℕ → Submodule K (Poly K h)}

theorem prepared_even_independent_of_full (hd : 0<d)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (p : Space m d q J counts O) (P : OuterSpace K (Fin h) m d b)
    (U : Fin b → Forms K h d) (F : OuterSpace K (Fin h) m d f)
    (hi : LinearIndependent K (zeroScalarEndpointFamily hd hO hJ U P (p,F))) :
    LinearIndependent K (preparedEvenBiform hO hJ heven p) := by
  let emb : PreparedParameters.Label q J counts → Fin (Fintype.card (PreparedTarget.Label q f b J counts)) :=
    fun i => Fintype.equivFin _ (Sum.inl i)
  have hemb : Function.Injective emb := (Fintype.equivFin _).injective.comp Sum.inl_injective
  apply LinearIndependent.of_comp evenPolynomialToForms
  convert hi.comp emb hemb using 1
  funext i
  apply Subtype.ext
  apply (renameEquiv K finSumFinEquiv.symm).injective
  simp only [Function.comp_apply,renameEquiv_apply,evenPolynomialToForms_val]
  change rename finSumFinEquiv.symm (rename finSumFinEquiv (generator p i))=
    rename finSumFinEquiv.symm (zeroScalarEndpointFamily hd hO hJ U P (p,F)
      (Fintype.equivFin _ (Sum.inl i))).val
  rw [zeroScalarEndpointFamily_back]
  exact (renameEquiv K finSumFinEquiv).left_inv _

theorem prepared_private_odd_split (hd : 0<d) (ho : d%2=1)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (e : Fin r ≃ PreparedParameters.Label q J counts) (p : Space m d q J counts O)
    (P : OuterSpace K (Fin h) m d b) (U : Fin b → Forms K h d)
    (F : OuterSpace K (Fin h) m d f)
    (hi : LinearIndependent K (preparedEvenBiform hO hJ heven p))
    (H : OddCyclesExact U P (p,F)) :
    OddSplitExact (fun i => evenRestorationBiform (evenGenerator hO hJ heven p (e i)))
      (fun i => oddRestorationBiform (privateOddFamily hd ho P U i)) := by
  let eqv : PreparedParameters.Label q J counts ≃ Fin (q+Fintype.card (ProductRows.LayerLabel J counts)) :=
    (Equiv.sumCongr (Equiv.refl (Fin q)) (Fintype.equivFin _)).trans finSumFinEquiv
  let Q := Fin.append (preparedBaseBiform hO hJ heven p) (preparedPositiveBiform hO hJ heven p)
  have hQ (i : PreparedParameters.Label q J counts) : Q (eqv i)=preparedEvenBiform hO hJ heven p i := by
    cases i <;> simp [Q,eqv,preparedBaseBiform,preparedPositiveBiform]
  have hQi : LinearIndependent K Q := by
    convert hi.comp eqv.symm eqv.symm.injective using 1
    funext i
    simpa only [Function.comp_apply,Equiv.apply_symm_apply] using hQ (eqv.symm i)
  have hfull := prepared_odd_split_exact hd ho hO hJ heven U P (p,F) H
  have hright := odd_split_exact_restrict_right Q
    (fun i => preparedOddBiform hd ho U P F (Sum.inl i))
    (fun i => preparedOddBiform hd ho U P F (Sum.inr i)) hQi hfull
  have hnew := odd_split_exact_reindex Q
    (fun i => preparedOddBiform hd ho U P F (Sum.inr i)) (e.trans eqv) (Equiv.refl (Fin b)) hright
  have hnewQ : (fun i => Q ((e.trans eqv) i))=
      (fun i => evenRestorationBiform (evenGenerator hO hJ heven p (e i))) := by
    funext i
    rw [Equiv.trans_apply,hQ]
    apply Subtype.ext
    rfl
  have hnewG : (fun i => preparedOddBiform hd ho U P F (Sum.inr ((Equiv.refl (Fin b)) i)))=
      (fun i => oddRestorationBiform (privateOddFamily hd ho P U i)) := by
    funext i
    apply Subtype.ext
    rfl
  rw [hnewQ,hnewG] at hnew
  exact hnew

theorem prepared_private_endpoint_odd (hd : 0<d) (ho : d%2=1)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (e : Fin r ≃ PreparedParameters.Label q J counts) (p : Space m d q J counts O)
    (P : OuterSpace K (Fin h) m d b) (U : Fin b → Forms K h d)
    (F : OuterSpace K (Fin h) m d f)
    (hi : LinearIndependent K (zeroScalarEndpointFamily hd hO hJ U P (p,F)))
    (H : OddCyclesExact U P (p,F))
    (a : (endpointMultiplication (privateEndpointFamily hd ho hO hJ heven e p P U)).ker)
    (ha : ∀ i,(a.val i).val.IsWeightedHomogeneous (coreParity h m)
      (1-biformSplitEndpointParity (q := r) (f := b) i)) :
    a.val∈oppositeKoszulSpace (privateEndpointFamily hd ho hO hJ heven e p P U)
      (biformSplitEndpointParity (q := r) (f := b)) :=
  odd_split_endpoint _ _ (prepared_private_odd_split hd ho hO hJ heven e p P U F
    (prepared_even_independent_of_full hd hO hJ heven p P U F hi) H) a ha


theorem privateEndpointFamily_full_value (hd : 0<d) (ho : d%2=1)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (e : Fin r ≃ PreparedParameters.Label q J counts) (p : Space m d q J counts O)
    (P : OuterSpace K (Fin h) m d b) (U : Fin b → Forms K h d)
    (F : OuterSpace K (Fin h) m d f) (i : Fin r ⊕ Fin b) :
    privateEndpointFamily hd ho hO hJ heven e p P U (finSumFinEquiv i)=
      zeroScalarEndpointFamily hd hO hJ U P (p,F)
        (Fintype.equivFin _ (Sum.map e (Sum.inr : Fin b → Fin f ⊕ Fin b) i)) := by
  apply Subtype.ext
  apply (renameEquiv K finSumFinEquiv.symm).injective
  simp only [renameEquiv_apply]
  change rename finSumFinEquiv.symm
    (privateSplitEndpoint (fun i => evenGenerator hO hJ heven p (e i))
      (privateOddFamily hd ho P U) (finSumFinEquiv i)).val=_
  rw [privateSplitEndpoint_back,zeroScalarEndpointFamily_back]
  cases i <;> rfl

theorem prepared_private_endpoint_independent (hd : 0<d) (ho : d%2=1)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (e : Fin r ≃ PreparedParameters.Label q J counts) (p : Space m d q J counts O)
    (P : OuterSpace K (Fin h) m d b) (U : Fin b → Forms K h d)
    (F : OuterSpace K (Fin h) m d f)
    (hi : LinearIndependent K (zeroScalarEndpointFamily hd hO hJ U P (p,F))) :
    LinearIndependent K (privateEndpointFamily hd ho hO hJ heven e p P U) := by
  let emb : Fin (r+b) → Fin (Fintype.card (PreparedTarget.Label q f b J counts)) :=
    fun k => Fintype.equivFin _ (Sum.map e (Sum.inr : Fin b → Fin f ⊕ Fin b) (finSumFinEquiv.symm k))
  have hemb : Function.Injective emb :=
    (Fintype.equivFin _).injective.comp
      ((e.injective.sumMap (Sum.inr_injective (α := Fin f) (β := Fin b))).comp finSumFinEquiv.symm.injective)
  convert hi.comp emb hemb using 1
  funext k
  obtain ⟨i,rfl⟩ := finSumFinEquiv.surjective k
  simpa only [Function.comp_apply,emb,Equiv.symm_apply_apply] using
    privateEndpointFamily_full_value hd ho hO hJ heven e p P U F i

end Froberg.PreparedParameters
