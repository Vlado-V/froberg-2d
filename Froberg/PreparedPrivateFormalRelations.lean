module

public import Froberg.PrivateFormalRelations
public import Froberg.PreparedBiformFamilies
public import Froberg.PreparedBiformCompatibility
public import Froberg.BackgroundFlagSpan

@[expose] public section

/-! The actual prepared even/private-odd background has exactly the old
scalar formal relations after any supported scalar target deletion. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial
variable {K : Type} [Field K] [Infinite K]
variable {h m d q r b : ℕ} {J : Finset ℕ} {counts : ℕ → ℕ}
variable {O : ℕ → Submodule K (Poly K h)}

def privateEndpointFamily (hd : 0<d) (ho : d%2=1)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (e : Fin r ≃ Label q J counts) (p : Space m d q J counts O)
    (P : Fin b → FullBiform K (Fin h) m 1 (d-1)) (U : Fin b → Forms K h d) :
    Fin (r+b) → Forms K (h+m) d :=
  privateSplitEndpoint (fun i => evenGenerator hO hJ heven p (e i)) (privateOddFamily hd ho P U)

theorem privateEndpointFamily_scalar (hd : 0<d) (ho : d%2=1)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (e : Fin r ≃ Label q J counts) (p : Space m d q J counts O)
    (P : Fin b → FullBiform K (Fin h) m 1 (d-1)) (U : Fin b → Forms K h d)
    (i : Fin r) (j : Fin q) (he : e i=Sum.inl j) :
    privateEndpointFamily hd ho hO hJ heven e p P U (finSumFinEquiv (Sum.inl i))=
      renameForm (Fin.natAdd h) (p.1 (Sum.inl j)) := by
  apply Subtype.ext
  apply (renameEquiv K finSumFinEquiv.symm).injective
  simp only [renameEquiv_apply]
  change rename finSumFinEquiv.symm
    (privateSplitEndpoint (fun i => evenGenerator hO hJ heven p (e i))
      (privateOddFamily hd ho P U) (finSumFinEquiv (Sum.inl i))).val=_
  rw [privateSplitEndpoint_back]
  change generator p (e i)=rename finSumFinEquiv.symm (rename (Fin.natAdd h) (p.1 (Sum.inl j)).val)
  rw [he,rename_rename]
  rw [show (finSumFinEquiv.symm ∘ Fin.natAdd h : Fin m → Fin h ⊕ Fin m)=Sum.inr from
    funext fun k => finSumFinEquiv_symm_apply_natAdd k]
  simp [generator,scalar,high]

theorem prepared_private_formal_relations (hd : 0<d) (ho : d%2=1)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (hpos : ∀ j∈J,0<j) (e : Fin r ≃ Label q J counts)
    (p : Space m d q J counts O) (P : Fin b → FullBiform K (Fin h) m 1 (d-1))
    (U : Fin b → Forms K h d)
    (hi : LinearIndependent K (privateEndpointFamily hd ho hO hJ heven e p P U))
    (D : Submodule K (Forms K (h+m) (2*d)))
    (hD : D≤(renameForm (K := K) (d := 2*d) (Fin.natAdd h : Fin m → Fin (h+m))).range)
    (hodd : ∀ a : (endpointMultiplication (privateEndpointFamily hd ho hO hJ heven e p P U)).ker,
      (∀ i,(a.val i).val.IsWeightedHomogeneous (coreParity h m)
        (1-biformSplitEndpointParity (q := r) (f := b) i)) →
      a.val∈oppositeKoszulSpace (privateEndpointFamily hd ho hO hJ heven e p P U)
        (biformSplitEndpointParity (q := r) (f := b)))
    (hreduce : ∀ (c : Fin r → evenRestorationSpace (K := K) (outputWeight (σ := Fin h) (n := m)) d)
      (v : Fin b → oddRestorationSpace (K := K) (outputWeight (σ := Fin h) (n := m)) d),
      SplitRestoration.row (evenRestorationSpace outputWeight d).subtype
        (oddRestorationSpace outputWeight d).subtype (positiveWeightProjection outputWeight d)
        (fun i => evenGenerator hO hJ heven p (e i)) (privateOddFamily hd ho P U) (c,v)=0 →
      ∃ (M : Fin r → Fin r → K) (C : Fin b → Fin b → K)
        (z : retainedScalarCoefficients (K := K) outputWeight d (fun i => degree (e i))),
        c-coefficientBoundary (fun i => evenGenerator hO hJ heven p (e i)) M=z.val ∧
        v=coefficientBoundary (privateOddFamily hd ho P U) C) :
    (D.mkQ.comp formalPolynomialMultiplication).ker ⊓
        formalMixed (Submodule.span K (Set.range (privateEndpointFamily hd ho hO hJ heven e p P U)))=
      (D.mkQ.comp formalPolynomialMultiplication).ker ⊓
        formalProducts ((Submodule.span K (Set.range (fun j : Fin q => p.1 (Sum.inl j)))).map
          (renameForm (Fin.natAdd h)))
          (renameForm (K := K) (d := d) (Fin.natAdd h : Fin m → Fin (h+m))).range := by
  apply private_split_supported_relations (fun i => evenGenerator hO hJ heven p (e i)) (privateOddFamily hd ho P U)
    hi D hD hodd (fun i => degree (e i)) _ _ _ hreduce
  · rw [Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨a,⟨j,rfl⟩,rfl⟩
    rw [←privateEndpointFamily_scalar hd ho hO hJ heven e p P U
      (e.symm (Sum.inl j)) j (e.apply_symm_apply _)]
    exact Submodule.subset_span ⟨_,rfl⟩
  · intro i hi0
    cases he : e i with
    | inl j =>
      change privateEndpointFamily hd ho hO hJ heven e p P U (finSumFinEquiv (Sum.inl i))∈_
      rw [privateEndpointFamily_scalar hd ho hO hJ heven e p P U i j he]
      exact ⟨_,Submodule.subset_span ⟨j,rfl⟩,rfl⟩
    | inr a =>
      rw [he] at hi0
      have hp := hpos a.1.val a.1.property
      change a.1.val=0 at hi0
      omega


def privateBackgroundFlagIndex (e : Fin r ≃ Label q J counts) :
    (Fin q ⊕ (Fin (Fintype.card (ProductRows.LayerLabel J counts)) ⊕ Fin b)) ≃ Fin (r+b) :=
  (Equiv.sumAssoc _ _ _).symm.trans
    ((Equiv.sumCongr
      ((Equiv.sumCongr (Equiv.refl (Fin q)) (Fintype.equivFin _).symm).trans e.symm)
      (Equiv.refl (Fin b))).trans finSumFinEquiv)

theorem privateEndpointFamily_flag_reindex {f : ℕ} (hd : 0<d) (ho : d%2=1)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (e : Fin r ≃ Label q J counts) (p : Space m d q J counts O)
    (P : Fin b → FullBiform K (Fin h) m 1 (d-1)) (U : Fin b → Forms K h d)
    (F : PreparedTarget.OuterSpace K (Fin h) m d f) :
    privateEndpointFamily hd ho hO hJ heven e p P U ∘ privateBackgroundFlagIndex e=
      Sum.elim (fun j => renameForm (Fin.natAdd h) (p.1 (Sum.inl j)))
        (backgroundPositiveForms (PreparedTarget.preparedPositiveBiform hO hJ heven p)
          (fun j => PreparedTarget.preparedOddBiform hd ho U P F (Sum.inr j))) := by
  funext k
  rcases k with j | (j | j)
  · change privateEndpointFamily hd ho hO hJ heven e p P U
      (finSumFinEquiv (Sum.inl (e.symm (Sum.inl j))))=_
    exact privateEndpointFamily_scalar hd ho hO hJ heven e p P U _ j (e.apply_symm_apply _)
  · apply Subtype.ext
    apply (renameEquiv K finSumFinEquiv.symm).injective
    simp only [renameEquiv_apply,Function.comp_apply]
    change rename finSumFinEquiv.symm
      (privateSplitEndpoint (fun i => evenGenerator hO hJ heven p (e i))
        (privateOddFamily hd ho P U)
        (finSumFinEquiv (Sum.inl (e.symm (Sum.inr ((Fintype.equivFin _).symm j)))))).val=_
    rw [privateSplitEndpoint_back]
    change generator p (e (e.symm (Sum.inr ((Fintype.equivFin _).symm j))))=
      rename finSumFinEquiv.symm (rename finSumFinEquiv
        (generator p (Sum.inr ((Fintype.equivFin _).symm j))))
    rw [Equiv.apply_symm_apply]
    exact ((renameEquiv K finSumFinEquiv).left_inv _).symm
  · apply Subtype.ext
    apply (renameEquiv K finSumFinEquiv.symm).injective
    simp only [renameEquiv_apply,Function.comp_apply]
    change rename finSumFinEquiv.symm
      (privateSplitEndpoint (fun i => evenGenerator hO hJ heven p (e i))
        (privateOddFamily hd ho P U) (finSumFinEquiv (Sum.inr j))).val=_
    rw [privateSplitEndpoint_back]
    have hG : (PreparedTarget.preparedOddBiform hd ho U P F (Sum.inr j)).val=
        (P j).val+rename Sum.inl (U j).val := rfl
    simp only [Sum.elim_inr,backgroundPositiveForms,oddPolynomialToForms_val,privateOddFamily_val,hG]
    exact ((renameEquiv K finSumFinEquiv).left_inv _).symm

theorem privateEndpointFamily_flag_span {f : ℕ} (hd : 0<d) (ho : d%2=1)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (e : Fin r ≃ Label q J counts) (p : Space m d q J counts O)
    (P : Fin b → FullBiform K (Fin h) m 1 (d-1)) (U : Fin b → Forms K h d)
    (F : PreparedTarget.OuterSpace K (Fin h) m d f) :
    Submodule.span K (Set.range (privateEndpointFamily hd ho hO hJ heven e p P U))=
      embeddedFlagSpace (renameForm (Fin.natAdd h)) (fun j : Fin q => p.1 (Sum.inl j)) ⊔
        Submodule.span K (Set.range (backgroundPositiveForms
          (PreparedTarget.preparedPositiveBiform hO hJ heven p)
          (fun j => PreparedTarget.preparedOddBiform hd ho U P F (Sum.inr j)))) := by
  rw [←(privateBackgroundFlagIndex (b := b) e).surjective.range_comp
    (privateEndpointFamily hd ho hO hJ heven e p P U),
    privateEndpointFamily_flag_reindex hd ho hO hJ heven e p P U F,
    Set.Sum.elim_range,Submodule.span_union]
  simp only [embeddedFlagSpace,Submodule.map_span,←Set.range_comp]
  rfl

end Froberg.PreparedParameters
