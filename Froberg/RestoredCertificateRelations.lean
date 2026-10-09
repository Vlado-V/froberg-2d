module

public import Froberg.RestoredCommonSelection
public import Froberg.PreparedRestoredRelations

@[expose] public section

/-! A common restored certificate supplies the background independence
and odd-cycle hypotheses of the literal formal-relation theorem. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace Froberg
open Module MvPolynomial
variable {K : Type} [Field K] [Infinite K] {h m d r : ℕ}

@[simp] theorem biformRestorationForms_back
    (g : Fin r → evenRestorationSpace (K := K) (blockWeight h m) d) (i : Fin r) :
    rename finSumFinEquiv.symm (biformRestorationForms g i).val=(g i).val := by
  change rename finSumFinEquiv.symm (rename finSumFinEquiv (g i).val)=(g i).val
  exact (renameEquiv K finSumFinEquiv).left_inv (g i).val

theorem biform_restoration_odd_cycle_zero
    (g : Fin r → evenRestorationSpace (K := K) (blockWeight h m) d)
    (hinj : Function.Injective (PreparedParameters.restoredOddRowLinear g))
    (a : (endpointMultiplication (biformRestorationForms g)).ker)
    (ha : ∀ i,(a.val i).val.IsWeightedHomogeneous (coreParity h m) 1) : a.val=0 := by
  have hpar (i : Fin r) :
      (rename finSumFinEquiv.symm (a.val i).val).IsWeightedHomogeneous
        (fun x => (blockWeight h m x : ZMod 2)) 1 := by
    apply weighted_homogeneous_rename finSumFinEquiv.symm.toEmbedding
    simpa only [coreParity_eq_blockParity,Equiv.coe_toEmbedding] using ha i
  let c : Fin r → biformParitySpace K h m d 1 := fun i =>
    ⟨rename finSumFinEquiv.symm (a.val i).val,
      (a.val i).property.rename_isHomogeneous,hpar i⟩
  have hc : PreparedParameters.restoredOddRowLinear g c=0 := by
    have hz := congrArg (fun x : Forms K (h+m) (2*d) => rename finSumFinEquiv.symm x.val) a.property
    rw [endpointMultiplication_val] at hz
    simp only [map_sum,map_mul,Submodule.coe_zero,map_zero,biformRestorationForms_back] at hz
    exact hz
  have hcz : c=0 := hinj (hc.trans (map_zero (PreparedParameters.restoredOddRowLinear g)).symm)
  funext i
  apply Subtype.ext
  apply (renameEquiv K finSumFinEquiv.symm).injective
  have hi := congrArg (fun v : Fin r → biformParitySpace K h m d 1 => (v i).val) hcz
  change rename finSumFinEquiv.symm (a.val i).val=0 at hi
  change rename finSumFinEquiv.symm (a.val i).val=rename finSumFinEquiv.symm 0
  rw [map_zero]
  exact hi

namespace PreparedParameters
variable {q f : ℕ} {J : Finset ℕ} {counts : ℕ → ℕ}
variable {O : ℕ → Submodule K (Poly K h)}

theorem restoredOuterEndpoint_castAdd (hdp : 1≤d) (hd : d%2=0)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (idx : Fin r ≃ Label q J counts) (slot : Fin (finrank K (Forms K h d)) → Fin r)
    (p : RestoredOuterSpace m d q f J counts O) (i : Fin r) :
    restoredOuterEndpoint hdp hd hO hJ heven idx slot p (Fin.castAdd f i)=
      restoredEndpointFamily hd hO hJ heven idx slot p.1 i := by
  apply Subtype.ext
  change rename finSumFinEquiv (biformSplitFamily
    (restoredBiformFamily hd hO hJ heven idx slot p.1)
    (fun j => linearOddForm hdp (PreparedTarget.outerVectorEquiv.symm (p.2 j)))
    (finSumFinEquiv.symm (Fin.castAdd f i))).val=
    rename finSumFinEquiv (restoredFamilyLinear hd hO hJ heven idx slot p.1 i).val
  rw [finSumFinEquiv_symm_apply_castAdd]
  rfl

theorem RestoredCertificate.background_independent (hdp : 1≤d) (hd : d%2=0)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (idx : Fin r ≃ Label q J counts) (slot : Fin (finrank K (Forms K h d)) → Fin r)
    (p : RestoredOuterSpace m d q f J counts O)
    (cert : RestoredCertificate hdp hd hO hJ heven idx slot p) :
    LinearIndependent K (restoredEndpointFamily hd hO hJ heven idx slot p.1) := by
  have hi := cert.independent.comp (Fin.castAdd f) (Fin.castAdd_injective r f)
  simpa only [Function.comp_def,restoredOuterEndpoint_castAdd] using hi

theorem restored_certificate_formal_relations (hdp : 1≤d) (hd : d%2=0)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (hpos : ∀ j∈J,0<j)
    (idx : Fin r ≃ Label q J counts) (slot : Fin (finrank K (Forms K h d)) → Fin r)
    (hslot : ∀ k,0<degree (idx (slot k)))
    (p : RestoredOuterSpace m d q f J counts O)
    (cert : RestoredCertificate hdp hd hO hJ heven idx slot p)
    (D : Submodule K (Forms K (h+m) (2*d)))
    (hD : D≤(renameForm (K := K) (d := 2*d) (Fin.natAdd h : Fin m → Fin (h+m))).range) :
    (D.mkQ.comp formalPolynomialMultiplication).ker ⊓
        formalMixed (Submodule.span K (Set.range (restoredEndpointFamily hd hO hJ heven idx slot p.1)))=
      (D.mkQ.comp formalPolynomialMultiplication).ker ⊓
        formalProducts ((Submodule.span K (Set.range (fun j : Fin q => p.1.1.1 (Sum.inl j)))).map
          (renameForm (Fin.natAdd h)))
          (renameForm (K := K) (d := d) (Fin.natAdd h : Fin m → Fin (h+m))).range := by
  apply prepared_restored_formal_relations hd hO hJ heven hpos idx slot hslot p.1
    (cert.background_independent hdp hd hO hJ heven idx slot p) D hD
  · intro a ha
    have hz := biform_restoration_odd_cycle_zero
      (restoredFamilyLinear hd hO hJ heven idx slot p.1) cert.background_odd_injective a ha
    rw [hz]
    exact Submodule.zero_mem _
  · exact cert.positive_reduction

end PreparedParameters
end Froberg
