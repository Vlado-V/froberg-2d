module

public import Froberg.PreparedLowComponentInstances
public import Froberg.RestoredEndpointSpan
public import Froberg.RestoredQuadraticParameters

@[expose] public section

/-! The actual restored C.2 coordinates have exactly the scalar space and
low components used by the formal separation bridge. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial
variable {K : Type} [Field K] [Infinite K] {h m d q r f : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ} {O : ℕ → Submodule K (Poly K h)}

theorem restoredC2Projection_familySpace
    (idx : Fin r ≃ Label q J counts) (p : RestoredOuterSpace m d q f J counts O) :
    familySpace ((restoredC2Projection idx p).1)=PreparedTarget.preparedScalarSpace p.1.1 := by
  change Submodule.span K (Set.range ((fun i => (p.1.1.1 i).val) ∘ idx))=
    Submodule.span K (Set.range (fun i => (p.1.1.1 i).val))
  rw [idx.surjective.range_comp]

theorem restoredEndpointFamily_lowComponents (hd : 3≤d) (he : d%2=0)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d)
    (heven : ∀ j∈J,j%2=0) (hmin : ∀ j∈J,2≤j)
    (idx : Fin r ≃ Label q J counts)
    (slot : Fin (finrank K (Forms K h d)) → Fin r)
    (p : RestoredOuterSpace m d q f J counts O) :
    PreparedLowComponents
      (Submodule.span K (Set.range (restoredEndpointFamily he hO hJ heven idx slot p.1)))
      (polynomialTensorSpace (Forms K h 0) (familySpace ((restoredC2Projection idx p).1)))
      ⊥ (polynomialTensorSpace (O 2) (Forms K m (d-2))) := by
  rw [restoredC2Projection_familySpace]
  apply PreparedLowComponents.span
  intro i
  exact PreparedTarget.renamed_restored_low_components hd he hO hJ heven hmin idx slot p.1 i

theorem oddPolynomialToForms_linearOuter_val (hd : 1≤d)
    (F : FullBiform K (Fin h) m 1 (d-1)) :
    (oddPolynomialToForms (linearOddForm hd (PreparedTarget.outerVectorEquiv.symm F))).val=
      rename finSumFinEquiv F.val := by
  rw [oddPolynomialToForms_val]
  change rename finSumFinEquiv
    (sumBiformMap (linearOutputTensorEquiv (PreparedTarget.outerVectorEquiv.symm F)))=_
  rw [←PreparedTarget.outerVectorEquiv_val,LinearEquiv.apply_symm_apply]

end Froberg.PreparedParameters
