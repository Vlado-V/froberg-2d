module

public import Froberg.PreparedRestoredRelations
public import Froberg.RestoredScalarCompatibility
public import Froberg.BackgroundFlagSpan

@[expose] public section

/-! The restored even endpoint spans precisely the embedded scalar family
and its positive columns, in the literal ambient coordinates. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial
variable {K : Type} [Field K] [Infinite K] {h m d q r : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ} {O : ℕ → Submodule K (Poly K h)}

theorem restoredEndpointFamily_span (hd : d%2=0)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (idx : Fin r ≃ Label q J counts) (slot : Fin (finrank K (Forms K h d)) → Fin r)
    (hslot : ∀ k,0<degree (idx (slot k))) (p : RestoredSpace m d q J counts O) :
    Submodule.span K (Set.range (restoredEndpointFamily hd hO hJ heven idx slot p))=
      embeddedFlagSpace (renameForm (Fin.natAdd h)) (fun j : Fin q => p.1.1 (Sum.inl j)) ⊔
        Submodule.span K (Set.range
          (evenPolynomialToForms ∘ restoredPositiveBiform hd hO hJ heven idx slot p)) := by
  have hmap :
      (fun i => evenPolynomialToForms (Fin.append
        (restoredBaseBiform hd hO hJ heven idx slot p)
        (restoredPositiveBiform hd hO hJ heven idx slot p) i))=
      Fin.append
        (fun i => evenPolynomialToForms (restoredBaseBiform hd hO hJ heven idx slot p i))
        (fun i => evenPolynomialToForms (restoredPositiveBiform hd hO hJ heven idx slot p i)) := by
    funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;> simp only [Fin.append_left,Fin.append_right]
  have hsplit : restoredEndpointFamily hd hO hJ heven idx slot p=
      (Fin.append
        (fun i => evenPolynomialToForms (restoredBaseBiform hd hO hJ heven idx slot p i))
        (fun i => evenPolynomialToForms (restoredPositiveBiform hd hO hJ heven idx slot p i))) ∘
      restoredEvenIndex idx := by
    funext i
    change evenPolynomialToForms (restoredBiformFamily hd hO hJ heven idx slot p i)=_
    rw [←restored_split_value hd hO hJ heven idx slot p i]
    exact congrFun hmap (restoredEvenIndex idx i)
  rw [hsplit,(restoredEvenIndex idx).surjective.range_comp,span_fin_append,
    restoredBaseBiform_eq_scalar hd hO hJ heven idx slot hslot]
  simp only [evenPolynomialToForms_scalar]
  rw [embeddedFlagSpace,Submodule.map_span,←Set.range_comp]
  rfl

end Froberg.PreparedParameters
