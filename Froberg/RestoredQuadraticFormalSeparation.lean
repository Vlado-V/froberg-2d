module

public import Froberg.RestoredQuadraticNuisance
public import Froberg.RestoredQuadraticFormalProperty
public import Froberg.PreparedQuadraticFormalSeparation

@[expose] public section

/-! The genuine coefficient-row open implies C.2 for every scalar-supported
endpoint deletion and the literal restored background. -/
noncomputable section
set_option maxHeartbeats 1800000
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial
variable {K : Type} [Field K] [Infinite K]
variable {h m d q r f c : ℕ} {J : Finset ℕ} {counts : ℕ → ℕ}
variable {O : ℕ → Submodule K (Poly K h)}

/-- C.2 in exactly the endpoint coordinates used by the restored comparison. -/
theorem restored_quadratic_formal_separation
    (hd : 3≤d) (hdp : 1≤d) (he : d%2=0)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d)
    (heven : ∀ j∈J,j%2=0) (hmin : ∀ j∈J,2≤j)
    (idx : Fin r ≃ Label q J counts)
    (slot : Fin (finrank K (Forms K h d)) → Fin r)
    (T : Poly K h →ₗ[K] (Fin c → K))
    (hT : T.comp (homogeneousComponent 2)=T) (hO₂ : O 2≤T.ker)
    (p : RestoredOuterSpace m d q f J counts O)
    (hsep : QuadraticSeparated T (restoredC2Projection idx p))
    (D : Submodule K (Forms K (h+m) (2*d)))
    (hD : D≤(renameForm (K := K) (d := 2*d)
      (Fin.natAdd h : Fin m → Fin (h+m))).range) :
    formalSquare (Submodule.span K (Set.range (fun i => oddPolynomialToForms
      (linearOddForm hdp (PreparedTarget.outerVectorEquiv.symm (p.2 i)))))) ⊓
      ((formalMixed (Submodule.span K (Set.range
        (restoredEndpointFamily he hO hJ heven idx slot p.1)))).map
        (D.mkQ.comp formalPolynomialMultiplication)).comap
        (D.mkQ.comp (formalPolynomialMultiplication (K := K) (n := h+m) (d := d)))=⊥ := by
  let P : Fin 0 → FullBiform K (Fin h) m 1 (d-1) := Fin.elim0
  refine prepared_quadratic_formal_separation (by omega) T hT
    (restoredC2Projection idx p).1 P p.2 _ ?_ (O 2) hO₂ _ ?_
    (quadraticSeparated_empty_private T _ hsep) D hD
  · intro i
    exact oddPolynomialToForms_linearOuter_val hdp (p.2 i)
  · have hempty : Submodule.span K (Set.range (fun i : Fin 0 =>
        rename finSumFinEquiv (P i).val))=⊥ := by simp
    rw [hempty]
    exact restoredEndpointFamily_lowComponents hd he hO hJ heven hmin idx slot p

theorem QuadraticSeparated.restored_formal
    (hd : 3≤d) (hdp : 1≤d) (he : d%2=0)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d)
    (heven : ∀ j∈J,j%2=0) (hmin : ∀ j∈J,2≤j)
    (idx : Fin r ≃ Label q J counts)
    (slot : Fin (finrank K (Forms K h d)) → Fin r)
    (T : Poly K h →ₗ[K] (Fin c → K))
    (hT : T.comp (homogeneousComponent 2)=T) (hO₂ : O 2≤T.ker)
    (p : RestoredOuterSpace m d q f J counts O)
    (hsep : QuadraticSeparated T (restoredC2Projection idx p)) :
    RestoredFormalQuadraticSeparation hdp he hO hJ heven idx slot p :=
  restored_quadratic_formal_separation hd hdp he hO hJ heven hmin idx slot T hT hO₂ p hsep

end Froberg.PreparedParameters
