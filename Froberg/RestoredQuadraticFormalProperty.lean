import Froberg.RestoredQuadraticLowComponents

/-! The genuine coefficient-row open implies C.2 for every scalar-supported
endpoint deletion and the literal restored background. -/
noncomputable section
set_option maxHeartbeats 1800000
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial
variable {K : Type} [Field K] [Infinite K]
variable {h m d q r f c : ℕ} {J : Finset ℕ} {counts : ℕ → ℕ}
variable {O : ℕ → Submodule K (Poly K h)}

/-- Uniform C.2 separation for every scalar-supported target deletion. -/
def RestoredFormalQuadraticSeparation (hdp : 1≤d) (he : d%2=0)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (idx : Fin r ≃ Label q J counts)
    (slot : Fin (finrank K (Forms K h d)) → Fin r)
    (p : RestoredOuterSpace m d q f J counts O) : Prop :=
  ∀ D : Submodule K (Forms K (h+m) (2*d)),
    D≤(renameForm (K := K) (d := 2*d)
      (Fin.natAdd h : Fin m → Fin (h+m))).range →
    formalSquare (Submodule.span K (Set.range (fun i => oddPolynomialToForms
      (linearOddForm hdp (PreparedTarget.outerVectorEquiv.symm (p.2 i)))))) ⊓
      ((formalMixed (Submodule.span K (Set.range
        (restoredEndpointFamily he hO hJ heven idx slot p.1)))).map
        (D.mkQ.comp formalPolynomialMultiplication)).comap
        (D.mkQ.comp (formalPolynomialMultiplication (K := K) (n := h+m) (d := d)))=⊥

end Froberg.PreparedParameters
