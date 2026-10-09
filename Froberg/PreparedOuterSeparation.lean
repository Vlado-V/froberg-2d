module

public import Froberg.PreparedBiformFamilies
public import Froberg.BackgroundFlagSpan

@[expose] public section

/-! The C.2 separation certificate on the actual full prepared parameter
space. It is uniform in the later supported scalar deletion. -/
noncomputable section
namespace Froberg.PreparedTarget
open Froberg Module MvPolynomial PreparedParameters
variable {K : Type} [Field K] [Infinite K] {h m d q f u : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ} {O : ℕ → Submodule K (Poly K h)}

def PreparedOuterSeparation (hd : 0<d) (ho : d%2=1)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (U : Fin u → Forms K h d)
    (p : FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O) : Prop :=
  ∀ (D : Submodule K (Forms K (h+m) (2*d))),
    D≤(renameForm (K := K) (d := 2*d) (Fin.natAdd h : Fin m → Fin (h+m))).range →
    formalSquare (Submodule.span K (Set.range
      (fun i => oddPolynomialToForms (preparedOddBiform hd ho U p.1 p.2.2 (Sum.inl i))))) ⊓
      ((formalMixed (embeddedFlagSpace (renameForm (Fin.natAdd h))
        (fun i : Fin q => p.2.1.1 (Sum.inl i)) ⊔
          Submodule.span K (Set.range (backgroundPositiveForms
            (preparedPositiveBiform hO hJ heven p.2.1)
            (fun i => preparedOddBiform hd ho U p.1 p.2.2 (Sum.inr i)))))).map
              (D.mkQ.comp formalPolynomialMultiplication)).comap
                (D.mkQ.comp (formalPolynomialMultiplication (K := K) (n := h+m) (d := d)))=⊥

end Froberg.PreparedTarget
