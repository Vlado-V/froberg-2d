import Froberg.PreparedPrivateOddExact
import Froberg.PrivatePreparedOpen

/-! The full prepared certificate directly supplies the original scalar
formal-relation equality on the private background used for replacement. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial PreparedTarget
variable {K : Type} [Field K] [Infinite K]
variable {h m d q r f b : ℕ} {J : Finset ℕ} {counts : ℕ → ℕ}
variable {O : ℕ → Submodule K (Poly K h)}

theorem prepared_private_flag_formal_relations (htwo : (2 : K)≠0) (hd : 0<d) (ho : d%2=1)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (hpos : ∀ j∈J,0<j) (e : Fin r ≃ PreparedParameters.Label q J counts)
    (U : Fin b → Forms K h d)
    (p : FullPreparedParameters.FixedPureZeroScalarSpace m d q f b J counts O)
    (hi : LinearIndependent K (zeroScalarEndpointFamily hd hO hJ U p.1 p.2))
    (H : OddCyclesExact U p.1 p.2)
    (hreduce : FullPreparedParameters.PrivateSplitReduction hd ho hO hJ heven e U p)
    (D : Submodule K (Forms K (h+m) (2*d)))
    (hD : D≤(renameForm (K := K) (d := 2*d) (Fin.natAdd h : Fin m → Fin (h+m))).range) :
    (D.mkQ.comp formalPolynomialMultiplication).ker ⊓
        formalMixed (embeddedFlagSpace (renameForm (Fin.natAdd h))
          (fun j : Fin q => p.2.1.1 (Sum.inl j)) ⊔
          Submodule.span K (Set.range (backgroundPositiveForms
            (preparedPositiveBiform hO hJ heven p.2.1)
            (fun j => preparedOddBiform hd ho U p.1 p.2.2 (Sum.inr j)))))=
      (D.mkQ.comp formalPolynomialMultiplication).ker ⊓
        formalProducts (embeddedFlagSpace (renameForm (Fin.natAdd h))
          (fun j : Fin q => p.2.1.1 (Sum.inl j)))
          (renameForm (K := K) (d := d) (Fin.natAdd h : Fin m → Fin (h+m))).range := by
  have hf := prepared_private_formal_relations htwo hd ho hO hJ heven hpos e p.2.1 p.1 U
    (prepared_private_endpoint_independent hd ho hO hJ heven e p.2.1 p.1 U p.2.2 hi)
    D hD (prepared_private_endpoint_odd hd ho hO hJ heven e p.2.1 p.1 U p.2.2 hi H) hreduce
  rw [privateEndpointFamily_flag_span hd ho hO hJ heven e p.2.1 p.1 U p.2.2] at hf
  exact hf

end Froberg.PreparedParameters
