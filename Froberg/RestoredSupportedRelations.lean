import Froberg.RestoredFormalRelations
import Froberg.SupportedDeletionProjection
import Froberg.RestorationRename

/-! The formal relation comparison after the manuscript's supported
scalar deletion, using literal restored homogeneous polynomials. -/
noncomputable section
namespace Froberg
open Module MvPolynomial
variable {K : Type} [Field K] [Infinite K] {h m d r : ℕ}

theorem restored_supported_formal_relations
    (htwo : (2 : K)≠0)
    (g : Fin r → evenRestorationSpace (K := K) (coreWeight h m) d)
    (hi : LinearIndependent K (restorationForms (coreWeight h m) g))
    (D : Submodule K (Forms K (h+m) (2*d)))
    (hD : D≤(renameForm (K := K) (d := 2*d) (Fin.natAdd h : Fin m → Fin (h+m))).range)
    (hodd : ∀ a : (endpointMultiplication (restorationForms (coreWeight h m) g)).ker,
      (∀ i,(a.val i).val.IsWeightedHomogeneous (coreParity h m) 1) →
      a.val∈oppositeKoszulSpace (restorationForms (coreWeight h m) g) (fun _ => 0))
    (degree : Fin r → ℕ) (Q : Submodule K (Forms K (h+m) d))
    (hQ : Q≤Submodule.span K (Set.range (restorationForms (coreWeight h m) g)))
    (hlabel : ∀ i,degree i=0 → restorationForms (coreWeight h m) g i∈Q)
    (hreduce : ∀ c : Fin r → evenRestorationSpace (K := K) (coreWeight h m) d,
      PolynomialRestoration.row (evenRestorationSpace (coreWeight h m) d).subtype
        (positiveWeightProjection (coreWeight h m) d) g c=0 →
      ∃ (M : Fin r → Fin r → K)
        (z : retainedScalarCoefficients (K := K) (coreWeight h m) d degree),
        c-coefficientBoundary g M=z.val) :
    (D.mkQ.comp formalPolynomialMultiplication).ker ⊓
        formalMixed (Submodule.span K (Set.range (restorationForms (coreWeight h m) g)))=
      (D.mkQ.comp formalPolynomialMultiplication).ker ⊓
        formalProducts Q (renameForm (K := K) (d := d) (Fin.natAdd h : Fin m → Fin (h+m))).range := by
  exact restored_projected_formal_relations htwo (coreWeight h m) g hi D.mkQ
    (supported_deletion_odd_zero D hD) (supported_deletion_positive_zero D hD)
    hodd degree Q _ hQ hlabel core_weight_zero_mem_scalar_range hreduce

end Froberg
