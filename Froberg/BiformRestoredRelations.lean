import Froberg.RestoredSupportedRelations

/-! The restored prepared polynomials on X and Y give the literal formal
relation equality after renaming variables into the single endpoint ring. -/
noncomputable section
namespace Froberg
open Module MvPolynomial
variable {K : Type} [Field K] [Infinite K] {h m d r : ℕ}

def biformRestorationForms
    (g : Fin r → evenRestorationSpace (K := K) (blockWeight h m) d) :
    Fin r → Forms K (h+m) d :=
  restorationForms (blockWeight h m ∘ finSumFinEquiv.symm)
    (fun i => evenRestorationRenameEquiv finSumFinEquiv (blockWeight h m) d (g i))

theorem biform_restored_supported_relations
    (htwo : (2 : K)≠0)
    (g : Fin r → evenRestorationSpace (K := K) (blockWeight h m) d)
    (hi : LinearIndependent K (biformRestorationForms g))
    (D : Submodule K (Forms K (h+m) (2*d)))
    (hD : D≤(renameForm (K := K) (d := 2*d) (Fin.natAdd h : Fin m → Fin (h+m))).range)
    (hodd : ∀ a : (endpointMultiplication (biformRestorationForms g)).ker,
      (∀ i,(a.val i).val.IsWeightedHomogeneous (coreParity h m) 1) →
      a.val∈oppositeKoszulSpace (biformRestorationForms g) (fun _ => 0))
    (degree : Fin r → ℕ) (Q : Submodule K (Forms K (h+m) d))
    (hQ : Q≤Submodule.span K (Set.range (biformRestorationForms g)))
    (hlabel : ∀ i,degree i=0 → biformRestorationForms g i∈Q)
    (hreduce : ∀ c : Fin r → evenRestorationSpace (K := K) (blockWeight h m) d,
      PolynomialRestoration.row (evenRestorationSpace (blockWeight h m) d).subtype
        (positiveWeightProjection (blockWeight h m) d) g c=0 →
      ∃ (M : Fin r → Fin r → K)
        (z : retainedScalarCoefficients (K := K) (blockWeight h m) d degree),
        c-coefficientBoundary g M=z.val) :
    (D.mkQ.comp formalPolynomialMultiplication).ker ⊓
        formalMixed (Submodule.span K (Set.range (biformRestorationForms g)))=
      (D.mkQ.comp formalPolynomialMultiplication).ker ⊓
        formalProducts Q (renameForm (K := K) (d := d) (Fin.natAdd h : Fin m → Fin (h+m))).range := by
  have hw : ∀ x,blockWeight h m x≤1 := by intro x;cases x <;> simp [blockWeight]
  have hr := restoration_reduction_rename finSumFinEquiv (blockWeight h m) hw g degree hreduce
  refine restored_projected_formal_relations htwo
    (blockWeight h m ∘ finSumFinEquiv.symm)
    (fun i => evenRestorationRenameEquiv finSumFinEquiv (blockWeight h m) d (g i)) hi D.mkQ
    ?_ ?_ ?_ degree Q _ hQ hlabel ?_ hr
  · intro z hz
    rw [←coreWeight_eq_blockWeight]
    exact supported_deletion_odd_zero D hD z hz
  · simpa only [←coreWeight_eq_blockWeight] using supported_deletion_positive_zero D hD
  · intro a ha
    apply hodd a
    intro i
    change (a.val i).val.IsWeightedHomogeneous (fun x => (coreWeight h m x : ZMod 2)) 1
    rw [coreWeight_eq_blockWeight]
    exact ha i
  · intro f hf
    apply core_weight_zero_mem_scalar_range f
    simpa only [←coreWeight_eq_blockWeight] using hf

end Froberg
