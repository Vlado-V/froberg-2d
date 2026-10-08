import Froberg.PreparedOddVectorCriteria

/-! The full fixed-pure parameter space surjects onto the complete F+P
vector family and all scalar parts. The remaining high coefficients are
free, so every nonempty joint row open pulls back to the prepared space. -/
noncomputable section
namespace Froberg.PreparedTarget
open Froberg Module MvPolynomial Quartic VectorMultiplicationCoordinates
variable {K : Type} [Field K] [Infinite K] {h m d q f u : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ} {O : ℕ → Submodule K (Poly K h)}

def preparedOddVectorParameters :
    FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O →ₗ[K]
      ScalarVectorParameters K h m d (f+u) (Fintype.card (PreparedParameters.Label q J counts)) where
  toFun p := (combinedVectorEnumeration p.1 p.2.2,scalarEnumeration p.2.1)
  map_add' p p' := by
    apply Prod.ext
    · funext i
      rcases hi : (finSumFinEquiv.symm i : Fin f ⊕ Fin u) with j | j <;>
        simp only [combinedVectorEnumeration,Prod.fst_add,Prod.snd_add,hi,Sum.elim_inl,Sum.elim_inr,
          Pi.add_apply,map_add]
    · rfl
  map_smul' a p := by
    apply Prod.ext
    · funext i
      change outerVectorEquiv.symm
        (Sum.elim (a • p.2.2) (a • p.1) (finSumFinEquiv.symm i))=
        a • outerVectorEquiv.symm (Sum.elim p.2.2 p.1 (finSumFinEquiv.symm i))
      rcases hi : (finSumFinEquiv.symm i : Fin f ⊕ Fin u) with j | j <;>
        simp only [hi,Sum.elim_inl,Sum.elim_inr,Pi.smul_apply,map_smul]
    · rfl

theorem preparedOddVectorParameters_surjective : Function.Surjective
    (preparedOddVectorParameters (K := K) (h := h) (m := m) (d := d) (q := q) (f := f)
      (u := u) (J := J) (counts := counts) (O := O)) := by
  rintro ⟨g,Q⟩
  refine ⟨(fun j => outerVectorEquiv (g (finSumFinEquiv (Sum.inr j))),
    ((fun i => Q (Fintype.equivFin _ i),0),
      fun j => outerVectorEquiv (g (finSumFinEquiv (Sum.inl j))))),?_⟩
  apply Prod.ext
  · funext i
    change outerVectorEquiv.symm (Sum.elim
      (fun j : Fin f => outerVectorEquiv (g (finSumFinEquiv (Sum.inl j))))
      (fun j : Fin u => outerVectorEquiv (g (finSumFinEquiv (Sum.inr j))))
      (finSumFinEquiv.symm i))=g i
    have he : Sum.elim
        (fun j : Fin f => outerVectorEquiv (g (finSumFinEquiv (Sum.inl j))))
        (fun j : Fin u => outerVectorEquiv (g (finSumFinEquiv (Sum.inr j))))=
        fun j : Fin f ⊕ Fin u => outerVectorEquiv (g (finSumFinEquiv j)) := by
      funext j
      cases j <;> rfl
    rw [he]
    dsimp only
    rw [Equiv.apply_symm_apply,LinearEquiv.symm_apply_apply]
  · funext i
    exact congrArg Q ((Fintype.equivFin _).apply_symm_apply i)

end Froberg.PreparedTarget
