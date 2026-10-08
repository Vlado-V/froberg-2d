import Froberg.ProjectedDetection

/-! A separated outer-product block in the quadratic coefficient row gives
the literal formal-square condition, uniformly under supported deletions. -/
noncomputable section
namespace Froberg
open Module
variable {K : Type} [Field K] [Infinite K]
variable {V W X Y : Type*}
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module K W]
variable [AddCommGroup X] [Module K X]
variable [AddCommGroup Y] [Module K Y]
variable {f : ℕ}

theorem formalSquare_separated_of_coefficient_row
    (mu : SymmetricSquare K V →ₗ[K] W) (R : W →ₗ[K] Y)
    (A : X →ₗ[K] Y) (q : Fin f → V) (L : Submodule K V)
    (hrow : ∀ x (a : Sym2 (Fin f) → K),
      A x+(∑ s,a s • R (mu (formalPair q s)))=0 → a=0)
    (hL : (formalMixed L).map mu≤A.range.comap R)
    (D : Submodule K W) (hD : D≤A.range.comap R) :
    formalSquare (Submodule.span K (Set.range q)) ⊓
      ((formalMixed L).map (D.mkQ.comp mu)).comap (D.mkQ.comp mu)=⊥ := by
  classical
  let T := A.range.mkQ.comp R
  have hLI : LinearIndependent K (fun s => T (mu (formalPair q s))) := by
    apply Fintype.linearIndependent_iff.mpr
    intro a ha s
    let y : Y := ∑ t,a t • R (mu (formalPair q t))
    have hy : A.range.mkQ y=0 := by
      simpa only [y,T,LinearMap.comp_apply,map_sum,map_smul] using ha
    have hym : y∈A.range := (Submodule.Quotient.mk_eq_zero A.range).mp hy
    obtain ⟨x,hx⟩ := hym
    have hz : A (-x)+y=0 := by rw [map_neg,hx];exact neg_add_cancel y
    exact congrFun (hrow (-x) a hz) s
  have hker (y : W) (hy : R y∈A.range) : T y=0 :=
    (Submodule.Quotient.mk_eq_zero A.range).mpr hy
  exact formalSquare_separated_after_target_deletion mu T D
    (fun y hy => hker y (hD hy)) L (fun y hy => hker y (hL hy)) q hLI

end Froberg
