import Froberg.DetectedSymmetricProducts

/-! A detector that annihilates the deleted target gives the same product
separation on the actual projected target. -/
noncomputable section
namespace Froberg
variable {K : Type} [Field K]
variable {V W X : Type*} [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W] [AddCommGroup X] [Module K X]
variable {I : Type*}

theorem formalSquare_separated_after_target_deletion
    (mu : SymmetricSquare K V →ₗ[K] W) (T : W →ₗ[K] X)
    (D : Submodule K W) (hD : D≤T.ker)
    (L : Submodule K V) (hL : (formalMixed L).map mu≤T.ker)
    (q : I → V) (hq : LinearIndependent K (fun p => T (mu (formalPair (K := K) q p)))) :
    formalSquare (Submodule.span K (Set.range q)) ⊓
      ((formalMixed L).map (D.mkQ.comp mu)).comap (D.mkQ.comp mu)=⊥ := by
  let T' : (W ⧸ D) →ₗ[K] X := D.liftQ T hD
  apply formalSquare_separated_from_mixed_of_detected_products (D.mkQ.comp mu) T' L
  · rintro _ ⟨x,hx,rfl⟩
    exact hL ⟨x,hx,rfl⟩
  · exact hq

end Froberg
