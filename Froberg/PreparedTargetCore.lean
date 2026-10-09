module

public import Froberg.PreparedTargetWitness

@[expose] public section

/-! The finite prepared upper-target witness, independent of the eventual
quadratic endpoint theorem. -/
noncomputable section
namespace Froberg.PreparedTarget
open Froberg Module MvPolynomial
variable {K : Type} [Field K] {h m d H u : ℕ}
attribute [local instance] tensorGroup

def HasUpperWitness (d f r q : ℕ) (frame : Fin H → Forms K h 2)
    (U : Fin u → Forms K h d) (P : Fin u → MvPolynomial (Fin h ⊕ Fin m) K) : Prop :=
  ∃ p : Space m d q f u (activeEvenIndices d) (targetLayerCount d h m r) (targetLayerOutput frame),
    p.2.2=0 ∧ ∀ b,2≤b → b≤2*d → TargetLift
      ((Submodule.span K (Set.range (renamedGenerator U P p)))*Forms K (h+m) d) d b

end Froberg.PreparedTarget
