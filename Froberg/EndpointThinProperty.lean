import Froberg.OddEndpointScalarSlices

/-! A fixed proposition in the three generator tuples. This presentation
lets family equalities be applied without exposing dependent quotient
instances in the closed-slice definition. -/
noncomputable section
namespace Froberg
open Module BilinearScalarFamily BilinearCovectorStrata
variable {K : Type} [Field K] [Infinite K] {h m d q f u : ℕ}

def OddEndpointThin
    (Q : Fin q → biformParitySpace K h m d 0)
    (F : Fin f → biformParitySpace K h m d 1)
    (G : Fin u → biformParitySpace K h m d 1) (C : ℝ) : Prop :=
  HasClosedKernelSlices (oddEndpointScalarAction Q F G)
    (thinSlices (finrank K (oddTargetSpace
      ((fun i => (blockWeight h m i : ZMod 2)) ∘ finSumFinEquiv.symm)
      (backgroundEnumeratedForms Q F G))) C)

theorem OddEndpointThin.congr
    {Q Q' : Fin q → biformParitySpace K h m d 0}
    {F F' : Fin f → biformParitySpace K h m d 1}
    {G G' : Fin u → biformParitySpace K h m d 1} {C : ℝ}
    (hQ : Q=Q') (hF : F=F') (hG : G=G') :
    OddEndpointThin Q F G C ↔ OddEndpointThin Q' F' G' C := by
  subst Q'
  subst F'
  subst G'
  rfl

end Froberg
