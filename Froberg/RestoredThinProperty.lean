import Froberg.RestoredScalarCompatibility
import Froberg.OddEndpointScalarSlices
import Froberg.BottomVectorQuotient

/-! The thin-slice property of the literal restored endpoint family. -/
noncomputable section
set_option maxHeartbeats 200000
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial VectorMultiplicationCoordinates BilinearScalarFamily BilinearCovectorStrata
variable {K : Type} [Field K] [Infinite K] {h m d q f r : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ} {O : ℕ → Submodule K (Poly K h)}

def RestoredEndpointThin (hdp : 1 ≤ d) (hd : d%2=0)
    (hO : ∀ j ∈ J, O j ≤ Forms K h j) (hJ : ∀ j ∈ J, j ≤ d)
    (heven : ∀ j ∈ J, j%2=0) (idx : Fin r ≃ Label q J counts)
    (slot : Fin (finrank K (Forms K h d)) → Fin r) (C : ℝ)
    (p : RestoredOuterSpace m d q f J counts O) : Prop :=
  let Q := Fin.append (restoredBaseBiform hd hO hJ heven idx slot p.1)
    (restoredPositiveBiform hd hO hJ heven idx slot p.1)
  let F := fun i => linearOddForm hdp (PreparedTarget.outerVectorEquiv.symm (p.2 i))
  HasClosedKernelSlices (oddEndpointScalarAction Q F emptyOddFamily)
    (thinSlices (finrank K (oddTargetSpace
      ((fun i => (blockWeight h m i : ZMod 2)) ∘ finSumFinEquiv.symm)
      (backgroundEnumeratedForms Q F emptyOddFamily))) C)

theorem linearOddForm_family_eq_embedding (hdp : 1 ≤ d)
    (g : Fin f → Rows K h m (d-1)) :
    (fun i => linearOddForm hdp (g i))=
      fun i => oddBiformEmbedding hdp (by decide) (bottomTensorFamily g i) := by
  funext i
  apply Subtype.ext
  rfl

end Froberg.PreparedParameters
