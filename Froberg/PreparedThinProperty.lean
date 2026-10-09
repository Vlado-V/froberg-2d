module

public import Froberg.PreparedScalarFiberProperties
public import Froberg.OddEndpointScalarSlices
public import Froberg.BottomVectorQuotient

@[expose] public section

/-! The thin-slice conclusion attached to the literal prepared family. -/
noncomputable section
set_option maxHeartbeats 400000
namespace Froberg.PreparedTarget
open Froberg Module MvPolynomial PreparedParameters BilinearScalarFamily BilinearCovectorStrata
variable {K : Type} [Field K] [Infinite K] {h m d q f u : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ} {O : ℕ → Submodule K (Poly K h)}

def PreparedEndpointThin (hd : 0 < d) (hdodd : d%2=1)
    (hO : ∀ j∈J,O j≤Forms K h j) (hJ : ∀ j∈J,j≤d) (heven : ∀ j∈J,j%2=0)
    (U : Fin u → Forms K h d) (C : ℝ)
    (p : FullPreparedParameters.FixedPureZeroScalarSpace m d q f u J counts O) : Prop :=
  let Q := Fin.append (preparedBaseBiform hO hJ heven p.2.1)
    (preparedPositiveBiform hO hJ heven p.2.1)
  let F := fun i => preparedOddBiform hd hdodd U p.1 p.2.2 (Sum.inl i)
  let G := fun i => preparedOddBiform hd hdodd U p.1 p.2.2 (Sum.inr i)
  HasClosedKernelSlices (oddEndpointScalarAction Q F G)
    (thinSlices (finrank K (oddTargetSpace
      ((fun i => (blockWeight h m i : ZMod 2)) ∘ finSumFinEquiv.symm)
      (backgroundEnumeratedForms Q F G))) C)

theorem preparedOddBiform_outer_family (hd : 0 < d) (hdodd : d%2=1)
    (U : Fin u → Forms K h d) (P : OuterSpace K (Fin h) m d u)
    (F : OuterSpace K (Fin h) m d f) :
    (fun i => preparedOddBiform hd hdodd U P F (Sum.inl i))=
      fun i => oddBiformEmbedding (by omega : 1 ≤ d) (by decide)
        (bottomTensorFamily (fun j => outerVectorEquiv.symm (F j)) i) := by
  funext i
  rw [preparedOddBiform_outer]
  apply Subtype.ext
  rfl

theorem preparedOddBiform_private_family (hd : 0 < d) (hdodd : d%2=1)
    (U : Fin u → Forms K h d) (P : OuterSpace K (Fin h) m d u)
    (F : OuterSpace K (Fin h) m d f) :
    (fun i => preparedOddBiform hd hdodd U P F (Sum.inr i))=
      fun i => mixedPureOddGenerator (Nat.odd_iff.mpr hdodd) (U i) (sumBiformEquiv.symm (P i)) := by
  funext i
  exact preparedOddBiform_private hd hdodd U P F i

end Froberg.PreparedTarget
