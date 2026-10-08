import Froberg.RestoredThinProperty
import Froberg.EndpointThinProperty
import Froberg.ActualEndpointReplacement

/-! The thinness produced by restored scalar selection is the literal
background thinness required by the concrete comparison theorem. -/
noncomputable section
set_option maxHeartbeats 200000
namespace Froberg.PreparedParameters
open Froberg Module MvPolynomial BilinearScalarFamily BilinearCovectorStrata
variable {K : Type} [Field K] [Infinite K] {h m d q f r : ℕ}
variable {J : Finset ℕ} {counts : ℕ → ℕ} {O : ℕ → Submodule K (Poly K h)}

theorem restored_endpoint_thin_background (hdp : 1 ≤ d) (hd : d%2=0)
    (hO : ∀ j ∈ J, O j ≤ Forms K h j) (hJ : ∀ j ∈ J, j ≤ d)
    (heven : ∀ j ∈ J, j%2=0) (idx : Fin r ≃ Label q J counts)
    (slot : Fin (finrank K (Forms K h d)) → Fin r)
    (hslot : ∀ k, 0 < degree (idx (slot k))) (C : ℝ)
    (p : RestoredOuterSpace m d q f J counts O)
    (hthin : RestoredEndpointThin hdp hd hO hJ heven idx slot C p) :
    HasClosedKernelSlices (oddEndpointScalarAction
      (Fin.append (fun i => scalarEvenBiform (h := h) (p.1.1.1 (Sum.inl i)))
        (restoredPositiveBiform hd hO hJ heven idx slot p.1))
      (fun i => linearOddForm hdp (PreparedTarget.outerVectorEquiv.symm (p.2 i))) emptyOddFamily)
      (thinSlices (backgroundOddTargetDimension
        (Fin.append (fun i => scalarEvenBiform (h := h) (p.1.1.1 (Sum.inl i)))
          (restoredPositiveBiform hd hO hJ heven idx slot p.1))
        (fun i => linearOddForm hdp (PreparedTarget.outerVectorEquiv.symm (p.2 i))) emptyOddFamily) C) := by
  change OddEndpointThin
    (Fin.append (restoredBaseBiform hd hO hJ heven idx slot p.1)
      (restoredPositiveBiform hd hO hJ heven idx slot p.1))
    (fun i => linearOddForm hdp (PreparedTarget.outerVectorEquiv.symm (p.2 i))) emptyOddFamily C at hthin
  rw [restoredBaseBiform_eq_scalar hd hO hJ heven idx slot hslot p.1] at hthin
  exact hthin

end Froberg.PreparedParameters
