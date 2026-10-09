module

public import Froberg.PreparedBasicCore

@[expose] public section

/-! Finite certificate data, independent of the legacy eventual construction. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace Froberg.PreparedTarget
open Froberg PreparedParameters Filter Module MvPolynomial
open scoped Topology
variable {K : Type} [Field K] [Infinite K]

def PreparedFramePairOpen {d h u : ℕ} (hd : 3≤d) (n f e : ℕ)
    (U : Fin u → Forms K h d)
    (frame : Fin (quadraticOutputDimension d h) → Forms K h 2) : Prop :=
  HasBasicOpen (m := n) (q := upperCount n d) (f := f)
    (counts := allEvenCount d h n e) (by omega : 0<d)
    (fun j _ => targetLayerOutput_homogeneous frame j)
    (fun j hj => (mem_allEvenIndices.mp hj).2.1) U ∧
  HasBasicOpen (m := n) (q := upperCount n d) (f := f)
    (counts := allEvenCount d h n (e+1)) (by omega : 0<d)
    (fun j _ => targetLayerOutput_homogeneous frame j)
    (fun j hj => (mem_allEvenIndices.mp hj).2.1) U


end Froberg.PreparedTarget
