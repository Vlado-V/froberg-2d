module

public import Froberg.ActualPreparedComparison

@[expose] public section

/-! Finite certificate data, independent of the legacy eventual construction. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace Froberg.PreparedTarget
open Froberg PreparedParameters FullPreparedParameters Filter Module MvPolynomial
open scoped Topology
variable {K : Type} [Field K] [Infinite K]

structure PreparedFrameReady {d h u : ℕ} (hd : 3≤d) (ho : d%2=1) (n f e : ℕ)
    (U : Fin u → Forms K h d)
    (frame : Fin (quadraticOutputDimension d h) → Forms K h 2) : Prop where
  independent : LinearIndependent K frame
  base : HasBasicOpen (m := n) (q := upperCount n d) (f := f)
    (counts := allEvenCount d h n e) (by omega : 0<d)
    (fun j (_ : j∈allEvenIndices d) => targetLayerOutput_homogeneous frame j)
    (fun j hj => (mem_allEvenIndices.mp hj).2.1) U
  enlarged : HasEnlargedPreparedOpen (m := n) (q := upperCount n d) (f := f)
    (counts := allEvenCount d h n (e+1)) (by omega : 0<d) ho
    (fun j (_ : j∈allEvenIndices d) => targetLayerOutput_homogeneous frame j)
    (fun j hj => (mem_allEvenIndices.mp hj).2.1)
    (fun j hj => (mem_allEvenIndices.mp hj).2.2) (Fintype.equivFin _).symm U


end Froberg.PreparedTarget
