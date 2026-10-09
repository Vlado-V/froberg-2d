module

public import Froberg.CountedRestoredFullOpen
public import Froberg.ActualRestoredSlots

@[expose] public section

/-! Finite certificate data, independent of the legacy eventual construction. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace Froberg.PreparedParameters
open Froberg PreparedTarget Filter Module MvPolynomial
open scoped Topology
variable {K : Type} [Field K] [Infinite K]

def RestoredFramePairOpen {d h : ℕ} (hd : 3≤d) (he : d%2=0) (n f e : ℕ)
    (frame : Fin (quadraticOutputDimension d h) → Forms K h 2) : Prop :=
  HasRestoredCertificateOpen (m := n) (f := f) (by omega : 1≤d) he
    (fun j (_ : j∈allEvenIndices d) => targetLayerOutput_homogeneous frame j)
    (fun j hj => (mem_allEvenIndices.mp hj).2.1)
    (fun j hj => (mem_allEvenIndices.mp hj).2.2)
    (actualRestoredIndex K d h n e 0) (actualRestoredBaseSlot hd) ∧
  HasRestoredCertificateOpen (m := n) (f := f) (by omega : 1≤d) he
    (fun j (_ : j∈allEvenIndices d) => targetLayerOutput_homogeneous frame j)
    (fun j hj => (mem_allEvenIndices.mp hj).2.1)
    (fun j hj => (mem_allEvenIndices.mp hj).2.2)
    (actualRestoredIndex K d h n e 1) (actualRestoredEnlargedSlot hd)

end Froberg.PreparedParameters
