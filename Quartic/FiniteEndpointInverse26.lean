import Quartic.FiniteEndpointCheckerLoad

/-! Packed inverse data; rank assertions are separately kernel checked. -/
noncomputable section
namespace Quartic.FiniteEndpointInverse26
set_option Elab.async false
set_option maxRecDepth 1000000
load_packed_tree inverseData from "certificates/finite/n26/inverse.bin" nrows 23751 nwords 372
def binaryInverse (i : Nat) : Nat := inverseData.get i
end Quartic.FiniteEndpointInverse26
