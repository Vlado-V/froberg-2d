module

public import Quartic.FiniteEndpointCheckerLoad

@[expose] public section

/-! Packed inverse data for the supplied thirty-variable endpoint certificate.
This module only reifies natural-number literals; equations are checked separately. -/
noncomputable section
namespace Quartic.FiniteEndpointInverse30
set_option Elab.async false
set_option maxRecDepth 1000000
load_packed_tree inverseData from "certificates/finite/n30/inverse.bin" nrows 40920 nwords 640

def binaryInverse (i : Nat) : Nat := inverseData.get i
end Quartic.FiniteEndpointInverse30
