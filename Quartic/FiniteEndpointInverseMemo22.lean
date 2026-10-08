import Quartic.FiniteEndpointInverse22
import Quartic.FiniteEndpointCheckerMemo

/-! Shared checked lookup equalities for the packed inverse. -/
namespace Quartic.FiniteEndpointRows22
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 32000000
certify_inverse_lookups certificate from "certificates/finite/n22/inverse.bin" inverse_fn Quartic.FiniteEndpointInverse22.binaryInverse nrows 12650 nwords 198
end Quartic.FiniteEndpointRows22
