import Quartic.FiniteEndpointInverse18
import Quartic.FiniteEndpointCheckerMemo

/-! Shared checked lookup equalities for the packed inverse. -/
namespace Quartic.FiniteEndpointRows18
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 32000000
certify_inverse_lookups certificate from "certificates/finite/n18/inverse.bin" inverse_fn Quartic.FiniteEndpointInverse18.binaryInverse nrows 5985 nwords 94
end Quartic.FiniteEndpointRows18
