import Quartic.FiniteEndpointInverse17
import Quartic.FiniteEndpointCheckerMemo

/-! Shared checked lookup equalities for the packed inverse. -/
namespace Quartic.FiniteEndpointRows17
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 32000000
certify_inverse_lookups certificate from "certificates/finite/n17/inverse.bin" inverse_fn Quartic.FiniteEndpointInverse17.binaryInverse nrows 4845 nwords 76
end Quartic.FiniteEndpointRows17
