import Quartic.FiniteEndpointInverse19
import Quartic.FiniteEndpointCheckerMemo

/-! Shared checked lookup equalities for the packed inverse. -/
namespace Quartic.FiniteEndpointRows19
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 32000000
certify_inverse_lookups certificate from "certificates/finite/n19/inverse.bin" inverse_fn Quartic.FiniteEndpointInverse19.binaryInverse nrows 7315 nwords 115
end Quartic.FiniteEndpointRows19
