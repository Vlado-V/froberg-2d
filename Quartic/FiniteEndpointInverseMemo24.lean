import Quartic.FiniteEndpointInverse24
import Quartic.FiniteEndpointCheckerMemo

/-! Shared checked lookup equalities for the packed inverse. -/
namespace Quartic.FiniteEndpointRows24
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 32000000
certify_inverse_lookups certificate from "certificates/finite/n24/inverse.bin" inverse_fn Quartic.FiniteEndpointInverse24.binaryInverse nrows 17550 nwords 275
end Quartic.FiniteEndpointRows24
