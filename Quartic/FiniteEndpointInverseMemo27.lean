import Quartic.FiniteEndpointInverse27
import Quartic.FiniteEndpointCheckerMemo

/-! Shared checked lookup equalities for the packed inverse. -/
namespace Quartic.FiniteEndpointRows27
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 32000000
certify_inverse_lookups certificate from "certificates/finite/n27/inverse.bin" inverse_fn Quartic.FiniteEndpointInverse27.binaryInverse nrows 27405 nwords 429
end Quartic.FiniteEndpointRows27
