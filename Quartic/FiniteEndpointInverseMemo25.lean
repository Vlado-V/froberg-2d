import Quartic.FiniteEndpointInverse25
import Quartic.FiniteEndpointCheckerMemo

/-! Shared checked lookup equalities for the packed inverse. -/
namespace Quartic.FiniteEndpointRows25
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 32000000
certify_inverse_lookups certificate from "certificates/finite/n25/inverse.bin" inverse_fn Quartic.FiniteEndpointInverse25.binaryInverse nrows 20475 nwords 320
end Quartic.FiniteEndpointRows25
