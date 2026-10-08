import Quartic.FiniteEndpointInverse21
import Quartic.FiniteEndpointCheckerMemo

/-! Shared checked lookup equalities for the packed inverse. -/
namespace Quartic.FiniteEndpointRows21
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 32000000
certify_inverse_lookups certificate from "certificates/finite/n21/inverse.bin" inverse_fn Quartic.FiniteEndpointInverse21.binaryInverse nrows 10626 nwords 167
end Quartic.FiniteEndpointRows21
