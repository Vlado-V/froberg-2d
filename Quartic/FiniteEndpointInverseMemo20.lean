import Quartic.FiniteEndpointInverse20
import Quartic.FiniteEndpointCheckerMemo

/-! Shared checked lookup equalities for the packed inverse. -/
namespace Quartic.FiniteEndpointRows20
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 32000000
certify_inverse_lookups certificate from "certificates/finite/n20/inverse.bin" inverse_fn Quartic.FiniteEndpointInverse20.binaryInverse nrows 8855 nwords 139
end Quartic.FiniteEndpointRows20
