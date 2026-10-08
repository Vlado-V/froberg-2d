import Quartic.FiniteEndpointInverse26
import Quartic.FiniteEndpointCheckerMemo

/-! Shared checked lookup equalities for the packed inverse. -/
namespace Quartic.FiniteEndpointRows26
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 32000000
certify_inverse_lookups certificate from "certificates/finite/n26/inverse.bin" inverse_fn Quartic.FiniteEndpointInverse26.binaryInverse nrows 23751 nwords 372
end Quartic.FiniteEndpointRows26
