import Quartic.FiniteEndpointInverse23
import Quartic.FiniteEndpointCheckerMemo

/-! Shared checked lookup equalities for the packed inverse. -/
namespace Quartic.FiniteEndpointRows23
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 32000000
certify_inverse_lookups certificate from "certificates/finite/n23/inverse.bin" inverse_fn Quartic.FiniteEndpointInverse23.binaryInverse nrows 14950 nwords 234
end Quartic.FiniteEndpointRows23
