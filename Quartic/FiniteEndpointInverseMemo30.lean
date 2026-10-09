module

public import Quartic.FiniteEndpointInverse30
public import Quartic.FiniteEndpointCheckerMemo

-- Build order: finish the large profile checks before concurrent certificate row checks.
import Quartic.ProfileCertificate.Data
import Quartic.SharpCertificate.Data

@[expose] public section

/-! Every packed inverse lookup is identified with a shared literal by a checked equality. -/
namespace Quartic.FiniteEndpointRows30
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 32000000
certify_inverse_lookups certificate from "certificates/finite/n30/inverse.bin" inverse_fn Quartic.FiniteEndpointInverse30.binaryInverse nrows 40920 nwords 640
end Quartic.FiniteEndpointRows30
