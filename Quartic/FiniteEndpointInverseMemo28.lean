module

public import Quartic.FiniteEndpointInverse28
public import Quartic.FiniteEndpointCheckerMemo

-- Build order: finish the large profile checks before concurrent certificate row checks.
import Quartic.ProfileCertificate.Data
import Quartic.SharpCertificate.Data

@[expose] public section

/-! Shared checked lookup equalities for the packed inverse. -/
namespace Quartic.FiniteEndpointRows28
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 32000000
certify_inverse_lookups certificate from "certificates/finite/n28/inverse.bin" inverse_fn Quartic.FiniteEndpointInverse28.binaryInverse nrows 31465 nwords 492
end Quartic.FiniteEndpointRows28
