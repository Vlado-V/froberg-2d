module

public import Quartic.FiniteEndpointMetadata28Data
public import Quartic.FiniteEndpointShapeMemo

@[expose] public section

namespace Quartic.FiniteEndpointRows28
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 32000000

certify_product_lookups certificate from "certificates/finite/n28"
  product_fn Quartic.FiniteEndpointMetadata28Data.naturalProduct
  start_index 144231 lookup_count 20605

end Quartic.FiniteEndpointRows28
