module

public import Quartic.FiniteEndpointMetadata29Data
public import Quartic.FiniteEndpointShapeMemo

@[expose] public section

namespace Quartic.FiniteEndpointRows29
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 32000000

certify_product_lookups certificate from "certificates/finite/n29"
  product_fn Quartic.FiniteEndpointMetadata29Data.naturalProduct
  start_index 141918 lookup_count 23653

end Quartic.FiniteEndpointRows29
