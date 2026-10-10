module

public import Quartic.FiniteEndpointMetadata30Data
public import Quartic.FiniteEndpointShapeMemo

@[expose] public section

namespace Quartic.FiniteEndpointRows30
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 32000000

certify_product_lookups certificate from "certificates/finite/n30"
  product_fn Quartic.FiniteEndpointMetadata30Data.naturalProduct
  start_index 189196 lookup_count 27029

end Quartic.FiniteEndpointRows30
