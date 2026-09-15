import Bindings.HomogeneousPartialV2
open BlowupDensity
-- V2 binding is a closed value of the API (no hypotheses), exactly as V1's:
#check @BlowupDensity.Bindings.homogeneousPartialV2
#check @BlowupDensity.Bindings.homogeneousPartial
#check @BlowupDensity.Bindings.homogeneousPartial_of_v2
-- the V2 API extends V1: the inherited projection field exists and has V1's type
#check @Contracts.V2.HomogeneousPartial.HomogeneousApproxPartialV2API.toHomogeneousApproxPartialAPI
