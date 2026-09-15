import NSFormalization.Section4.A01.ForcedSourceUpgrade

open NSFormalization.Section4.A01.ForcedSourceUpgrade

#print axioms truncate_leray
#print axioms sourceTime
#print axioms sourceTime_ae
#print axioms sourceTime_restriction
#print axioms sourceTime_integrable_sq
#print axioms truncate_forcePath
#print axioms exists_local_source_of_memForce

-- The actual local-existence consumer is polymorphic in every q >= 6.
-- This elaborates its minimal admissible order, preserving its complete output.
#check exists_local_source_of_memForce (q := 6) (by omega)
