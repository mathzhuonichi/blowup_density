import NSFormalization.Section3.T17.ForceVolume

/-!
# T17 U8 axiom audit

Every declaration of `Section3/T17/ForceVolume.lean` must stay inside Lean's
standard `[propext, Classical.choice, Quot.sound]` footprint.
-/

open NSFormalization.Section3.T17

#print axioms latticeVector_eq
#print axioms latticeVector_coord
#print axioms coordinateVector_coord
#print axioms latticeVector_neg
#print axioms latticeVector_add_single
#print axioms latticeVector_sub_single
#print axioms intCast_unitAddCircle_eq_zero
#print axioms continuous_torusPoint
#print axioms torusPoint_sub_latticeVector
#print axioms mem_periodicSet_self
#print axioms mem_periodicSet_add_coordinateVector
#print axioms indicator_periodicSet_isPeriodicSpatial
#print axioms measure_torusPoint_image_le
#print axioms torusRepr
#print axioms torusPoint_torusRepr_self
#print axioms torusSpaceTimeLift_apply
#print axioms tsupport_torusSpaceTimeLift_subset
#print axioms torusTemporalSupport_subset_Icc
#print axioms torusSpatialSupport_subset_image
#print axioms spatialVolumeConst
#print axioms spatialVolumeConst_nonneg
#print axioms measure_torusSpatialSupport_le
#print axioms measure_torusTemporalSupport_le
#print axioms force_spatial_volume
#print axioms force_time_length
