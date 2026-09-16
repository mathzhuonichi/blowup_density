import Bindings.ScalingHomogeneous

-- Every named declaration introduced by lane 250.
#print axioms NSFormalization.Section4.I03.homogeneous_integral_concentrated
#print axioms NSFormalization.Section4.I03.homogeneous_norm_concentrated
#print axioms NSFormalization.Section4.I03.homogeneous_time_scaling
#print axioms NSFormalization.Section4.I03.homogeneous_time_scaling_epsilon
#print axioms NSFormalization.Section4.I03.homogeneous_profile_finite
#print axioms NSFormalization.Section4.I03.homogeneous_norm_smul
#print axioms NSFormalization.Section4.I03.correction_scalar_homogeneous
#print axioms NSFormalization.Section4.I03.componentTimeNorm
#print axioms NSFormalization.Section4.I03.componentTimeNorm_packet
#print axioms NSFormalization.Section4.I03.componentTimeNorm_finite
#print axioms NSFormalization.Section4.I03.correction_componentTimeNorm
#print axioms NSFormalization.Section4.I03.angular_homogeneous_integral
#print axioms NSFormalization.Section4.I03.norm_homogeneousDatum_cycles
#print axioms NSFormalization.Section4.I03.homogeneous_vector_datum_scaling
#print axioms NSFormalization.Section4.I03.compactHomogeneousPath_norm_le
#print axioms NSFormalization.Section4.I03.compactHomogeneousPath_slice
#print axioms NSFormalization.Section4.I03.compactHomogeneousPath_norm_stronglyMeasurable
#print axioms NSFormalization.Section4.I03.homogeneous_datum_time_scaling
#print axioms NSFormalization.Section4.I03.homogeneous_datum_positive_eq_volume
#print axioms NSFormalization.Section4.I03.CompactHomogeneousRealization
#print axioms NSFormalization.Section4.I03.forceHomogeneousENorm_le_components
#print axioms NSFormalization.Section4.I03.forceHomogeneousENorm_eq_path
#print axioms NSFormalization.Section4.I03.forceHomogeneousENorm_scaling
#print axioms NSFormalization.Section4.I03.packetHomogeneousIdentity
#print axioms NSFormalization.Section4.I03.packetHomogeneousConst
#print axioms NSFormalization.Section4.I03.homogeneous_bound_of_components
#print axioms NSFormalization.Section4.I03.packetNegativeHomogeneous
#print axioms NSFormalization.Section4.I03.forceHomogeneousENorm_finite
#print axioms NSFormalization.Section4.I03.packetNegativeHomogeneous_profile
#print axioms NSFormalization.Section4.I03.correction_components
#print axioms NSFormalization.Section4.I03.correctionNegativeHomogeneous
#print axioms NSFormalization.Section4.I03.exists_correction_homogeneous_const
#print axioms NSFormalization.Section4.I03.homogeneousScaling
#print axioms NSFormalization.Section4.I03.zero_homogeneous_path
#print axioms NSFormalization.Section4.I03.forceHomogeneousENorm_zero
#print axioms NSFormalization.Section4.I03.compact_realization_zero

open BlowupDensity.Contracts.V1
open NSFormalization.Section4.I03
open scoped ENNReal

example (q : ℝ≥0∞) (s : ℝ) : Data.forceHomogeneousENorm q s (0 : VelocityField) = 0 :=
  forceHomogeneousENorm_zero q s

-- The actual packet, not a surrogate zero profile, has the explicit slice path.
example {ν : ℝ} (P : PacketAPI ν) :
    Data.IsHomogeneousPath (-1) P.force
      (NSFormalization.Section4.D01.Homogeneous.compactHomogeneousPath
        (by norm_num) P.force_smooth P.force_support.1) :=
  NSFormalization.Section4.D01.Homogeneous.isHomogeneousPath_compact
    (by norm_num) P.force_smooth P.force_support.1
