import Formal.NavierStokesTimeBridge
import Formal.R3CoordinateIncompressibility
import Formal.R3ClassicalIncompressibility
import Formal.R3DecoderFrequencyBridge
import Formal.R3InversionConsistency
import Formal.R3HelmholtzPressure
import Formal.FlowMapNonextendibilityCriterion
import Formal.UniformRestartContinuation
import Formal.TerminalFlowMapAmplification
import Formal.TerminalFlowMapOperatorNorm
import Formal.MildSolutionSemantics
import Formal.MildFlowMapBridge
import Formal.MildZeroUniqueness
import Formal.QuadraticMildNonlinearity
import Formal.QuadraticLinearizedMild
import Formal.QuadraticMildTangentAdapter
import Formal.QuadraticMildFixedPointDerivative
import Formal.QuadraticMildTangentRealization
import Formal.QuadraticMildCoherentFamilyAdapter
import Formal.LerayProjectedQuadratic
import Formal.R3LerayFrequencySymbol
import Formal.R3StokesFrequencySymbol
import Formal.R3StokesL2Operator
import Formal.R3LerayL2Operator
import Formal.R3LerayFourierBridge
import Formal.R3LerayComplexFiberSymbol
import Formal.R3SobolevCarrier
import Formal.R3SchwartzConvectionSobolevEstimate
import Formal.R3SobolevConvectionExtension
import Formal.R3ProjectedSobolevConvection
import Formal.R3StokesH2H3Smoothing
import Formal.EndpointSafeTwoSpaceDuhamel
import Formal.R3StokesH3Evolution
import Formal.R3EndpointSafeProjectedDuhamel
import Formal.EndpointSafeTwoSpacePicard
import Formal.R3EndpointSafeProjectedLocalExistence
import Formal.R3ConjugationReflection
import Formal.R3FourierConjugationBridge
import Formal.R3StokesConjugationEquivariance
import Formal.R3LerayConjugationEquivariance
import Formal.R3ConvectionConjugationEquivariance
import Formal.R3RealLocalMildSolution
import Formal.R3QuantitativeLifespan
import Formal.EndpointSafeTwoSpaceRestart
import Formal.EndpointSafeTwoSpaceUniqueness
import Formal.EndpointSafeTwoSpaceConcatenation
import Formal.R3ConvectionSourceIdentification
import Formal.R3ProjectedMomentumDuhamelInfrastructure
import Formal.R3ProjectedMomentumEquation
import Formal.R3NavierStokesEquation
import Formal.R3FiniteEnergy
import Formal.R3MildContinuation
import Formal.R3DecodedVelocityRealness
import Formal.R3SchwartzDivergence
import Formal.R3SchwartzInitialData
import Formal.ReducedBridgeResidual
import Formal.FiniteRankReducedBridge
import Formal.GronwallIntegralInequality
import Formal.R3TSelDecodedGradient
import Formal.R3TSelBridge
import Formal.R3TSelClassicalComparability
import Formal.R3TSelSchwartzCalculus
import Formal.R3TSelLeibnizCommutator

/-
CI-visible axiom audit for the strongest currently formalized bridge theorems.

These commands do not add assumptions. They print the axiom dependencies of the declarations
into the Lean build log so that unexpected dependencies are visible during review.
-/
#print axioms MNS2.affine_flowmap_bridge_of_contDiffOn_open
#print axioms MNS2.radial_flowmap_bridge_of_contDiffOn_open
#print axioms MNS2.FixedTimePDEBridgeAdapter.affine_bridge
#print axioms MNS2.FixedTimePDEBridgeAdapter.radial_bridge
#print axioms MNS2.FixedTimePDEBridgeAdapter.radial_bridge_of_zero_fixed
#print axioms MNS2.NavierStokesTimeBridgeAdapter.affine_bridge_at_time
#print axioms MNS2.NavierStokesTimeBridgeAdapter.radial_bridge_at_time
#print axioms MNS2.NavierStokesTimeBridgeAdapter.radial_bridge_at_time_of_zero_fixed
#print axioms MNS2.FlowMapContinuationPackage.endpoint_norm_le_of_radial_directional_bound
#print axioms MNS2.FlowMapContinuationPackage.directional_fderiv_unbounded_of_nonextendible
#print axioms MNS2.FlowMapUniformRestartPackage.continuation_of_uniform_endpoint_bound
#print axioms MNS2.FlowMapUniformRestartPackage.directional_fderiv_unbounded_of_nonextendible
#print axioms MNS2.FlowMapUniformRestartPackage.terminal_directional_fderiv_unbounded_of_nonextendible
#print axioms MNS2.FlowMapUniformRestartPackage.eventually_arbitrarily_large_directional_fderiv
#print axioms MNS2.FlowMapUniformRestartPackage.terminal_fderiv_opNorm_unbounded_of_nonextendible
#print axioms MNS2.FlowMapUniformRestartPackage.exists_terminal_fderiv_opNorm_above
#print axioms MNS2.MildEvolutionKernel.evolvesAt_nonnegative
#print axioms MNS2.MildEvolutionKernel.evolvesAt_zero_eq_initial
#print axioms MNS2.MildEvolutionKernel.evolvesAt_endpoint_equation
#print axioms MNS2.NavierStokesTimeBridgeAdapter.mild_endpoint_equation
#print axioms MNS2.NavierStokesTimeBridgeAdapter.radial_path_has_mild_witness
#print axioms MNS2.NavierStokesTimeBridgeAdapter.radial_bridge_eq_mild_duhamel
#print axioms MNS2.MildEvolutionKernel.trajectoryUniqueOn_endpointUniqueAt
#print axioms MNS2.MildEvolutionKernel.zero_isMildSolutionOn
#print axioms MNS2.MildEvolutionKernel.zero_evolvesAt_zero
#print axioms MNS2.NavierStokesTimeBridgeAdapter.stateMap_zero_of_mild_endpointUnique
#print axioms MNS2.NavierStokesTimeBridgeAdapter.stateMap_zero_of_mild_trajectoryUnique
#print axioms MNS2.NavierStokesTimeBridgeAdapter.radial_bridge_eq_mild_duhamel_of_endpointUnique
#print axioms MNS2.hasFDerivAt_quadraticDiagonal
#print axioms MNS2.fderiv_quadraticDiagonal
#print axioms MNS2.MildEvolutionKernel.ofQuadratic_zero_evolvesAt_zero
#print axioms MNS2.quadraticLinearizedMild_equation_at_time_expanded
#print axioms MNS2.quadraticMildTangentEvolvesAt_nonnegative
#print axioms MNS2.quadraticMildTangentEvolvesAt_zero_eq_initial
#print axioms MNS2.quadraticMildTangent_zero_evolvesAt_zero
#print axioms MNS2.QuadraticMildC1TangentAdapter.fderiv_realizes_linearized_mild
#print axioms MNS2.QuadraticMildC1TangentAdapter.radial_bridge_with_linearized_mild_semantics
#print axioms MNS2.QuadraticMildC1TangentAdapter.radial_endpoint_bridge_with_linearized_mild_semantics
#print axioms MNS2.quadraticMild_fixedPoint_fderiv_eq_of_dominated
#print axioms MNS2.quadraticMild_fixedPoint_fderiv_apply_eq_of_dominated
#print axioms MNS2.quadraticMild_fixedPoint_fderiv_eq_of_dominated_on_nhds
#print axioms MNS2.quadraticMild_fixedPoint_fderiv_apply_eq_of_dominated_on_nhds
#print axioms MNS2.quadraticMildRHSDerivativeAtTime_apply_eq_linearized
#print axioms MNS2.quadraticMild_fixedPoint_direction_equation_of_certificate
#print axioms MNS2.quadraticMild_fixedPoint_direction_equation_of_local_certificate
#print axioms MNS2.quadraticMildTangentEvolvesAt_of_dominated_fixedPoint_family
#print axioms MNS2.quadraticMildTangentEvolvesAt_of_local_fixedPoint_family
#print axioms MNS2.QuadraticMildC1CoherentFamilyAdapter.fderiv_realizes_linearized_mild
#print axioms MNS2.QuadraticMildC1CoherentFamilyAdapter.radial_bridge_with_derived_tangent_semantics
#print axioms MNS2.LerayProjectedQuadraticContract.leray_idempotent_apply
#print axioms MNS2.LerayProjectedQuadraticContract.projectedConvection_mem
#print axioms MNS2.LerayProjectedQuadraticContract.quadraticDerivative_mem
#print axioms MNS2.LerayProjectedQuadraticContract.fderiv_mildKernel_nonlinearity_mem
#print axioms MNS2.mem_r3SolenoidalFiber_iff_inner
#print axioms MNS2.r3LeraySymbol_mem
#print axioms MNS2.inner_r3LeraySymbol_eq_zero
#print axioms MNS2.r3LeraySymbol_idempotent
#print axioms MNS2.norm_r3LeraySymbol_le
#print axioms MNS2.r3LeraySymbol_zero
#print axioms MNS2.r3LeraySymbol_self
#print axioms MNS2.r3LeraySymbol_apply
#print axioms MNS2.r3StokesDecayRate_nonneg
#print axioms MNS2.r3StokesScalar_le_one
#print axioms MNS2.r3StokesFrequencySymbol_zero_time
#print axioms MNS2.r3StokesFrequencySymbol_add_time
#print axioms MNS2.r3StokesFrequencySymbol_mem
#print axioms MNS2.r3StokesFrequencySymbol_commutes_leray
#print axioms MNS2.norm_r3StokesFrequencySymbol_le
#print axioms MNS2.r3StokesLerayFrequencySymbol_mem
#print axioms MNS2.continuous_r3StokesScalarComplex
#print axioms MNS2.norm_r3StokesScalarComplex_le_one
#print axioms MNS2.r3StokesL2FrequencyMultiplier_ae
#print axioms MNS2.fourier_r3StokesL2Operator
#print axioms MNS2.r3StokesL2FrequencyMultiplier_zero_time
#print axioms MNS2.r3StokesL2Operator_zero_time
#print axioms MNS2.r3LerayL2Operator_mem_solenoidal
#print axioms MNS2.r3NormalizedDivergenceL2OperatorAux_r3LerayL2Operator
#print axioms MNS2.r3LerayL2Operator_fixed_of_mem
#print axioms MNS2.r3LerayL2Operator_idempotent
#print axioms MNS2.norm_r3LerayL2Operator_apply_le
#print axioms MNS2.norm_r3LerayL2Operator_le_one
#print axioms MNS2.fourier_mem_r3L2FrequencySolenoidalSubmodule_iff
#print axioms MNS2.map_r3L2SolenoidalSubmodule_fourier
#print axioms MNS2.r3LerayL2FrequencyOperator_mem_solenoidal
#print axioms MNS2.fourier_r3LerayL2Operator
#print axioms MNS2.mem_r3ComplexSolenoidalFiber_iff_inner
#print axioms MNS2.r3LeraySymbolComplex_mem
#print axioms MNS2.inner_r3LeraySymbolComplex_eq_zero
#print axioms MNS2.r3LeraySymbolComplex_fixed_of_mem
#print axioms MNS2.r3LeraySymbolComplex_idempotent
#print axioms MNS2.norm_r3LeraySymbolComplex_le
#print axioms MNS2.r3LeraySymbolComplex_zero
#print axioms MNS2.r3LeraySymbolComplex_self
#print axioms MNS2.r3LeraySymbolComplex_apply
#print axioms MNS2.besselPotential_r3HsToTempered_eq_coordinate
#print axioms MNS2.r3HsToTempered_memSobolev
#print axioms MNS2.r3HmToTempered_memSobolev
#print axioms MNS2.r3StrongSobolevOrder_three
#print axioms MNS2.r3SchwartzConvectionTermSobolevEstimate_three
#print axioms MNS2.r3SchwartzConvectionSobolevEstimate_three
#print axioms MNS2.r3SchwartzToHsCLM_denseRange
#print axioms MNS2.r3ConvectionH3ToH2_apply_schwartz
#print axioms MNS2.r3HsToTempered_r3ConvectionH3ToH2_schwartz
#print axioms MNS2.norm_r3ConvectionH3ToH2_apply_le
#print axioms MNS2.r3ConvectionH3ToH2_unique
#print axioms MNS2.r3L2ToTempered_r3H2ToL2Operator
#print axioms MNS2.r3H2ToL2Operator_commutes_leray
#print axioms MNS2.r3HsToTempered_r3LerayH2Operator
#print axioms MNS2.norm_r3ProjectedConvectionH3ToH2_le
#print axioms MNS2.norm_r3ProjectedConvectionH3ToH2_apply_le
#print axioms MNS2.r3H2ToL2Operator_r3ProjectedConvectionH3ToH2_mem_solenoidal
#print axioms MNS2.r3HsToTempered_r3ProjectedConvectionH3ToH2
#print axioms MNS2.r3HsToTempered_r3ProjectedConvectionH3ToH2_schwartz
#print axioms MNS2.norm_r3StokesH2ToH3Operator_le
#print axioms MNS2.intervalIntegrable_r3StokesH2H3TimeKernel
#print axioms MNS2.r3L2ToTempered_r3H3ToL2Operator
#print axioms MNS2.r3H3ToL2Operator_r3StokesH2ToH3Operator
#print axioms MNS2.r3HsToTempered_r3StokesH2ToH3Operator
#print axioms MNS2.r3HsToTempered_r3LerayH3Operator
#print axioms MNS2.r3StokesH2ToH3Operator_commutes_leray
#print axioms MNS2.r3StokesH2ToH3Operator_mem_solenoidal
#print axioms MNS2.r3StokesL2Operator_r3H2ToL2Operator_mem_solenoidal
#print axioms MNS2.EndpointSafeTwoSpaceDuhamelContract.intervalIntegrable_duhamelIntegrand_of_continuousOn
#print axioms MNS2.EndpointSafeTwoSpaceDuhamelContract.isMildAt_zero_iff
#print axioms MNS2.r3StokesH3Evolution_add
#print axioms MNS2.continuous_r3StokesH3Evolution_action
#print axioms MNS2.r3H3ToL2Operator_r3StokesH3Evolution
#print axioms MNS2.r3StokesH2ToH3Operator_add_nnreal
#print axioms MNS2.aestronglyMeasurable_r3EndpointSafeProjectedDuhamelIntegrand
#print axioms MNS2.intervalIntegrable_r3EndpointSafeProjectedDuhamelIntegrand
#print axioms MNS2.norm_integral_r3EndpointSafeProjectedDuhamelIntegrand_le
#print axioms MNS2.r3EndpointSafeProjectedMild_equation_at_time
#print axioms MNS2.EndpointSafeTwoSpaceDuhamelContract.continuousOn_duhamelIntegral
#print axioms MNS2.EndpointSafeTwoSpaceDuhamelContract.exists_pos_time_isMildSolutionOn
#print axioms MNS2.r3EndpointSafeProjected_exists_localMildSolution
#print axioms MNS2.r3EndpointSafeProjected_localMildSolution_equation
#print axioms MNS2.r3L2Reflect_r3L2Conj
#print axioms MNS2.isR3RealVelocity_iff_im_ae
#print axioms MNS2.isR3ConjugateSymmetricVelocity_iff_reflect_eq_conj
#print axioms MNS2.isClosed_setOf_isR3RealVelocity
#print axioms MNS2.isClosed_setOf_isR3ConjugateSymmetricVelocity
#print axioms MNS2.r3Fourier_conj_eq
#print axioms MNS2.fourier_r3SchwartzConjCLM
#print axioms MNS2.fourier_r3L2Conj
#print axioms MNS2.isR3RealVelocity_iff_fourier_conjugateSymmetric
#print axioms MNS2.r3L2Conj_of_fourier_realEven
#print axioms MNS2.r3L2Conj_r3StokesL2Operator
#print axioms MNS2.r3L2Conj_r3StokesH3Evolution
#print axioms MNS2.r3L2Conj_r3StokesH2ToH3Operator
#print axioms MNS2.r3L2Conj_of_fourier_conjEquivariant_even
#print axioms MNS2.r3CConj_r3LeraySymbolComplex
#print axioms MNS2.r3L2Conj_r3LerayL2Operator
#print axioms MNS2.IsR3RealVelocity.leray
#print axioms MNS2.IsR3RealVelocity.stokesH3
#print axioms MNS2.r3L2Conj_r3LerayH2Operator
#print axioms MNS2.r3L2Conj_r3LerayH3Operator
#print axioms MNS2.r3L2Conj_r3SchwartzToHsCLM
#print axioms MNS2.r3SchwartzConvection_conj
#print axioms MNS2.r3ConjugatedConvectionH3ToH2_eq
#print axioms MNS2.r3L2Conj_r3ConvectionH3ToH2
#print axioms MNS2.r3L2Conj_r3ProjectedConvectionH3ToH2
#print axioms MNS2.IsR3RealVelocity.projectedConvection
#print axioms MNS2.IsR3EndpointSafeProjectedMildSolutionOn.r3L2Conj_comp
#print axioms MNS2.r3EndpointSafeProjected_exists_realLocalMildSolution

-- Explicit quantitative lifespan: given-horizon Picard, closed-form kernel mass
-- `K(T) = T + √T/(π√ν)`, the explicit lifespan `T₀ = (δ/(1+(π√ν)⁻¹+δ))²`, and the
-- quantitative existence theorems on the explicit horizon (complex + real data).
#print axioms MNS2.EndpointSafeTwoSpaceDuhamelContract.exists_isMildSolutionOn_of_kernelPrimitive_lt
#print axioms MNS2.r3MildSmallnessThreshold_pos
#print axioms MNS2.r3MildSmallnessThreshold_le_one
#print axioms MNS2.r3MildLifespan_pos
#print axioms MNS2.r3MildLifespan_le_one
#print axioms MNS2.r3EndpointSafeProjected_kernelPrimitive_eq
#print axioms MNS2.endpointSafe_lifespan_sq_add_lt
#print axioms MNS2.r3EndpointSafeProjected_kernelPrimitive_mildLifespan_lt
#print axioms MNS2.r3EndpointSafeProjected_exists_mildSolutionOn_mildLifespan
#print axioms MNS2.r3EndpointSafeProjected_exists_realMildSolutionOn_mildLifespan

-- Mild restart identity and unrestricted uniqueness: a mild solution restarted at a
-- certified time solves the shifted problem; two mild solutions with the same datum agree
-- on their common horizon (no ball restriction); consequently every mild solution with
-- physically real datum is pointwise physically real.
#print axioms MNS2.EndpointSafeTwoSpaceDuhamelContract.duhamelIntegrand_comp_add_left
#print axioms MNS2.EndpointSafeTwoSpaceDuhamelContract.IsMildSolutionOn.restart
#print axioms MNS2.IsR3EndpointSafeProjectedMildSolutionOn.restart
#print axioms MNS2.EndpointSafeTwoSpaceDuhamelContract.IsMildSolutionOn.mono
#print axioms MNS2.EndpointSafeTwoSpaceDuhamelContract.isMildSolutionOn_eq_of_contraction
#print axioms MNS2.EndpointSafeTwoSpaceDuhamelContract.IsMildSolutionOn.unique
#print axioms MNS2.r3EndpointSafeProjectedMildSolution_unique
#print axioms MNS2.IsR3EndpointSafeProjectedMildSolutionOn.isR3RealVelocity

-- Maximal continuation layer: the concatenation identity (converse of restart), the
-- antitone explicit lifespan, the uniform-step extension of norm-bounded solutions, and
-- the blow-up dichotomy for the certified-horizon set.
#print axioms MNS2.EndpointSafeTwoSpaceDuhamelContract.IsMildSolutionOn.concat
#print axioms MNS2.IsR3EndpointSafeProjectedMildSolutionOn.concat
#print axioms MNS2.r3MildSmallnessThreshold_antitone
#print axioms MNS2.r3MildLifespan_antitone
#print axioms MNS2.r3EndpointSafeProjected_exists_extension_of_bounded
#print axioms MNS2.r3MildHorizons_nonempty
#print axioms MNS2.r3EndpointSafeProjected_horizons_unbounded_of_uniform_bound
#print axioms MNS2.r3EndpointSafeProjected_blowup_dichotomy
#print axioms MNS2.interval_integral_approximation_error_bound
#print axioms MNS2.radial_reduced_bridge_error_bound
#print axioms MNS2.radial_reduced_endpoint_error_bound_of_zero_fixed
#print axioms MNS2.intervalIntegral_finiteRankPath
#print axioms MNS2.radial_finiteRank_bridge_error_bound
#print axioms MNS2.radial_finiteRank_endpoint_error_bound_of_zero_fixed

-- Coordinate incompressibility semantics (Clay semantic-promotion edge 1, distributional
-- half): a Fourier-side solenoidal L² velocity represents a physical tempered distribution
-- whose physical-coordinate divergence (the sum of the distributional coordinate partial
-- derivatives of its components) vanishes; no phantom Sobolev order consumed.
#print axioms MNS2.r3TemperedDivergence_apply
#print axioms MNS2.r3TemperedDivergence_eq_zero_of_mem_solenoidal

-- Coordinate incompressibility semantics, classical half (Clay semantic-promotion edge 1b):
-- the explicit inverse-Fourier-integral physical representative is C^1 under explicit
-- frequency-side L^1 hypotheses, differentiable everywhere with an explicit derivative,
-- and its classical divergence vanishes at every point for solenoidal data; hypotheses
-- witnessed non-vacuous by Schwartz profiles.
#print axioms MNS2.contDiff_one_r3PhysicalRepresentative
#print axioms MNS2.hasFDerivAt_r3PhysicalRepresentative
#print axioms MNS2.r3RepresentativeDeriv_div_eq_zero
#print axioms MNS2.r3ClassicalDivergence_r3PhysicalRepresentative
#print axioms MNS2.r3PhysicalRepresentative_incompressible_of_mem_solenoidal
#print axioms MNS2.r3PhysicalRepresentative_hypotheses_nonvacuous

-- Bessel decoder -> edge-1b frequency hypotheses (Clay semantic edge 3a): the decoded
-- frequency data of an H^3 Bessel coordinate satisfies both explicit L^1 hypotheses of
-- edge 1b (Cauchy-Schwarz against the order-three inverse Bessel weight in dimension
-- three), is a.e. the Fourier transform of the L^2-level physical decode, coordinate
-- solenoidality transfers to the decode, and the capstone discharges every edge-1b
-- hypothesis from the decoder.
#print axioms MNS2.integrable_r3DecodedFrequency
#print axioms MNS2.integrable_weighted_r3DecodedFrequency
#print axioms MNS2.r3DecodedFrequency_ae_coeFn_fourier
#print axioms MNS2.r3Decoded3PhysicalVelocity_mem_solenoidal
#print axioms MNS2.r3DecodedFrequency_incompressible
#print axioms MNS2.r3L2ToTempered_r3Decoded3PhysicalVelocity
#print axioms MNS2.r3DecodedFrequency_incompressible_leray

-- Inversion consistency (Clay semantic edge 3b): the pointwise inverse-Fourier-integral
-- representative of the decoded frequency data agrees a.e. with the L^2-level decode
-- (Schwartz pairing on both sides + a.e. uniqueness against smooth compactly supported
-- test functions; no general L^1-cap-L^2 inversion library).
#print axioms MNS2.integral_smul_r3PhysicalRepresentative
#print axioms MNS2.integral_smul_r3Decoded3PhysicalVelocity
#print axioms MNS2.r3PhysicalRepresentative_ae_r3Decoded3PhysicalVelocity
#print axioms MNS2.r3DecodedFrequency_incompressible_ae_decoder

-- Generic Helmholtz pressure reconstruction (Clay semantic edge 2a): for every L^2
-- source, the explicit pressure tempered distribution (inverse Fourier transform of the
-- low/high split of the divergence-over-|xi|^2 profile) satisfies grad p = -(I-P)F
-- componentwise in Schwartz'; supporting integrability and frequency-realization facts.
#print axioms MNS2.integrable_r3PressureFrequencyLow
#print axioms MNS2.memLp_two_r3PressureFrequencyHigh
#print axioms MNS2.fourier_r3LerayComplementL2_ae
#print axioms MNS2.r3HelmholtzPressure_gradient
#print axioms MNS2.exists_r3LerayComplementL2_ne_zero

-- General H^3 convection source identification (Clay semantic edge 2b-i): the genuine
-- J^-2 decode of the completed coordinate convection operator equals, for all order-three
-- coordinates, the pointwise convection (U.grad)V of the decoded physical representatives
-- built from the explicit derivative; projected corollary P((U.grad)V); quantitative
-- Cauchy-Schwarz decoder L^1 bound; generic L^1-cap-L^2 inversion consistency; and the
-- edge-2a pressure gradient instantiated at the identified convection source.
#print axioms MNS2.integral_norm_r3DecodedFrequency_le
#print axioms MNS2.r3PhysicalRepresentative_ae_fourierInv
#print axioms MNS2.r3DecodedDerivativeL2Operator_ae_deriv
#print axioms MNS2.r3DecodedConvectionL2_schwartz
#print axioms MNS2.r3H2ToL2Operator_r3ConvectionH3ToH2
#print axioms MNS2.r3H2ToL2Operator_r3ProjectedConvectionH3ToH2
#print axioms MNS2.r3HelmholtzPressure_gradient_decodedConvection
#print axioms MNS2.exists_r3DecodedConvectionL2_ne_zero
#print axioms MNS2.exists_r3ConvectionH3ToH2_ne_zero

-- Duhamel differentiation infrastructure towards the projected momentum equation (Clay
-- semantic edge 2b-ii.a, infrastructure pass; the momentum equation itself is proved in
-- the assembly pass audited below, which consumes the commutations,
-- integral_inner_r3StokesL2Path, integral_triangle_swap and
-- r3MildDecodedVelocity_duhamel; r3L2ToTempered_r3H3LaplacianL2Operator and
-- r3HelmholtzPressure_gradient_trajectoryConvection remain unconsumed by any theorem):
-- the decoded Laplacian multiplier and its
-- identification with the distributional Laplacian, its commutations with the Stokes flow
-- and the H2-to-H3 smoothing, the Stokes generator identity in pairing form and its
-- integrated (FTC) form, the Duhamel-triangle Fubini swap, and the decoded mild identity.
#print axioms MNS2.r3L2ToTempered_r3H3LaplacianL2Operator
#print axioms MNS2.r3H3LaplacianL2Operator_stokes
#print axioms MNS2.r3H3LaplacianL2Operator_smoothing
#print axioms MNS2.hasDerivAt_inner_r3StokesL2Path
#print axioms MNS2.integral_inner_r3StokesL2Path
#print axioms MNS2.integral_triangle_swap
#print axioms MNS2.r3MildDecodedVelocity_duhamel
#print axioms MNS2.r3HelmholtzPressure_gradient_trajectoryConvection

-- The projected momentum equation (Clay semantic edge 2b-ii.a-assembly): along an
-- endpoint-safe projected mild solution, the decoded physical velocity satisfies the
-- fundamental integral identity and, at interior times, the strong L2-valued derivative
-- d/dt U = nu Delta U - P((U.grad)U), with the edge-2b-i identified nonlinearity.
#print axioms MNS2.continuousOn_r3MildMomentumIntegrand
#print axioms MNS2.inner_r3MildDecodedVelocity_eq_integral
#print axioms MNS2.r3MildDecodedVelocity_eq_integral
#print axioms MNS2.hasDerivAt_r3MildDecodedVelocity
#print axioms MNS2.r3EndpointSafeProjectedMild_momentum
#print axioms MNS2.exists_r3EndpointSafeProjectedMild_momentum

-- The incompressible Navier-Stokes equation (Clay semantic edge 2b-ii.b, closing edge
-- 2b): along a mild solution with solenoidal initial coordinate, the decoded physical
-- velocity has the strong L2 time derivative, satisfies the unprojected momentum
-- equation with the explicit edge-2a Helmholtz pressure (consumed) componentwise in
-- Schwartz', and is distributionally divergence-free (edge 1a); plus solenoidal
-- propagation along the mild solution and the existence composition.
#print axioms MNS2.r3EndpointSafeProjectedMild_mem_solenoidal
#print axioms MNS2.postcomp_r3LerayL2Operator_eq
#print axioms MNS2.r3EndpointSafeProjectedMild_navierStokes
#print axioms MNS2.exists_r3EndpointSafeProjectedMild_navierStokes

-- Finite-energy semantics (Clay semantic edge 4): the decoded physical velocity of
-- every order-three coordinate has square-integrable pointwise norm, with energy equal
-- to the squared L2 carrier norm; instantiated along mild solutions. No energy
-- inequality is claimed.
#print axioms MNS2.integrable_norm_sq_r3L2
#print axioms MNS2.integral_norm_sq_r3L2
#print axioms MNS2.r3DecodedVelocity_finiteEnergy
#print axioms MNS2.r3MildDecodedVelocity_finiteEnergy

-- Realness transport through the order-three decoder (Stage-9 readiness, Gate A): the
-- decoder symbol J^-3 is real and even, so the bounded decoder commutes with pointwise
-- conjugation and preserves IsR3RealVelocity; hence along every mild solution with
-- physically real initial coordinate the decoded physical velocity appearing in the
-- Navier-Stokes capstone is real at every certified time. No classical C-infinity
-- upgrade and no pointwise representative theorem is claimed.
#print axioms MNS2.r3H3InverseBesselWeightComplex_conj
#print axioms MNS2.r3H3InverseBesselWeightComplex_neg
#print axioms MNS2.r3L2Conj_r3H3ToL2Operator
#print axioms MNS2.isR3RealVelocity_r3H3ToL2Operator
#print axioms MNS2.r3EndpointSafeProjectedMild_isR3RealVelocity_decoded

-- Admissible Schwartz initial data (Clay semantic edge 3, adapter form; Stage-9
-- readiness, Gates B and C): real divergence-free Schwartz velocity fields encode into
-- the solenoidal Bessel carrier, the order-three decoder inverts the canonical encoder
-- on the Schwartz core, and the literal datum is smooth, rapidly decaying, classically
-- divergence-free, real and finite-energy. The frequency-side and classical
-- divergence-free conditions are proved EQUIVALENT on the Schwartz core (pointwise
-- transfer identity with the nonzero constant 2 pi i, plus Schwartz Fourier inversion),
-- so the interface predicate is exactly "real and classically divergence-free" and
-- nothing convenient is smuggled into the definition. The entry capstone starts the
-- certified local Navier-Stokes theory from such a datum; the dichotomy corollary feeds
-- the same datum into the already-proved continuation machinery (Gate C, instantiation
-- only); and the witness chain exhibits an explicit NONZERO admissible datum, so the
-- capstone is neither an empty implication nor a statement about the zero datum.
-- No arbitrary-H3 characterization is claimed; H3 does not imply smoothness anywhere
-- here. Terminal by design (audited but consumed by no other module): the entry
-- capstone, the dichotomy corollary, the interface characterization, the datum
-- certificates (.classicalDivergence / .smooth / .decay / r3Schwartz_finiteEnergy) and
-- the non-vacuity witness.
#print axioms MNS2.r3SchwartzConjCLM_eq_self_iff
#print axioms MNS2.r3H3ToL2Operator_r3SchwartzToHsCLM
#print axioms MNS2.r3SchwartzDivergence_fourier_apply
#print axioms MNS2.r3Schwartz_rawDivergence_fourier_iff_classical
#print axioms MNS2.isR3AdmissibleSchwartzDatum_iff
#print axioms MNS2.r3NormalizedDivergencePointwise_smul
#print axioms MNS2.IsR3AdmissibleSchwartzDatum.encode_mem_solenoidal
#print axioms MNS2.IsR3AdmissibleSchwartzDatum.classicalDivergence
#print axioms MNS2.IsR3AdmissibleSchwartzDatum.isR3RealVelocity_encode
#print axioms MNS2.IsR3AdmissibleSchwartzDatum.smooth
#print axioms MNS2.IsR3AdmissibleSchwartzDatum.decay
#print axioms MNS2.r3Schwartz_finiteEnergy
#print axioms MNS2.r3AdmissibleSchwartzDatum_navierStokes
#print axioms MNS2.r3AdmissibleSchwartzDatum_blowup_dichotomy
#print axioms MNS2.r3SchwartzWitnessFrequency_divergence
#print axioms MNS2.r3SchwartzWitnessFrequency_conjSymm
#print axioms MNS2.fourier_r3SchwartzWitnessDatum
#print axioms MNS2.r3SchwartzWitnessDatum_real
#print axioms MNS2.r3SchwartzWitnessDatum_ne_zero
#print axioms MNS2.isR3AdmissibleSchwartzDatum_r3SchwartzWitnessDatum
#print axioms MNS2.exists_isR3AdmissibleSchwartzDatum_ne_zero

-- T-SEL bridge formalization (Stage-9 selected theorem, user-commissioned 2026-09-02):
-- the ten-lemma paper bridge of docs/gates/STAGE9_REVERSE_GAP_AUDIT_2026-09-02.md SS-6
-- as a Lean statement layer plus conditional assembly. CLOSED here: the Gronwall-Bellman
-- integral inequality (SEL-6, new standalone infrastructure); the quantitative decoded
-- embedding sup+gradient-sup <= C_emb * carrier norm with explicit Cauchy-Schwarz
-- constants (SEL-2), including the weighted decoder L^1 bound, the everywhere Frechet
-- derivative bound, Schwartz-core pinning, a.e. identification of the measured
-- representative with the decoded velocity, and Lipschitz continuity of the gradient-sup
-- on the carrier; the SEL-7 bookkeeping (norm continuity, integrand integrability, Q
-- monotonicity); SEL-8 realness instantiation; the SEL-9 exponential carrier bound
-- CONDITIONAL on the integrated H3 ladder hypothesis; SEL-10 uniqueness transfer and the
-- sSup/BddAbove plug discharge; and the conditional chain N0 -> N1 -> N2 -> N3
-- (ladder hypothesis + OPEN head hypothesis => unbounded certified horizons => global
-- continuation of the certified class from admissible Schwartz data). NOT closed and NOT
-- claimed: the head N0 (R3TSelGradientBound / R3TSelHead -- open, hypothesis-only, no
-- proof search performed by commission), the Kato-Ponce commutator (SEL-4), the
-- integrated H3 ladder (SEL-5), interior Sobolev smoothing (SEL-3 clause), and the
-- classical Sobolev comparability (SEL-1 clause) -- all four are Prop-valued statement
-- definitions consumed as explicit hypotheses, never asserted, never axiomatized. No
-- Clay-level claim; the terminal node is the certified-class continuation proxy.
#print axioms MNS2.le_mul_exp_of_le_add_intervalIntegral
#print axioms MNS2.integral_weighted_norm_r3DecodedFrequency_le
#print axioms MNS2.norm_fderiv_r3DecodedRepresentative_le
#print axioms MNS2.r3TSel_decoded_embedding
#print axioms MNS2.r3DecodedRepresentative_ae_r3H3ToL2Operator
#print axioms MNS2.r3DecodedSup_schwartz
#print axioms MNS2.r3DecodedGradSup_schwartz
#print axioms MNS2.abs_r3DecodedGradSup_sub_le
#print axioms MNS2.continuous_r3DecodedGradSup
#print axioms MNS2.r3TSelGradIntegral_nonneg
#print axioms MNS2.r3TSelGradIntegral_mono
#print axioms MNS2.r3TSel_initial_carrierNorm
#print axioms MNS2.r3TSel_carrierNorm_continuousOn
#print axioms MNS2.r3TSel_gradIntegrand_intervalIntegrable
#print axioms MNS2.r3TSel_decodedReal_of_admissible
#print axioms MNS2.r3TSel_carrierBound_of_ladder
#print axioms MNS2.r3TSel_uniform_bound_transfer
#print axioms MNS2.r3TSel_uniform_carrierBound_of_head
#print axioms MNS2.r3TSel_horizons_unbounded
#print axioms MNS2.r3TSel_admissibleSchwartz_globalContinuation
#print axioms MNS2.r3TSel_conditional_globalContinuation

-- T-SEL bridge discharge, step 1 (SEL-1, user-commissioned 2026-09-02 third session):
-- the classical Sobolev comparability statement R3TSelClassicalSobolevComparability is
-- now a PROVED theorem: on the Schwartz core the summed squared L2 norms of the iterated
-- Frechet derivatives up to order three are two-sidedly comparable to the squared Bessel
-- carrier norm, with explicit constants c1 = 1/81 and c2 = 27*(2*pi)^6, via iterated
-- line-derivative Fourier calculus, Schwartz Plancherel, the direction-tuple expansion
-- of the multilinear operator norm, and the pointwise weight comparison. No new
-- assumption is introduced; the open Prop of the statement layer is discharged.
#print axioms MNS2.r3TSel_classicalSobolevComparability

-- T-SEL bridge discharge, step 2 (SEL-4, same commission): the BKM derivative-tuple
-- commutator estimate R3TSelKatoPonceCommutator is now PROVED with the explicit constant
-- C = 93*(2*pi)^3 (r3TSel_katoPonceCommutator). Infrastructure proved on the way, all
-- Schwartz-core: the exact Leibniz commutator expansions at orders one to three; the
-- commutation of line derivatives from C^2 symmetry of the second Frechet derivative (no
-- analyticity); integration by parts on R^3 obtained by evaluating the Fourier transform
-- of the derivative at frequency zero (integral_fderiv_apply_eq_zero); the by-parts
-- Gagliardo-Nirenberg quartic interpolation r3TSel_gn_quartic; Cauchy-Schwarz for
-- integrals; single-tuple L^2 bounds by the carrier norm via the proved SEL-1
-- comparability machinery. The sharp fractional (J^3-form) Kato-Ponce commutator is
-- deliberately NOT claimed; it is consumed by nothing in the T-SEL chain.
#print axioms MNS2.lineDerivOp_comm
#print axioms MNS2.integral_fderiv_apply_eq_zero
#print axioms MNS2.integral_mul_le_sqrt_mul_sqrt
#print axioms MNS2.r3TSel_gn_quartic
#print axioms MNS2.norm_toLp_tuple_le
#print axioms MNS2.smul_commutator_three
#print axioms MNS2.r3TSel_term_bound_three
#print axioms MNS2.r3TSel_katoPonceCommutator
