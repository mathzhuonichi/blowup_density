# Lane 168: persistence route and the next actual nonlinear bridge

## 当前方案（lane 169，2026-09-15）

以 [H¹ 实施方案](IMPLEMENTATION_PLAN_169.md) 为当前执行依据。独立 [Astra xhigh 审核](REVIEW_H1_REFACTOR_169.md) 原文归档保留审查时的路径/行号；云端核对源码时以报告记录的 A01 / R43 commit 为准。以下历史供应记录保留，当前顺序和完成边界由新方案明确。

## Required local theorem

`paper/sections/02-preliminaries.tex:105`, `prop:local`, requires a unique maximal smooth velocity for smooth all-order initial data and force, pressure in the stated convention, a common interval for all Sobolev orders, and smooth extension if the H2 squared time integral remains finite. These are separate obligations; finite-order local existence or Bochner maximal regularity does not alone prove them.

| Obligation | Actual supply | Remaining work |
| --- | --- | --- |
| Finite-order local path, initial value, true force | `Source/OrdinaryForcedLocal.exists_local`; `C01.forcePath_field`, `forcePath_jetLp_continuous` | Local lifespan depends on q. |
| One derivative gain on that same interval | `A01/ForcedMaximalRegularity.forced_mild_maximal_regularity`, `exists_local_of_memForce` | W is TimeLp H(q+2), only a.e. restriction; no endpoint or continuous high path. |
| Consistency of nonlinear spatial maps | `SobolevNonlinearCompatibility.restrict_asymmetricTransport`; `CorrectionSourceRestriction.truncate_transport`; `SmoothFieldSobolevTime.restrict_sobolev` | **Done in lane 168:** `ForcedSourceUpgrade.sourceTime_restriction` specializes to the actual source and the same lane-166 W. Regularized-difference source alignment remains. |
| Higher nonlinear source in time L2 | `TimeSobolevTransport.transportTime`, `transportTime_ae`; `TimeCorrectionSource.restrict_transport_state` | **Done in lane 168:** `sourceTime`, `sourceTime_ae`, `sourceTime_integrable_sq`, `exists_local_source_of_memForce`; no continuous high path is claimed. |
| Heat/mild restriction | `MildEquationBridge.truncate_heatOperator`, `truncate_heatKernel`, `truncate_heatConvolution` | Existing kernel truncation yields lower heat flow; a complete cross-order nonlinear mild identity still needs the actual source bridge and integral transport. |
| Unique compatible high solutions on overlaps | `VolterraUniqueness.mild_solution_unique` | The supplied theorem has a contraction-ball norm bound and small kernel-mass premise. Whole-window uniqueness needs a real window/restart argument. |
| Continuous higher-order persistence on the fixed-base interval | `HeatGradientTrace.heat_gradient_trace_dissipation`, `heat_gradient_trace_bound`; finite-Sobolev energy remains available for a tame alternative | Align regularized differences with the actual source; sum finite words; prove uniform Cauchy and complete/identify the continuous high path. H¹-to-high-order persistence remains a separate task. |
| Construct smooth representative / pressure / time smoothness | `OrdinarySobolevTower` reconstructs from continuous all-order realizations; ordinary time derivative supplied by `Source/OrdinaryForcedTime` | Build the same-horizon tower first; then bootstrap time regularity from actual MemForceR and reconstruct pressure. |
| Maximal continuation from finite H2 time integral | A04 conditional restart/extension, high Grönwall and force timeShift bounds; `Horizon` retains its prescribed-S auxiliary role | Complete H¹-budget classical API and A02 restart; evaluate m=3→H¹ along the actual maximal family, with hpath and endpoint gluing. Preserve the all-order A04 obligation. |

## New usable analytic supply, beyond lane 163's audit

`AsymmetricTransport.asymmetricTransport_bound` controls actual Hs × H(s+1) transport in Hs. `TimeSobolevTransport.transportTime` consequently multiplies the existing continuous H(q+1) velocity by the constructed TimeLp H(q+2) state to produce a genuine TimeLp H(q+1) nonlinearity. Its `transport_regularization_commutator` also proves the corresponding heat commutator tends to zero in that time norm; it is useful for passing finite-word regularized energy identities to the limit, but is not itself a high-order energy estimate.

`TimeCorrectionSource.restrict_transport_state` proves that this asymmetric high source restricts to the literal lower transport when the high state restricts to the low state. Lane 166 already supplies that condition a.e. No additional higher-regularity premise is needed. The actual force has a compatible H(q+1) path by `MemForceR`; the order-independent L2 Leray projection gives exact restriction compatibility.

## Implemented source bridge (lane 168)

`ForcedSourceUpgrade` constructs the actual projected source `P(f−advection(u,W))` in TimeLp H(q+1), and proves its restriction equals the original Hq nonlinear source a.e. on exactly the lane-166 horizon. The consumer retains the true physical force slice identification. This supplies the missing high-order source term for a subsequent finite-mild energy/trace argument, rather than inventing a continuous high-order path.

## Non-circular continuation route

Use this source and finite-word mild/regularized time laws to populate the hypotheses of the existing finite-Sobolev energy theorem. Establish a tame high-order bound driven by an already controlled low norm, so high-order partial solutions persist to the fixed low-order horizon. Restrict and identify them by actual mild uniqueness on overlapping windows; then use the resulting continuous compatible realizations to build the tower. This is one possible route, but a full nonlinear tame-energy argument is not established as necessary: the linear trace route below may supply the one-order continuous gain more directly. `A01/AprioriRows` and `GronwallInstance` assume a completed classical solution and cannot be used to construct it.

The initial source audit ran no Lean or lake command; final lane validation is recorded below. The table now distinguishes completed source/trace supply from remaining persistence obligations.

## Refined next step: linear heat trace after the source upgrade

The upgraded actual source may permit a shorter persistence proof without a new complete nonlinear high-energy argument. `HeatGradientEnergy.heat_gradient_energy_bound` bounds the derivative of gradient energy using only the undifferentiated L2 source norm. `HeatGradientIntegral.heat_laplacian_integral_bound` integrates it, but its exported conclusion drops the nonnegative terminal gradient energy and controls only the Laplacian time integral. Its proof already contains the pre-drop inequality from which a terminal gradient-energy estimate can be proved.

`HeatMaximalEstimate.heat_time_H2_bound` and `MaximalTopCauchy.maximalApproximation_cauchy` currently conclude Bochner-time bounds/Cauchy convergence, not supnorm Cauchy convergence in a higher continuous path space. `path_H2_point_bound` still has the instantaneous Laplacian norm on the right and therefore is not the missing trace bound.

The scalar terminal gradient estimate is now exported (see below). Next, apply it to actual regularized heat differences, bounded by the true high-order initial difference plus the L2-time difference of the upgraded source. Apply it to the finite word blocks, establish uniform Cauchy convergence in C([0,T], H(q+2)), complete that continuous path space, and identify its lower restriction with u. `RegularizedMildEquation` supplies actual regularized time laws, while `TimeSobolevTransport.transport_regularization_commutator` supplies the source commutator limit. A correct proof must explicitly align those regularizations with this lane's higher TimeLp source; that alignment and the finite-word uniform Cauchy construction are not yet exported as a complete theorem. Smooth initial data supply the high-order initial term. This route preserves T and can potentially iterate once the continuous lift is proved; mere source/W time-L2 convergence cannot be substituted for the uniform estimate.

## Lane-168 trace export status

The new `A01/HeatGradientTrace.lean` now contains `heat_gradient_trace_dissipation` and `heat_gradient_trace_bound` (compiled and axiom-audited successfully), deriving the retained terminal estimate from the actual heat PDE and continuity assumptions. Thus the missing work is no longer merely exporting that scalar terminal inequality. The remaining steps are actual-source alignment for regularized differences, finite-word summation, a uniform Cauchy estimate, and completion/identification of the continuous high-order limit. A single terminal inequality is not itself the completed uniform trace construction.

## Final lane status

Luna high completed both source and trace modules with native exit 0 (source r3, 10201 jobs; trace, 3829 jobs). The seven source and two trace axiom audits contain only propext, Classical.choice and Quot.sound. The lead also confirmed 26 contract checks and the mutation suite passed with native exit 0; see `tmp/lake_test_168_persistence.log` and `tmp/mutations_168_persistence.log`. `ATTEMPTS_SOURCE_UPGRADE_168.md` records the r1/r2/r3 elaboration repairs.

The implemented source upgrade and terminal gradient-energy estimate are complete. The proposed continuation route remains future work: actual-source alignment for regularized differences, finite-word uniform Cauchy bounds, and completion/identification of a continuous higher-order path. The fixed-q TimeLp witnesses and their a.e. compatibility do not assert endpoint traces or a continuous all-order tower.
