# T20 double-blind draft B comparison

Scope: Proposition `prop:critical` and its proof in
`paper/sections/03-torus.tex:383-503`.  This draft did not inspect any other
T20 lane.  The Section 4 comparison targets are the registered contracts
`R43.critical_regularity`, `C01.energy_absorption`, and `A04.continuation`.

## Paper clause to Lean field

| Paper clause | Draft B field | R43 / C01 / A04 counterpart |
|---|---|---|
| `:383-387`, one universal `c>0` before `ν,g` | `c`, `c_pos` | `R43.CriticalRegularityAPI.c`, `hc` |
| `:426-440`, absolute `C₀` | `Ccritical`, `Ccritical_pos` | Internal to the proof of `R43.universal`; no R43 field.  The analogous absorption constant is data in `C01.EnergyAbsorptionAPI` through its inherited `C₁` field. |
| `:467-484`, absolute `C₁` and Young constant | `Censtrophy`, `Censtrophy_pos`, `CHone`, `CHone_pos` | `C01.C₁` and `C01.CRH1`/`CRH1_pos` |
| `:492-500`, assembled `H²` constant | `Ccriterion`, `Ccriterion_pos` | `C01.Cassembly`/`Cassembly_pos`, with the torus mean-zero comparison from T12 replacing the whole-space Fourier assembly |
| `:457`, `c<1/(4C₀)` | `c_lt_critical` | Internal bootstrap choice in R43; deliberately hidden by `R43.inhomogeneousAtZero` |
| `:477-480`, `c<1/(4C₁)` | `c_lt_enstrophy` | Discharges the gate of `C01.enstrophyDifferentialBound`; internal to R43 |
| `:389-392`, the solution starts from the zero datum | `zero_initial_admissible` | The fixed zero datum used by `R43.inhomogeneousAtZero`; supplies T11's `initialClassT` premise explicitly |
| `:392-418,467-488`, all displayed norms are genuine finite slice norms | `reduction_regular` | The role is split between the maximal classical solution used by R43, inherited C01 slice regularity, and T12's `MemPeriodicHomogeneous`/`MemPeriodicHmVector`; no single Section 4 field |
| `:395-403`, `m(t)=mean(u(t))` | `mean_identification` | Torus-only; T11 `PeriodicMeanReductionAPI.mean_formula`; no R43/C01/A04 analogue |
| `:402-403`, `m(0)=0` | `mean_initial` | Torus-only; implicit in T11's data-defined `galileanMeanT` |
| `:402-403`, `m'=gbar` | `mean_derivative` | Torus-only; T11 `PeriodicMeanReductionAPI.mean_derivative` |
| `:404-406`, `eq:meanbound` | `mean_bound` | Torus-only; no R43/C01/A04 field |
| `:407-410`, `eq:meanfree` with `(m·∇)v` retained | `mean_free_equation` | No whole-space counterpart; T11's Galilean `transformed_solution` removes this term and therefore cannot replace this field |
| `:411`, constant transport is skew-adjoint | `constant_transport_skew` | Torus-only; no R43/C01/A04 field |
| `:411`, constant transport commutes with Fourier multipliers | `constant_transport_commutes_lambda` | Torus-only; stated against T12 `IsPeriodicLambda`; no R43/C01/A04 field |
| `:438-440`, `eq:criticalenergy` | `critical_energy` | Described in the proof of `R43.universal`, but not a registered R43 field; explicitly outside C01's ordinary-energy scope |
| `:442-444`, `eq:bintegral` | `b_integral` | Hidden in `R43.inhomogeneousAtZero`; no standalone R43/C01/A04 field |
| `:454-458`, `eq:ybound` plus the completed bootstrap | `y_bound` | Hidden in `R43.universal`/`inhomogeneousAtZero`; no standalone registered field |
| `:482-484`, `eq:H1energy` | `hOne_energy` | `C01.enstrophyDifferentialBound` is the direct whole-space shape; this torus field substitutes `v,h` and derives its absorption from `y_bound` |
| `:486-500`, orthogonal modes and finite squared-`H²` bound | `continuation_bound` | `C01.h2TimeIntegralZeroDatum`, with the extra torus mean mode and T12 `hTwo_le_laplacian` |
| `:490-502`, `eq:criterion` is finite at every finite endpoint | `maximal_criterion_finite` | Exact premise shape of T11 `PeriodicContinuationAPI.lifespanInfiniteOfLocallyFinite`; counterpart is `A04.ContinuationV2API.lifespanInfiniteOfLocallyFinite` |
| `:383-390,503`, `g∈F_T`, `ρ<cν` implies global lifespan | `global_regular` | `R43.CriticalRegularityAPI.inhomogeneousAtZero`; continuation conclusion matches A04/T11 `lifespanInfiniteOfLocallyFinite` |

The helper definitions mirror the manuscript notation directly:
`meanPathT`, `meanFreeVelocity`, `meanFreeForce`, `constantTransportT`,
`criticalY`, `criticalZ`, `criticalB`, `criticalBIntegral`, and `criticalRho`.
`meanModeCriterionIntegral` exposes the equality in `:496-499` rather than
collapsing it immediately to mere finiteness.

## Choices

1. `CriticalRegularityTAPI` is Type-valued and indexed by the binding T11
   `PeriodicLocalTheoryAPI`, `PeriodicContinuationAPI`,
   `PeriodicMeanReductionAPI`, and the binding T12
   `MeanZeroSobolevCalculusAPI`.  Like A03/A05/R43, it carries constants as
   data.  A Prop-valued record could not carry the selected numerical radius
   and estimate constants without moving them under an existential and
   obscuring their order before `ν` and `g`.  Dependency packages are indices,
   not duplicated theorem fields, so the T20 fields remain the paper clauses.
2. The main statement uses exactly
   `forceSobolevENormT 1 (1/2) g < ENNReal.ofReal (c*ν)` and
   `maximalLifespanT ν 0 g = ⊤`.  It requires `0<ν` and
   `g∈forceClassT` explicitly.  No mean-zero-force hypothesis was inserted.
3. All total norms remain `ℝ≥0∞`.  The three real differentiated energy
   quantities necessarily use `ENNReal.toReal`; `reduction_regular` explicitly
   supplies `≠⊤` for every operand, so an absent datum cannot become a junk
   zero.  `critical_energy` and `hOne_energy` existentially return derivative
   values instead of using a potentially vacuous `HasDerivAt ... → ...` premise.
4. T11's `galileanMeanT` is reused only as the data-defined mean path.  The
   velocity and force are not translated: `v=u-m`, `h=g-gbar`, and
   `mean_free_equation` retains `(m·∇)v`, as required by the Section 3
   reconciliation note.
5. `meanForceIntegralT`, `criticalBIntegral`, and the force-square integral
   are lintegrals.  The choices `Ioc 0 t`, `Ioo 0 S`, and
   `forceTimeMeasure=volume.restrict(Ioi 0)` differ only at null endpoints and
   preserve the paper's `(0,∞)` convention.
6. The paper's generic constants in `eq:H1energy` and `:499` are kept as
   separate positive fields (`CHone`, `Ccriterion`).  This avoids baking a
   proof-dependent product of T12 constants into the theorem statement.
7. The labeled estimates are exposed even though the registered R43 contract
   hides its proof internals.  The T20 brief explicitly requests these
   standalone proof facts, and they are the interfaces needed to connect the
   torus-specific mean reduction to C01/A04 shapes.

## Ambiguities

- The paper writes ordinary real integrals and norms.  The repository's safe
  convention is extended nonnegative reals.  Draft B uses `ℝ≥0∞` for all
  undifferentiated quantities and converts only finite slice norms when a real
  derivative inequality is unavoidable.
- `eq:ybound` is first proved on an interval satisfying a bootstrap hypothesis
  and then propagated through the entire lifespan.  The field records the
  final, useful lifespan-wide conclusion under `ρ<cν`, not the provisional
  conditional estimate.
- Line `:411` says commutation with the Fourier multiplier for every real
  Sobolev order.  T12 currently exposes a physical graph only for `Λ`.
  `constant_transport_commutes_lambda` records that available concrete case;
  the general coefficient-weight commutation remains a lemma below.
- The paper's maximal solution is a single common pair below its lifespan.
  T10's `maximalLifespanT` alone is a supremum of horizons, so the continuation
  field uses T11's `IsMaximalPeriodicSolution` rather than arbitrary unrelated
  solutions at each horizon.
- The exact numerical products defining `Ccritical`, `Censtrophy`, and
  `Ccriterion` depend on normalization of Hölder, Fourier multipliers, and the
  T12 comparison constants.  The paper asserts only absolute constants, so
  Draft B does not prescribe products not stated there.

## Needs a lemma

1. Zero datum belongs to `initialClassT`; a T11 local/maximal solution pair
   exists for every `ν>0`, `g∈forceClassT`.
2. The T11 mean formula specialized to zero data agrees definitionally or
   propositionally with `meanPathT`; derive `mean_initial`, `mean_derivative`,
   and `mean_identification` without a Galilean translation.
3. The zero Fourier coefficient and Cauchy--Schwarz bound
   `|gbar(t)| ≤ ‖g(t)‖_{H^(1/2)}` and its time-integrated form
   `meanForceIntegralT ≤ criticalRho`.
4. Subtracting the time-dependent constant from the PDE gives
   `mean_free_equation`, including derivative algebra and unchanged pressure.
5. Periodic integration by parts proves skew-adjointness of
   `constantTransportSpatialT`; coefficient multiplication proves commutation
   with `Λ` and, eventually, arbitrary real Fourier weights.
6. Classical periodic slices and centered force slices provide the exact
   `MemPeriodicHomogeneous`, `MemPeriodicHmVector`, `MemLp`, and finiteness
   facts in `reduction_regular`.
7. Mean removal is contractive for the inhomogeneous half-order datum path,
   giving `criticalBIntegral ≤ criticalRho` with compatible measurable
   witnesses.
8. Testing against `Λv`, pressure cancellation, the T12
   `velocityCriticalL3` and `gradientLambdaCriticalL3` bounds, and force
   pairing produce `critical_energy` with an actual derivative witness.
9. A scalar continuity/bootstrap lemma in the style of
   `CriticalEnergyCertificate.norm_le_radius` produces the full `y_bound`.
10. Testing against `-Δv`, T12 `velocityCriticalL3` and `gradientLSix`, and
    Young's inequality produce `hOne_energy`; integrate it on preterminal
    intervals.
11. Smooth compact time support implies
    `meanFreeForceLTwoSqIntegral (meanFreeForce g) ≠ ⊤`.
12. Orthogonality of the zero and nonzero Fourier modes gives the exact
    `meanModeCriterionIntegral` equality; T12 `hTwo_le_laplacian` gives the
    quantitative continuation bound.
13. Restriction of a T11 maximal common pair to every finite `S` transports
    `continuation_bound` into `maximal_criterion_finite`; T11
    `lifespanInfiniteOfLocallyFinite` then proves `global_regular`.

## Existing `Paper1/` implementation candidates

The following were inspected only as implementation candidates and are not
imported by the draft:

- `PeriodicCriticalRegularity.lean`: `CriticalRegularityCertificate`,
  `exists_critical_regularity_constant`, `critical_regular_ball`.
- `CriticalEnergyCertificate.lean`: `CriticalEnergyCertificate`,
  `CriticalEnergyCertificate.norm_le_radius`.
- `CriticalEnergyCoercivity.lean`:
  `CriticalEnergyCertificate.dissipation_coercive`.
- `CriticalEnergyDerivative.lean`:
  `absorbed_energy_inequality_on_interval`, `energy_derivative_le`.
- `CriticalEnergyForcing.lean`: `forcing_work_le_radius`.
- `CriticalEnergySignatures.lean`: the nonnegativity and initial-signature
  lemmas.
- `PeriodicMeanZeroEstimate.lean`:
  `finite_meanZero_l2_le_homogeneousHalfEnergy`,
  `finite_periodicFourier_meanZero_l2_le_homogeneousHalfEnergy`,
  `one_le_periodicAngularMagnitude`, and
  `finite_meanZero_l2_le_homogeneousHalfEnergy_one`.

These files supply useful scalar bootstrap and finite-mode Poincaré pieces,
but `PeriodicCriticalRegularity.CriticalRegularityCertificate` currently hides
the analytic bridge in one `global_lifespan` field.  It is therefore a consumer
shape, not an implementation of the richer T20 API.
