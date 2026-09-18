# T18 Draft A comparison: `thm:insertion`

This table is a clause-by-clause rendering of `paper/sections/03-torus.tex:287-346`.
The R42 column names the closest Section 4 field; “torus-only” means that no
R42 field carries the torus-specific assertion.  The draft uses the registered
T10/T11 names and copies the T13--T17 vocabulary blocks verbatim with source
provenance comments in `DraftA.lean`.

| Paper clause | Draft A field | R42 counterpart / status | Notes |
|---|---|---|---|
| `03-torus.tex:287-289`: smooth reference `(v,π,g)` on `[0,T+δ]` | `reference`, `reference_velocity`, `reference_pressure`, `delta_pos` | `InsertionFamilyAPI.reference`, `reference_velocity`, `reference_pressure` | Torus uses `ClassicalSolutionT`, `RegularThroughT` vocabulary; the horizon is `place.T+δ`. |
| `03-torus.tex:287-289`: `g∈F_T` | `reference_force_mem` | `InsertionLifespanAPI.memForce` (whole-space) | Same hypothesis, torus force class is `forceClassT`. |
| `03-torus.tex:287-289`: `a∈X` | `initial_mem` | derived/implicit in R42 bindings | Torus-only registered class is `initialClassT`. |
| `03-torus.tex:290-291`: one sufficiently small threshold | parameter `ε₀`, `eps_pos` | `InsertionFamilyAPI.ε₀`, `eps_pos` | Threshold is a parameter so the existential statement has exactly `∃ ε₀>0`. |
| threshold is below packet scaling range | `eps_le_scaling` | `eps_le_scaling` | Shared placement and scale data are parameters. |
| threshold is below correction range | `eps_le_correction` | `eps_le_scaling` (indirect) | Torus correction has its own `D.ε₀`. |
| `03-torus.tex:314`: `u_ε=v+w_ε+U_ε` | `velocity_formula` | `InsertionFamilyAPI.velocity_formula` | `U_ε` is `periodizedScaledVelocity`; `w_ε` is `D.correction ε`. |
| `03-torus.tex:314`: `p_ε=π+P_ε` | `pressure_formula` | `pressure_formula` | Torus-only pressure is `normalizedScaledPressure`, with zero Haar mean. |
| `03-torus.tex:314`: `g_ε=g+H_ε+F_ε` | `force_formula` | `force_formula` | `H_ε=correctionForce`; `F_ε=periodizedScaledForce`. |
| `03-torus.tex:291-292`: `g_ε∈F_T` | `force_mem` | `forceDifference_compact` plus ambient class | R42 exports compactness of the difference; Draft A exports the exact torus class membership. |
| `03-torus.tex:291-293`: a classical solution on `[0,T)` | `solution` | V2 `InsertionLifespanV2API.solution` | The existential is pinned to the record's velocity and pressure. |
| T11 uniqueness identifies the constructed solution | `maximal_solution` | V2 `InsertionLifespanV2API.maximal` | Torus-only predicate is `IsMaximalPeriodicSolution`. |
| `03-torus.tex:293-294`: `T_max^ν(a,g_ε)=T` | `lifespan` | `InsertionLifespanAPI.lifespan` | Exact equality in `ℝ≥0∞`. |
| breakdown membership at `T` | `breakdown` | torus-only | Uses registered `breakdownSetT`; combines `force_mem` and `lifespan`. |
| `03-torus.tex:293-294`: speed blows up at `T` | `blowup` | `InsertionFamilyAPI.blowup` | Same pointwise `SpeedUnboundedAt` API; V2 also has a limsup export. |
| `03-torus.tex:294`: unchanged history | `history` | `InsertionFamilyAPI.history` | Torus periodization does not change the early-time equality. |
| `03-torus.tex:295`: support in the chosen ball | `velocityDifference_support` | `velocityDifference_support` | Torus field is represented on `R³`, so `tsupport` is the physical lift support. |
| `03-torus.tex:295`: perturbation divergence free | `velocityDifference_divFree` | `velocityDifference_divFree` | Same pointwise divergence spelling. |
| `03-torus.tex:332-339`: `(b_ε·∇)U_ε=0` | `cross_transport_packet` | torus-only explicit identity | R42 explains the cancellation in `momentum` but does not export both zeros. |
| `03-torus.tex:332-339`: `(U_ε·∇)b_ε=0` | `cross_transport_background` | torus-only explicit identity | Independent field, as required by the proof's expansion. |
| `03-torus.tex:332-346`: exact momentum residual | `momentum` | `InsertionFamilyAPI.momentum` | Explicitly retained after the two cross-term identities. |
| `eq:Eclose` `:300-301` | `energyDifference_memLp`, `energyRateConst`, `energyRate` | `InsertionFamilyAPI.energyRate` | Uses registered `energyENormT`; the `MemLp` guard prevents totalized-norm junk. |
| `eq:Fclose` `:302-303`, `α(p,q)` | `mixedRateConst`, `mixedRateConst_nonneg`, `mixedRate` | `InsertionFamilyAPI.forceConvergence` | Torus-only display keeps the finite-scale bound `ε^α+ε^(α+1)` and `MemMixedLebesgueT`. |
| `eq:Hsclose` `:304-306`, `0≤s<1/2` | `sobolevRateConst`, `sobolevRateConst_pos`, `sobolevRate` | `InsertionFamilyAPI.forceConvergence` | Exact exponents are `1/2-s` and `3/2-s`; path guard is `MemForceSobolevT`. |
| negative `s` convergence `:306` | `negative_s_memLp`, `negative_s_convergence` | torus-only | Registered torus Sobolev norms make the inhomogeneous `s<0` monotonicity clause explicit. |

## Parameter/field choices

`P : T14.Draft.PacketImportAPI ν`, the shared `PlacementData`, the T15
`ScalingAPI`, the T16 cutoff data, and T17 `CorrectionAPI` are parameters.
They are proof inputs fixed before the scale and are deliberately not copied
into separate existential fields; this makes `T`, `x₀`, `K_*`, and `ε₀` the
same terms in every formula.  The T11 local/continuation APIs and the T12
`MeanZeroSobolevCalculusAPI` are also parameters: they are consumed by the
maximal-lifespan argument and by the `H² ↪ L∞` bridge (`boundedRepresentative`),
not conclusions of the insertion construction.

The reference datum, pressure, force, and `ClassicalSolutionT` are parameters
of the record as well, while their manuscript hypotheses (`δ>0`, class
membership, and field pinning) remain explicit record fields.  The inserted
velocity/pressure/force are fields because the theorem asserts one common
family.  `ε₀` is a parameter, rather than a field, solely so
`periodicInsertionStatement` can literally expose `∃ ε₀, 0 < ε₀ ∧ Nonempty …`.

## Ambiguities resolved

1. The registered `forceClassT`, `forceSobolevENormT`, and energy norms are
   used; the copied T10 names are not opened in the T18 namespace, avoiding a
   silent drift to the unregistered spelling.
2. `PlacementData` occurs in the T15/T17 copies under two historical
   namespaces.  Draft A's T17 correction block locally aliases it to the
   T15 placement record, so the scaling and correction really share one
   placement rather than being related by an unproved equality.
3. The theorem display gives an `L^q_tL^p_x` bound for all `1≤p,q≤∞`, while
   the registered R42 convergence field is a limiting statement.  Draft A
   records both the finite-scale bound and a concrete `MemMixedLebesgueT`
   witness for every norm.
4. The paper writes `limsup‖u_ε‖∞=∞`; the registered pointwise
   `SpeedUnboundedAt` is used, exactly as R42 does, and is paired with the
   full classical solution field.  A future torus V2 contract could add the
   essential-supremum limsup form.

## Lemmas/APIs the proof will consume

* T11: `PeriodicLocalTheoryAPI.velocity_unique` and `pressure_unique`,
  `horizon_le_lifespan`, `exists_maximal`, `maximal_unique`; then
  `PeriodicContinuationH3API.higherOrderBound`, `extendsBeyond`, and
  `lifespanInfiniteOfLocallyFinite`.
* T12: `MeanZeroSobolevCalculusAPI.boundedRepresentative` for
  `H² ↪ L∞`, together with `hTwo_le_laplacian` and `spectralGap` in the
  continuation estimate.
* T13: `LocalizationAPI.localization`, `wholeSpace_identity`,
  `torus_identity`, `endpoint_zero`, and `endpoint_one` for the one-copy
  periodized packet/correction norms.
* T14/T15: `PacketEnergyAPI.energy_le_work` and `work_eq_square`; the
  `ScalingAPI` fields `velocity_singleCopy`, `pressure_singleCopy`,
  `force_singleCopy`, `solution`, `unboundedSpeed`,
  `packetEnergyIdentity`, `packetDissipationIdentity`,
  `packetMixedScaling`, and `packetSobolevBound`.
* T16/T17: `LocalPotentialAPI.potential_curl`,
  `CorrectionAPI.correction_cancels`, `correction_divergence_free`,
  `correction_energy_bound`, `force_mixed_bound`, and
  `force_sobolev_bound`; the profile identities justify the two cross-term
  zeros and the smooth force class.
* Registered T10: `ClassicalSolutionT`, `maximalLifespanT`,
  `breakdownSetT`, `forceClassT`, `initialClassT`, `energyENormT`, and the
  four T11 API records.

## Implementation candidates

The existing periodic implementation surface to audit before proving this
record is:

```text
grep -nE "^(def|structure|theorem) " \
  formalization/NSFormalization/Paper1/PeriodicInsertion*.lean \
  formalization/NSFormalization/Paper1/PeriodicCrossComponentTransport*.lean
```

Likely entry points are the periodic insertion/localization modules for the
formula and support fields, and the cross-component transport modules for
`cross_transport_packet` and `cross_transport_background`.  The lifespan
fields should be discharged through the registered T11 APIs rather than by
importing the schematic citation axioms.
