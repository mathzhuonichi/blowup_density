# Lane 357-SPEC-t18-draft-b — report (double-blind draft B of `thm:insertion`)

## 1. What was stated
The Lean statement (no proofs) of Theorem `thm:insertion`, "exact local insertion
on `T³`" (`paper/sections/03-torus.tex:287-311`, proof `:312-346`): one
`Type`-valued structure `BlowupDensity.T18.DraftB.PeriodicInsertionAPI` with
**10 parameters** and **43 fields**, plus `def periodicInsertionStatement : Prop`
in the paper's quantifier order (`∀ν>0, ∀ packet/placement/data/reference/
correction, δ>0 → g∈𝓕 → a∈𝓧 → Nonempty (PeriodicInsertionAPI …)`).

Field coverage of the theorem's clauses:
- inserted triple `(u_ε,p_ε,g_ε)` + `eq:insertion` displays (`velocity/pressure/
  force`, `*_formula`, incl. the `∫_{T³}p=0` gauge on `p_ε`);
- class memberships `g_ε∈𝓕`, `g_ε-g∈𝓕`, `a∈𝓧` (`force_mem`, `forceDifference_mem`,
  `initial_mem`);
- classical torus trajectory on `[0,T)` (`velocity_smooth,pressure_smooth,initial,
  incompressible,momentum,history,velocity_periodic,solution`);
- **maximal lifespan exactly `T`** (`maximal`, `lifespan : maximalLifespanT … =
  ofReal T`);
- blow-up (i) in both pointwise (`blowup`) and ess-sup (`blowup_limsup`) forms;
- **the two vanishing cross-transport terms as explicit `=0` identities**
  (`crossTransport_background_advects_packet`, `crossTransport_packet_advects_background`);
- localization (iii): `velocityDifference_divFree`, `velocityDifference_support`
  (`⊆ periodicSet (ball x₀ (ε·ρ))`), `diffSupport_in_chart`;
- the three rates (iv) with exact exponents — `energyRate` (`ε^{1/2},ε^{3/2}`),
  `forceDifference_mixed_bound` (`ε^{α(p,q)},ε^{α(p,q)+1}`),
  `forceDifference_sobolev_bound` (`ε^{1/2-s},ε^{3/2-s}`, `0≤s<1/2`), plus the
  `s<0` `Tendsto` tail.
Every quantitative field carries an honesty guard (`MemLp`/`MemForceSobolevT`);
`ν>0` via `correction.viscosity_pos`; `ε∈Ioc 0 ε₀` on every family clause. No
field is `True`, a tautology, or an argument-ignoring def (brief grep
`': *True|:= *0$|→ *True'` empty).

## 2. Files
- `research/T18/DraftB.lean` (1406 lines) — elaborates, 0 errors.
- `research/T18/COMPARISON_B.md` — clause→field table with R42/R42.v2 counterparts,
  choices, ambiguities, needs-a-lemma list, implementation candidates.
- `research/T18/REPORT_357.md` — this report.

Vocabulary: the T13/T15/T16/T17 blocks (`LocalizationAPI`, mixed norms,
`PlacementData`, `CutoffData`, `LocalPotentialAPI`, `CorrectionAPI`, plus the
T10.Draft energy/force-norm restatements they depend on) are copied **verbatim**
from `research/T17/Spec.lean:17-987` in a delimited block. The registered
`Contracts.V1.TorusLocalTheory` names (`energyENormT`, `forceSobolevENormT`,
`ClassicalSolutionT`, `maximalLifespanT`, `IsMaximalPeriodicSolution`,
`forceClassT`, `initialClassT`, `normalizePressureT`) and the registered
`Contracts.V1.MaximalPartial.{limsupLeft,speedENorm}`, `Contracts.V1.{
SpeedUnboundedAt, scaledPressure, scaledForce, spatialDerivative, alpha}` are
imported and used by name. Five `example … := rfl` drift checks pin the copied
`T10.Draft` restatements (`energyENormT`, `energyEssSupT`, `energyGradientT`,
`forceSobolevENormT`, `IsPeriodicSobolevPath`) against their registered spellings
(all pass). Only two new defs are introduced — `periodicScaledPressure`/
`periodicScaledForce`, the lattice-sum companions of the copied
`periodicScaledPacket` for `P_ε`/`F_ε`.

## 3. Ambiguities and lemma needs
- Pressure gauge: `eq:insertion` writes `p_ε=π+P_ε` but `:318-320` normalizes by
  the torus mean; rendered with `normalizePressureT` (torus-faithful), unlike the
  whole-space R42 twin. A second reader could split into `p_ε-π=P_ε` + a gauge field.
- `eq:Hsclose` range `0≤s<1/2` (strict), narrower than `eq:HHs`'s `0≤s≤1`; kept as
  the theorem states.
- Support diameter `O(ε)` modelled by a carried positive `diffSupportRadius` (not
  reusing `r`, which bounds `w_ε` only).
- Needs-a-lemma (see COMPARISON_B for the field-level list): T11
  `PeriodicLocalTheoryAPI` uniqueness/maximal + `PeriodicContinuationH3API`
  continuation for `lifespan`/`maximal`; T12 `boundedRepresentative` (`H²↪L^∞`) for
  the `≤T` half; T16 `correction_cancels`/`potential_curl` (`eq:bgzero`) for the
  cross-transport; T17 `correction_energy_bound`/`force_mixed_bound`/
  `force_sobolev_bound` for the three rates; **T15/prop:scaling `eq:packetEscale/
  Fscale/Hs`** for the `(M+D)ε^{1/2}`, `ε^{α}`, `ε^{1/2-s}` terms — these torus
  scaling identities are **not yet a registered contract** (a registration gap the
  T18 assembly must close, e.g. by promoting `research/T15/Spec.lean`'s `ScalingAPI`).
- Implementation candidates: `Paper1/PeriodicInsertion.lean` (`velocity/pressure/
  force`, `Properties`, `of_insertion`), `PeriodicCrossComponentTransport*.lean` /
  `PeriodicProjectedTransport.lean` (transport cancellation),
  `PeriodicInsertionSupport.lean`, `…FiniteEndpoints/…PositiveConvergence/
  …EndpointRateBound.lean`, `InsertionEnergy.lean`.

## 4. Commands and results
- `. scripts/lean-env.sh`; from `verification/`:
  `LEAN_NUM_THREADS=6 lake env lean ../research/T18/DraftB.lean`
  → **EXIT=0, empty output** (elaborates; the 5 `rfl` drift checks and every field
  type-check).
- `grep -nE ': *True|:= *0$|→ *True' research/T18/DraftB.lean` → **empty**.
- Field count: 43; parameters: 10.
