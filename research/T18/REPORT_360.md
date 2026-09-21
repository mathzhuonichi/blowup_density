# Lane 360-SPEC-t18 — report (finalized T18 specification)

## 1. What was stated
Reconciled statement-only spec of **Theorem `thm:insertion`** (exact local
insertion on `T³`, `paper/sections/03-torus.tex:287-346`): the `Type`-valued
`structure BlowupDensity.T18.Spec.PeriodicInsertionAPI` (**11 parameters, 45
fields**) plus `def periodicInsertionStatement : Prop` in the paper's quantifier
order. Base draft B, four corrections from draft A, per `RECONCILIATION.md` §3.
Field groups (all with `03-torus.tex` docstrings, quantifier order, non-vacuity):
hypotheses `delta_pos/reference_force_mem/initial_mem` (3); threshold
`ε₀/eps_pos/eps_le_scaling/eps_le_cutoff` (4); inserted triple + `eq:insertion`
`velocity/pressure/force/velocity_formula/pressure_formula/force_formula` (6);
class `force_mem/forceDifference_mem` (2); kinematics
`velocity_smooth/pressure_smooth/initial/incompressible/momentum/history/velocity_periodic`
(7); solution/lifespan/blow-up `solution/maximal/lifespan/blowup/blowup_limsup`
(5); cross-transport (2); localization
`velocityDifference_divFree/diffSupportRadius(_pos)/velocityDifference_support/diffSupport_in_chart`
(5); rates `energyRate` + mixed (const/nonneg/`MemMixedLebesgueT`/bound) + Sobolev
(const/pos/`MemForceSobolevT`/bound) + `s<0` tendsto + `negative_s_memLp` (11).

## 2. Files (all under research/T18/)
- `Spec.lean` — the reconciled spec (elaborates, 0 errors). Vocabulary copied
  verbatim in historical namespaces (T13.Spec, T14.Draft, T15.Draft, T16.Draft,
  T15.Spec, T17.Spec with the `abbrev PlacementData := T15.Draft.PlacementData`
  shim), draft A's blocks minus its T12 block; registered names imported.
- `COMPARISON.md` — merged paper-clause → field table (A/B provenance, R42
  counterpart, ruling) + §Proof dependencies (§4) + §Open questions (the three).
- `DraftA.lean`, `DraftB.lean`, `COMPARISON_A.md`, `COMPARISON_B.md`,
  `REPORT_356.md`, `REPORT_357.md` — provenance copies from the two branches.
- `RECONCILIATION.md` — lead's binding decisions (on base, unchanged).

## 3. Deviations from the reconciliation (with reasons)
- **pressure_formula.** §3.1 said "re-point pressure_formula to
  `normalizedScaledPressure`"; §3 "Norms/exponents/spellings (binding)" said
  `p_ε = normalizePressureT (π + P_ε)`. These conflict (`normalizedScaledPressure
  = normalize(P_ε)` alone, giving `π + normalize(P_ε)`, whereas the binding
  spelling is `normalize(π + P_ε)`). Resolved to the **binding** spelling
  `normalizePressureT (fun z => reference.pressure z + periodizedScaledPressure P
  place.x₀ place.T ε z)` — this both uses the scaling record's periodized field
  (`periodizedScaledPressure`, satisfying §3.1's intent) and keeps
  `normalize(π + P_ε)`. Equals A's `π + normalize(P_ε)` since `π` is mean-zero.
- **T10 restatements not copied; no T10 rfl pins.** §3 both says "pin the copied
  T10.Draft restatements (B does this)" and "`energyENormT`/`forceSobolevENormT`
  … imported, never copied". Followed the second (and draft A's proven layout):
  `T10.Draft` is an empty compat namespace and the registered
  `TorusLocalTheory.{energyENormT,forceSobolevENormT,…}` are used directly, so
  there are no copied T10 restatements to pin. Drift `rfl` checks instead live in
  the copied `T15.Draft` block (`scaledPacket`/`scaledPressure`/`scaledForce`,
  `normalizedScaledPressure`) plus two added in `T18.Spec`
  (`alphaT = Contracts.V1.alpha`, `T15.Draft.mixedLebesgueENormT =
  T15.Spec.mixedLebesgueENormT`) — all `:= rfl`, all elaborate.
- **Both T15.Draft and T15.Spec blocks kept** (as draft A). The verbatim
  `T17.Spec.CorrectionAPI` block is written against `open T15.Spec`
  (`mixedLebesgueENormT`/`MemForceSobolevT`/`alphaT`) and the `abbrev PlacementData`
  shim; keeping both blocks + the shim is the mechanism that lets that verbatim
  block elaborate while `scaling`/`correction` share the single threaded
  `T15.Draft.PlacementData`. No math change.
- No other deviations. Parameters/fields/order/spellings/guards/intervals
  (`Ico` cross-transport, `Ioo` momentum, `periodicSet` support, `blowup_limsup`,
  `correction.energyConst`, registered `alpha`, `MemMixedLebesgueT`,
  `negative_s_memLp`, both `force_mem`+`forceDifference_mem`) all per §3.
  Dropped per §3: A's false `velocityDifference_support`, `breakdown`,
  `energyRateConst`(+guard), `reference` pins, `ε₀`-parameter, `localTheory`,
  `continuation`, `calculus`, the T12 block.

## 4. Commands run and results
- `grep -nE ': *True|:= *0$|→ *True' research/T18/Spec.lean` → empty (no stubs).
- `grep -nE 'sorry|admit|axiom|native_decide' research/T18/Spec.lean` → empty.
- `cd verification && lake env lean ../research/T18/Spec.lean` → **exit 0, 0 errors**
  (the ~45-field structure, the statement, and every `example … := rfl` drift
  check elaborate).
- Field count: 45 (44 ASCII + `ε₀`); 11 parameters.
