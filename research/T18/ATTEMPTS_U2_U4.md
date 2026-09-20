# T18 U2/U3/U4 attempts — lane 426

## Successful routes

- The canonical correction kinematic fields are on `data.correction.potential`,
  the threaded T16 `LocalPotentialAPI`, rather than directly on `CorrectionAPI`.
- U2: `MemForceT` is closed under addition using `tsupport_add` and a union of
  the compact time witnesses. The correction uses the closed interval
  `[T - 2ε², T + 2ε²]`; `place.eps_time` makes its lower endpoint positive.
  The open support bound implies this closed compact bound. Add the packet
  force and then the reference force. Pointwise abelian-group cancellation
  identifies the actual force difference with the correction plus packet.
- U3 velocity smoothness and periodicity restrict the reference from
  `[0,T+δ)` to `[0,T)`, and add the correction and pinned scaling solution.
- The scaling solution pins its pressure to `normalizedScaledPressure`, not
  the raw pressure. Consequently no raw spacetime pressure regularity lemma
  is needed. Reference pressure slices are integrable: complexify the smooth
  real slice, apply `Paper1.memLp_torusLift`, take `.re`, then `.integrable`.
  `scaling.pressureSlice_integrable` provides the other integrability premise.
  `integral_add` and the reference's pressure gauge show that inserted pressure
  equals reference pressure plus normalized packet pressure on the slab.
- History uses `image_eq_zero_of_notMem_tsupport` for the correction, and the
  explicit `zeroPastField` conditional for the packet. The latter vanishes
  whenever `t ≤ T - 2ε²` without any packet hypotheses or scale positivity.
  Initial value follows from history and `place.eps_time`.
- U4 spatial slicing uses `ContDiffOn.comp_contDiff`, so the time endpoint
  `t=0` is covered. T16 divergence additivity combines all three summands.
  Apply the same addition lemma to `(u-v)+v=u` for the difference field.

## Resolved elaboration errors

- `Tactic rewrite failed: Did not find an occurrence of the pattern ...` in
  periodicity of a sum: beta-reduce the lambda with `dsimp only` before `rw`.
- `dsimp made no progress` on a real interval: use `change 0 < t` and `linarith`.
- `This extensionality tactic only applies to equalities, not ... ↔ ...`:
  prove the difference-field function equality first, then rewrite membership.
- `expected token` at the infinity smoothness notation after the ForcePaths
  import: explicitly `open scoped ContDiff`.
- `Application type mismatch ... Continuous ...` for `memLp_torusLift`:
  that helper is complex-valued; use complexification and `.re` as above.
- `Unknown identifier tsum_eq_zero`: simplify the unfolded sum with the
  nonpositive-source-time fact, `ite_false`, `smul_zero`, and `tsum_zero`.
  The attempted `ite_eq_right (not_lt.mpr hnonpos)` was not the correct
  conditional simplification; separating unfolding from simplification works.
- `Application type mismatch ... DifferentiableAt.sub hu hv`: specify the
  spacetime function arguments `u` and `v` to divergence additivity explicitly.
- Probe `IsPeriodicOn` unknown: open the registered `TorusData` namespace.
- Probe force membership `Type mismatch: After simplification`: unfold the
  U1 constructor and fieldwise adapters before applying the force-class bridge.

## Residual obligations

None for U2/U3/U4. No named input, extra hypothesis, admission, or heartbeat
option was added. As in U1, these are assembly theorems conditional on the
threaded scaling/correction records; constructing those records belongs to
T15/T17, not these units. Existing Lean modules were not changed. The only
existing file changed is the explicitly requested U2/U3/U4 status ledger.
