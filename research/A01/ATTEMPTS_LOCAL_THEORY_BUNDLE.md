# Lane 211 — local theory bundle

## Successful construction

- `LocalCarrier` retains the smooth datum and its identification/divergence,
  `U` and its initial value, full lane-192 `hpairs` and `hpaths`, the smooth
  velocity and slice identity, pressure supply `G/hG_int/hG`, and the actual
  classical solution with velocity and initial-datum equalities.
- `localCarrier_of_base` repeats the witness-preserving composition of lane
  208's `solution_of_base`; it uses the exported `hb_of_base''`. The brief's
  `constructor_of_base` is a research-probe theorem, not a TameAssembly export.
- The uniform horizon is half the supremum of the times in `[0,1]` satisfying
  both strict Picard inequalities from lane 210. The vendor positive-budget
  theorem makes the supremum positive. A larger admissible time exists above
  its half; time monotonicity transfers both strict budgets to the half.
  Inclusion of budget sets proves antitonicity in both coefficient bounds.
- `uniformHorizon` uses precisely lane 210's sup-force ball and Lipschitz
  budgets. `uniformHorizon_mild` replays its Picard proof at this specified
  time, rather than choosing the existential theorem's arbitrary witness.
- `referenceForce` is the continuous H⁶ path supplied by continuous force
  jets on compact `[0,1]`. Its continuous-map norm bounds every slice and is
  a finite real number. The selected datum's actual cylinder H⁷ norm and
  this force norm determine `localHorizon'`.
- The fixed-force physical H⁷ estimate uses the correct datum-to-cylinder
  direction: `ordinarySobolev_norm_le_tensor`, equality of the smooth jets
  with `D01.jetOfDatum`, and `norm_jetOfDatum_le`. The explicit comparison
  constant is `sum (j in range 8) (jetDatumConst j 7)`.
- `localTheoryData` contains the shared horizon, chosen solution, manuscript
  regularity of that solution, and the fixed-force H⁷ bound.

## Rejected routes and elaboration repairs

- Choosing lane 210's existential horizon independently for every radius
  gives no antitonicity. Taking a minimum with lane 208's arbitrary horizon
  would lose the proved lower bound. Neither route is used.
- The `16^m`/`4^m` datum estimates and `OrderTwoCap` control the physical
  datum by cylinder words, the opposite direction to the radius bound needed
  here. The existing datum-to-jets comparison supplies the required direction.
- `HorizonLowerBoundH1` already exists in the imported lane-210 namespace;
  redeclaring that exact name would conflict. Its original field remains
  unchanged and unasserted. `ManuscriptHorizonLowerBoundH1` specializes it to
  the new horizon and carries the requested open-obligation documentation.
- Nested continuous-linear-map norms need the same explicit local
  `SeminormedAddCommGroup` instances as lane 210. Unqualified metavariable
  `norm_nonneg _` did not infer continuous-map norms; specifying the
  projection/quadratic object resolved the elaboration failure.
- Rewriting `sobolevENorm 7` with a datum at `(7 : Nat)` needs a typed
  intermediate equality. The norm conversion is generic `toReal_enorm`,
  not the real-scalar specialization `Real.enorm_eq_ofReal`.

## Repository state

The worktree initially contained an unfinished merge and staged lane-208/209
files. The worker did not resolve, complete, abort or commit that merge.
External coordination completed it as `9e0c8c6` during the work. Lane 211
changes are isolated from that pre-existing state. No contract, binding,
test registry, existing Lean module, merge, rebase or push was changed/run
by this worker.
