REJECT

## 1. What the lane claims

The worker is explicit that this is a partial delivery: `research/A01/REPORT_210.md:5-17`
says that the requested `horizon_lower_bound_H7` was not proved and instead claims a
uniform cylinder theorem under a time-supremum force bound. That claim is accurate.
The report also claims three budget/monotonicity lemmas, a more general coefficient
theorem, an exact H¹ obligation, an exact H⁷/L¹ obligation, and a zero-data instance
(`research/A01/REPORT_210.md:20-40`). All eight declarations exist with the reported
statements at `formalization/NSFormalization/Section4/A01/HorizonUniform.lean:23-39`,
`:42-77`, `:82-110`, `:114-139`, and `:143-153`.

The lane nevertheless does not meet its brief. The required theorem was a lower bound
for the physical, selected horizon (preferably lane 208's `localHorizon`) under physical
H⁷/L¹ bounds. The delivered principal theorem instead constructs a cylinder mild
solution under an H⁶ coefficient-path sup bound and makes no comparison with
`localHorizon`; its exact conclusion is at `HorizonUniform.lean:114-122`. This is a
useful lemma, but it is not the requested mathematics.

There is also one material false tree-status claim. `research/A01/REPORT_210.md:49-52`
and `research/A01/ATTEMPTS_HORIZON_UNIFORM.md:9-11` say that
`LocalSolution.lean`/`localHorizon` are absent. In this checkout,
`formalization/NSFormalization/Section4/A01/LocalSolution.lean:92-96` defines
`localHorizon`, `:99-104` proves its solution specification, and `:112-115` defines
`localSolution`. Commit `c85d133` (lane 208) is an ancestor of the lane tip, and the
file is already present in `HEAD^`. The narrower claim that no production theorem
named `constructor_of_base` exists is confirmed by a whole-Section4 search; the
relevant landed constructor is instead `solution_of_base` at `LocalSolution.lean:39-65`.

## 2. What is in Lean

### 2.1 Exact statements and quantifier order

`HorizonLowerBoundH1` is an unproved `Prop`, not a theorem. Its body at
`HorizonUniform.lean:23-29` is token-for-token the contract field at
`research/A01/Spec.lean:338-343`; the audit's `rfl` check is at
`research/A01/axioms_horizon_uniform.lean:20-29`. `HorizonLowerBoundH7L1` is likewise
honestly isolated as an unresolved `Prop` at `HorizonUniform.lean:31-39`. Neither
definition smuggles in a proof.

The quantifier order of both proved uniform statements is correct for what they say.
In `exists_uniform_H7_coefficient_horizon`, one `δ` is obtained from
`exists_positive_time_budget ν M L 1 S` before `C` and `a` are introduced
(`HorizonUniform.lean:82-96`). In `exists_uniform_H7_sup_force_horizon`, that theorem is
invoked before `F` and `a` are introduced (`HorizonUniform.lean:114-133`). Thus the
same `0 < δ ≤ S` works over the displayed coefficient/force and datum balls.

Both Picard budgets are genuinely used. `exists_positive_time_budget` returns the
ball and contraction inequalities at
`vendor/NavierStokesAndEuler/Euler/VolterraUniqueness.lean:68-92`. The delivered proof
transfers both into `hb'` and `hl'` at `HorizonUniform.lean:96`; `hb'` enters the
ball-invariance estimate `hbudget` at `:98-99`, while `hl'` is the final argument of
`exists_viscous_mild_solution` at `:100-106`. The vendor theorem separately requires
the ball estimate and contraction estimate at
`vendor/NavierStokesAndEuler/Euler/SobolevHeatVolterra.lean:63-77`.

The resulting object is a genuine quadratic mild solution on a nonempty interval:
`0 < δ` and `δ ≤ S` occur in the statement, the initial value is exactly `a`, and the
equation uses exactly `coefficients 1 (le_refl 6) F` at
`HorizonUniform.lean:116-122`. The coefficient definition really is projected force
minus advection, with zero linear part, at
`formalization/NSFormalization/Source/ForcedCylinderLocal.lean:51-58`. There is no
empty-interval trick and no `⊤.toReal = 0` use in these cylinder statements.

### 2.2 Radius monotonicity and the force bound

`picard_ballBound_mono` and `picard_ballLipschitz_mono` are genuine radius
monotonicity lemmas, not restatements: compare `HorizonUniform.lean:42-64` with the
definitions

```
ballBound R = ‖projection‖ * (‖forcing‖ + ‖linear‖ * R + ‖quadratic‖ * R^2)
ballLipschitz R = ‖projection‖ * (‖linear‖ + 2 * ‖quadratic‖ * R)
```

at `vendor/NavierStokesAndEuler/Euler/QuadraticCoefficients.lean:46-52`.

However, contrary to the route requested in the brief, neither radius-monotonicity
lemma is used in either uniform existence proof. The general proof assumes the two
bounds directly at radius `R+1` and uses only `picard_budget_mono`
(`HorizonUniform.lean:86-106`). The force specialization proves the ball-bound
inequality directly from `‖F‖ ≤ B`, and its Lipschitz bound is definitional equality
because forcing does not enter `ballLipschitz` (`HorizonUniform.lean:126-139`). The
datum hypothesis `‖a‖ ≤ R` supplies the one-unit ball margin. The theorem is valid,
but the report/brief must not say that the two radius-monotonicity lemmas are part of
this proof.

For negative `B`, the fiber `‖F‖ ≤ B` is empty, but this is not being used to mask the
meaningful case: `uniform_H7_zero` instantiates `B=R=0`, retains the actual nonlinear
coefficient bundle, and produces `0 < δ ≤ 1` at `HorizonUniform.lean:141-153`. The
audit also checks physical zero datum and force membership at
`axioms_horizon_uniform.lean:42-43`.

### 2.3 The selected horizon

The current `localHorizon` is exactly the selection problem identified by the worker,
but it is present. It is `Classical.choose (exists_localSolution ...)` at
`LocalSolution.lean:92-96`; its specification proves only positivity and existence at
the selected time (`LocalSolution.lean:99-104`). The witness made inside
`exists_positive_time_budget` is also an arbitrary neighborhood radius halved at
`VolterraUniqueness.lean:81-92`. No whole-tree declaration gives antitonicity of that
chosen witness in `M`, `L`, or the data bounds. `picard_budget_mono` only transfers
validity of one fixed time from larger coefficient bounds to smaller ones
(`HorizonUniform.lean:67-77`); it does not compare separately selected witnesses.

Therefore the proposed repair
`horizon ν a f := δ(ν, ‖a‖₇, ‖F‖sup)` is sound only if `δ` is defined by an explicit
positive Picard-time formula with proved antitonicity (or by another canonical/maximal
construction with the corresponding comparison theorem). Applying `Classical.choose`
to `exists_positive_time_budget` does not supply that fact. Lane 208's
`localHorizon` must be redefined or augmented; the current arbitrary existential
selection cannot support `δ(K) ≤ localHorizon ν a f`.

### 2.4 H¹, L¹ forcing, and the fixed-force re-cut

The worker's time-concentration sketch is decisive against the present vendor route.
The coefficient ball bound contains the continuous-path sup norm of the force
(`QuadraticCoefficients.lean:46-52` and `ForcedCylinderLocal.lean:51-58`), and local
existence uses both that bound and the Lipschitz bound
(`vendor/NavierStokesAndEuler/Euler/QuadraticHeatLocal.lean:31-53`). Smooth forces
`f_n(t,x)=n φ(nt)g(x)` can have a fixed L¹-in-time Sobolev norm but unbounded time sup,
arbitrarily close to time zero. Thus an H⁷/L¹ ball cannot provide the uniform `M` used
by this theorem. This does not disprove H⁷/L¹ local existence.

An L¹ same-order force estimate would repair the ball part by splitting the force
Duhamel term from the nonlinear Picard map and enlarging the radius by its integrated
H⁷ norm (and the projection norm). The tree contains the ordinary same-order Duhamel
integral at `vendor/NavierStokesAndEuler/Euler/DuhamelDifferentiation.lean:50-58` and
heat contraction at `vendor/NavierStokesAndEuler/Euler/SobolevHeat.lean:24-30`, but a
source-only `grep -rn` over the vendor and `Section4/A04` found no packaged theorem of
the form `‖∫ e^{(t-s)νΔ}F(s) ds‖ ≤ ∫ ‖F(s)‖ ds` and no forced Picard theorem assembled
around it. The many `sourceTime` hits are unrelated correction-source constructions.
One would also need the physical `forceSobolevENormL1 7` to canonical H⁷ path bridge.

HeliCorgi does not fill the H¹ gap. Its explicit lifespan theorem takes
`u0 : R3HsVelocity 3` and depends on `‖u0‖` at
`vendor/HeliCorgi/Formal/R3QuantitativeLifespan.lean:188-205`; the nonlinearity is the
unforced H³-to-H² map at
`vendor/HeliCorgi/Formal/R3ProjectedSobolevConvection.lean:10-18`. A whole-Section4
search found no forced H¹ local theory. The a-priori family starts with an already
existing interval, so using its high-order propagation to create that interval would
be circular. This agrees with the manuscript: Grönwall bounds every H^m only after a
solution exists up to `S` (`paper/sections/appendix-a-local-theory.tex:142-150`).

For a fixed `MemForceR` force, the order-6 coefficient path does have finite sup norm
on `[0,S+1]`: `C01.forcePath_jetLp_continuous` gives jet continuity at
`formalization/NSFormalization/Section4/C01/JetPaths.lean:92-110`, and `sobolevPath`
packages this as a continuous Sobolev path at
`vendor/NavierStokesAndEuler/Euler/SmoothFieldSobolevTime.lean:40-42`. Compactness then
gives a finite real norm; the analogous physical H¹ compact bound is already proved at
`formalization/NSFormalization/Section4/A04/Forcing.lean:151-173`.

The literal proposed re-cut

```
∀ ν > 0, ∀ f ∈ F_R, ∀ K ≠ ⊤, ∃ δ > 0,
  ∀ a ∈ initialClassR, sobolevENorm 7 a ≤ K → δ ≤ horizon ν a f
```

is enough for uniformity over initial data at time zero, but not by itself for the
current A04 restart. A04 restarts with `timeShift t₀ f` at
`formalization/NSFormalization/Section4/A04/Continuation.lean:101-109`. Applying the
displayed statement separately to every shifted force gives a possibly different
`δ(t₀)`. The restart consumes one `δ` before all restart times and, in its current API,
even before all forces (`A04/Continuation.lean:132-164`). The fixed-force strategy is
nevertheless viable if the re-cut is strengthened to one `δ` for all
`t₀ ∈ [0,S]` and all bounded restart data, or if the horizon is formulated with an
absolute start time. The finite sup norm on `[0,S+1]` then controls every shifted
window. In fact the cylinder-level theorem `forced_uniform_restart_time` already
chooses one window length uniformly over restart points for one force bundle at
`formalization/NSFormalization/Section4/A01/Continuation.lean:242-263`.

## 3. Gaps and required fixes

1. **Blocking — requested theorem absent.** The permitted probe
   `research/A01/probes/rev210_missing_goal.lean:1-4` checks the exact requested name
   and fails with the reproducing error:

   ```text
   ../research/A01/probes/rev210_missing_goal.lean:4:7: error(lean.unknownIdentifier): Unknown identifier `NSFormalization.Section4.A01.horizon_lower_bound_H7`
   ```

   Fix: prove the requested physical theorem against the selected horizon, or obtain
   owner authorization for a precise V2 re-cut. A cylinder existence theorem under a
   time-sup force hypothesis is not a replacement.

2. **Major — report/tree mismatch.** Correct `research/A01/REPORT_210.md:49-52` and
   `research/A01/ATTEMPTS_HORIZON_UNIFORM.md:9-11`: `LocalSolution.lean` and
   `localHorizon` are present. The actual issue is that `localHorizon` is an arbitrary
   existential choice and has no uniform lower-bound specification.

3. **Major — horizon selection.** Replace or augment lane 208's `localHorizon` using
   an explicit antitone Picard budget (or a canonical maximal admissible time), and
   prove its solution specification on exactly that time. No antitonicity theorem for
   the present `exists_positive_time_budget` witness exists in the tree.

4. **Major — A04-oriented re-cut.** If the owner chooses the fixed-force route, state
   uniformity over the compact family of restart times/time shifts, not only over data
   at time zero. Re-cut A04's current all-force `Restart` API accordingly. Use the
   compact order-6 force-path bound and the H⁷ datum-to-cylinder comparison; the
   relevant ingredients include `smoothL2_of_initialClassR`
   (`LocalSolution.lean:25-36`), `sobolevSpace_norm_le_sobolevENorm`
   (`formalization/NSFormalization/Section4/A01/AprioriRows.lean:287-294`), and
   `hword_jet_full` (`formalization/NSFormalization/Section4/A01/L2Descent.lean:200-205`).

5. **Note — monotonicity description.** Keep the two radius-monotonicity lemmas, but
   do not say they were used by the delivered uniform proof unless the proof is
   changed to invoke them.

The negative statement mutation is substantive and does not drop an argument.
`research/A01/probes/rev210_radius.lean:82-91` changes the promised solution radius
from `R+1` to `R-1`; the unchanged proof fails at `:107` because it only has
`‖u‖ ≤ R+1`, as expected. The exact control probe typechecks with zero output. The
zero-data theorem at `HorizonUniform.lean:143-153` supplies the requested non-vacuity
instance.

## 4. Commands and results

All Lean commands sourced `. scripts/lean-env.sh`; every Lake command ran from
`verification/` with `LEAN_NUM_THREADS=6`, one at a time. Full captures are under
`/tmp/rev210_*.log`. Only short exact head/tail excerpts are quoted here.

`lake build NSFormalization.Section4.A01.HorizonUniform` — exit 0, 82 lines / 4639
bytes. These are inherited replay warnings; there is no diagnostic from
`HorizonUniform.lean` itself.

```text
⚠ [8922/9655] Replayed NSFormalization.Source.FiniteHilbertBochner
warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
```

Last lines:

```text
warning: NSFormalization/Paper3/SobolevDirectionalDerivative.lean:103:16: `SchwartzMap.smul_apply` has been deprecated: Use `smul_apply` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.smul_apply` to `smul_apply x`).
Build completed successfully (9933 jobs).
```

`lake env lean ../formalization/NSFormalization/Section4/A01/HorizonUniform.lean` —
exit 0, exactly 0 lines / 0 bytes.

`lake env lean ../research/A01/axioms_horizon_uniform.lean` — exit 0. Whitespace-
normalized parsing finds exactly eight lists and every list is exactly
`[propext, Classical.choice, Quot.sound]`. Exact output:

```text
'NSFormalization.Section4.A01.HorizonLowerBoundH1' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.HorizonLowerBoundH7L1' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.picard_ballBound_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.picard_ballLipschitz_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.picard_budget_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.exists_uniform_H7_coefficient_horizon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.exists_uniform_H7_sup_force_horizon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.uniform_H7_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`make check` — exit 0, 28234 lines. First excerpt:

```text
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 30,
  "source_counts": {
    "formalization": 527,
    "vendor/NavierStokesAndEuler": 2486,
    "vendor/HeliCorgi": 129
  },
  "source_manifest_entries": 2975,
  "missing_copied_imports": [],
  "citation_interfaces_reachable": [],
```

Last excerpt:

```text
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.042s

OK
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.
```

The same successful check reports the pre-existing copied-source token and stale
source-hash status (`source_hashes_match: false`) near its beginning; neither is in the
lane module, and the checker exits successfully.

`lake test` — exit 0, 343 lines. Last excerpt:

```text
ℹ [10573/10573] Replayed Tests.EnergyAbsorptionV4
info: Tests/EnergyAbsorptionV4.lean:18:0: Contract BlowupDensity.Tests.checkedEnergyAbsorptionV4: checked; standard logical axioms only
info: Tests/EnergyAbsorptionV4.lean:19:0: Contract BlowupDensity.Bindings.energyAbsorptionPartialV3_of_v4: checked; standard logical axioms only
info: Tests/EnergyAbsorptionV4.lean:100:0: Contract BlowupDensity.Tests.energyAbsorptionV4_terminalFinite: checked; standard logical axioms only
```

`scripts/gates.sh NSFormalization.Section4.A01.HorizonUniform` — exit 0, 28359
lines. Last excerpt:

```text
== make test-mutations
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
== check_contracts
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
== gates OK
```

`python3 experiments/check_contracts.py --base-ref origin/erenup/integration` — exit
0, 28202 lines. Last excerpt:

```text
      "Tests.GradientL6V2"
    ]
  },
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
```

Control and mutation checks:

- `lake env lean ../research/A01/probes/rev210_control.lean` — exit 0, 0 output.
- `lake env lean ../research/A01/probes/rev210_radius.lean` — exit 1, with:

  ```text
  ../research/A01/probes/rev210_radius.lean:107:13: error: Application type mismatch: The argument
    hu
  has type
    ‖u‖ ≤ R + 1
  but is expected to have type
    ‖u‖ ≤ R - 1
  in the application
    And.intro hu
  ```

- `lake env lean ../research/A01/probes/rev210_missing_goal.lean` — exit 1, with the
  unknown-identifier error reproduced in part 3.

Hygiene commands found zero occurrences of
`sorry|admit|axiom|native_decide` and zero `maxHeartbeats` occurrences in the lane
module and audit. `git diff --name-only origin/erenup/integration...HEAD` prints
nothing because integration has advanced past this lane (`HEAD=06f9f33`, integration
`=ad8fc1f`, merge base `=06f9f33`). The lane-tip `git diff-tree` is therefore the
informative audit: it adds `HorizonUniform.lean`, modifies only `A3_SPLIT.md`, and adds
the attempts/report/axioms records; no existing Lean module or contract is modified.

Whole-tree/source-only gap searches used `grep -rn`, excluding build artifacts. These
exact searches produced no output:

```text
$ grep -rn --include='*.lean' -E '^(theorem|def) horizon_lower_bound_H7\b' formalization/NSFormalization/Section4
$ grep -rn --exclude-dir=.lake --include='*.lean' -Ei 'theorem .*([Dd]uhamel.*(L1|norm|bound)|L1.*[Dd]uhamel)' vendor/NavierStokesAndEuler formalization/NSFormalization/Section4/A04
$ grep -rn --include='*.lean' -Ei '^(theorem|def) .*([Ff]orced.*(H1|HOne|H¹).*(local|exist)|(local|exist).*[Ff]orced.*(H1|HOne|H¹))' formalization/NSFormalization/Section4
$ grep -rn --exclude-dir=.lake --include='*.lean' -Ei '^(theorem|def) .*(positive_time_budget|localHorizon).*(antitone|mono|decreasing)' vendor/NavierStokesAndEuler formalization/NSFormalization/Section4
$ grep -rn --include='*.lean' 'constructor_of_base' formalization/NSFormalization/Section4
```

The requested broad source search

```text
$ grep -rn --exclude-dir=.lake --include='*.lean' -E 'Duhamel|sourceTime|L1' vendor/NavierStokesAndEuler formalization/NSFormalization/Section4/A04 | wc -l
549
```

contains no packaged L¹ Duhamel bound. Its `sourceTime` declaration hits are unrelated:

```text
vendor/NavierStokesAndEuler/Euler/CorrectionEnergyRestriction.lean:38:theorem sourceTime_restriction {q : ℕ} (hq : 6 ≤ q) (T : ℝ) (hT : 0 ≤ T)
vendor/NavierStokesAndEuler/Euler/CorrectionEnergyTime.lean:54:def sourceTime {q : ℕ} (hq : 6 ≤ q+1) (T : ℝ) (hT : 0 ≤ T)
vendor/NavierStokesAndEuler/Euler/PacketSourcePiola.lean:26:def sourceTime (t : Icc (0 : ℝ) M.T) : Icc (0 : ℝ) D.T :=
vendor/NavierStokesAndEuler/Euler/PacketSourceScaleSequence.lean:159:theorem sourceTimeWidth_eq (J : ℕ) (X : ℝ) (n : ℕ) :
vendor/NavierStokesAndEuler/Euler/PacketSourceScaleSequence.lean:172:theorem sourceTimeWidth_le (J : ℕ) (hJ : 1 ≤ J) (X : ℝ) (hX : 0 < X)
vendor/NavierStokesAndEuler/Euler/HeatMaximalCauchy.lean:66:def sourceTime (T : ℝ) (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T, SobolevSpace period 1)) :
vendor/NavierStokesAndEuler/Euler/HeatMaximalCauchy.lean:82:theorem sourceTime_sub (T : ℝ) (hT : 0 ≤ T) (f g : C(Icc (0 : ℝ) T, SobolevSpace period 1)) :
vendor/NavierStokesAndEuler/Euler/PacketSourceScaleBounds.lean:132:theorem sourceTimeRatio_bound (J : ℕ) (hJ : 1 ≤ J) (x : ℕ → ℝ) (n : ℕ) :
```

Conversely, the search that refutes the report's absence claim begins:

```text
formalization/NSFormalization/Section4/A01/LocalSolution.lean:92:def localHorizon (ν : ℝ) (a : A02.SpatialField) (f : A02.SpaceTimeField) : ℝ := by
formalization/NSFormalization/Section4/A01/LocalSolution.lean:99:theorem localHorizon_spec {ν : ℝ} {a : A02.SpatialField} {f : A02.SpaceTimeField}
formalization/NSFormalization/Section4/A01/LocalSolution.lean:107:theorem localHorizon_pos {ν : ℝ} {a : A02.SpatialField} {f : A02.SpaceTimeField}
```

For the lead, the shortest honest path is an owner-authorized V2 fixed-force,
compact-restart-time re-cut at H⁷/cylinder order, using
`forcePath_jetLp_continuous` + `sobolevPath` for one finite H⁶ sup bound,
`sobolevSpace_norm_le_sobolevENorm` + `hword_jet_full` for the datum ball,
`exists_uniform_H7_sup_force_horizon` (or the already restart-shaped
`forced_uniform_restart_time`) for one window, and `solution_of_base` for the physical
solution. The field must quantify one `δ` over all `t₀ ∈ [0,S]` and the shifted force
windows; the literal fixed-force/time-zero formula is too weak for current A04.
Finally, lane 208's `localHorizon` must be redefined through an explicit antitone
budget (or another canonical comparable selection). Keeping the original H¹/L¹ field
instead requires genuinely new forced H¹ local theory; keeping H⁷/L¹ requires the new
same-order force-Duhamel estimate and Picard assembly described above.
