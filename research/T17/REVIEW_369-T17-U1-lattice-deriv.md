REJECT

## What the lane claims

The worker report says that it proved the local, zero-copy derivative equality and an `ℝ≥0∞` supremum bound (`research/T17/REPORT_369.md:3-5`). It explicitly acknowledges that the general existential `k` packaging was not included (`research/T17/REPORT_369.md:5`), and the attempts note repeats that this is future work (`research/T17/ATTEMPTS_U1.md:3`). The paper's correction lemma itself quantifies its derivative bounds globally in the spacetime variables and for every derivative order (`paper/sections/03-torus.tex:218-243`). The lane status therefore accurately describes a partial delivery, but that partial delivery does not satisfy U1's stated target: every `z`, a nearby lattice copy `k`, the shifted right-hand side, and the `k = 0` fundamental-ball form (`research/T17/T17_SPLIT.md:64-70`).

## What is in Lean

`latticeLift_iteratedFDeriv_eq` has exactly the local statement shown in the file: `hslice`, `r + ρ ≤ 1`, a point `x ∈ ball x₀ r`, arbitrary order `n` and tuple `u`, followed by equality with the unshifted `w` (`formalization/NSFormalization/Section3/T17/LatticeDeriv.lean:9-15`). Its proof obtains an actual neighborhood from the open ball, applies T16's local equality, and uses eventual derivative congruence on `univ` (`formalization/NSFormalization/Section3/T17/LatticeDeriv.lean:16-24`). This is faithful to T16's cited locality lemma, whose hypotheses and conclusion are precisely `r + ρ ≤ 1`, `x ∈ ball x₀ r`, and `latticeLift w (t,x) = w (t,x)` (`formalization/NSFormalization/Section3/T16/LatticeLift.lean:139-166`), and to the vendor's neighborhood fact (`vendor/NavierStokesAndEuler/NavierStokes/PeriodicLocalization.lean:250-258`).

The second theorem is only the corresponding pointwise-directional bound on the same ball; it retains `x ∈ ball x₀ r` and `u : Fin n → Space` and takes an `iSup` over the unshifted `w` evaluated at `(t,x)` (`formalization/NSFormalization/Section3/T17/LatticeDeriv.lean:25-33`). The supplied lane probe merely re-applies that theorem abstractly (`research/T17/probes/lattice_deriv_closes.lean:6-10`); it is not a nonzero instance. I added and checked a nonzero `ContDiffBump` instance at the origin in `research/T17/probes/rev369_nonvacuity.lean:11-47`.

## Gaps

1. **Blocking (missing required theorem):** There is no theorem packaging the requested `∃ k` for an arbitrary spacetime point, no `(0, latticeVector k)` shift on the right-hand side, and no no-nearby-copy/zero case. The only exported equality is the `k = 0` ball restriction (`formalization/NSFormalization/Section3/T17/LatticeDeriv.lean:9-24`), whereas the U1 target explicitly requires the existential and then the local `k = 0` specialization (`research/T17/T17_SPLIT.md:64-70`). This is why the lane cannot be accepted despite the local proof being valid.

2. **Blocking (corollary scope/shape):** The delivered `iSup` corollary is likewise restricted to the fundamental ball and to a fixed directional tuple `u` (`formalization/NSFormalization/Section3/T17/LatticeDeriv.lean:25-33`). It does not provide the requested all-`z` nearby-copy corollary, nor the operator-norm spelling suggested by the brief's `‖iteratedFDeriv ... z‖` formulation. It must be extended together with the existential theorem, with the `ℝ≥0∞` coercion and `⨆` retained.

3. **Missing review evidence in the lane records:** `REPORT_369.md` only says that validation was run and does not give command output (`research/T17/REPORT_369.md:7`); the lane probe also has no non-vacuity witness (`research/T17/probes/lattice_deriv_closes.lean:6-10`). The reviewer non-vacuity probe succeeds, but it should be incorporated into the lane's own probe/report when the missing general theorem is fixed.

The statement that is present does not add a smoothness assumption, but that is harmless here: eventual equality of functions gives equality of the iterated derivatives without requiring smoothness, and the support/ball hypotheses are the same as T16's non-vacuous locality lemma (`formalization/NSFormalization/Section3/T16/LatticeLift.lean:139-142`). No `sorry`, `admit`, `axiom`, `native_decide`, or `maxHeartbeats` occurs in the lane deliverables. A whole-Section4 grep for the missing bridge names returned no matches (`grep_rc=1`, zero bytes), so there is no existing Section4 theorem that was overlooked.

## Commands and results

All commands were run after `. scripts/lean-env.sh`, with `LEAN_NUM_THREADS=6`, and `lake` from `verification/`.

* `lake build NSFormalization.Section3.T17.LatticeDeriv`: exit 0. The module itself is silent; the cached closure replayed pre-existing warnings, ending with the exact line `Build completed successfully (9359 jobs).`
* `lake env lean ../formalization/NSFormalization/Section3/T17/LatticeDeriv.lean`: exit 0, zero output.
* `lake env lean ../research/T17/probes/lattice_deriv_closes.lean`: exit 0, zero output.
* `lake env lean ../research/T17/axioms_u1.lean`: exit 0, exact output:

  ```text
  'NSFormalization.Section3.T17.latticeLift_iteratedFDeriv_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
  'NSFormalization.Section3.T17.latticeLift_iteratedFDeriv_norm_le_iSup' depends on axioms: [propext,
   Classical.choice,
   Quot.sound]
  ```

* `make check`: exit 0. Its exact architecture summary included `"source_hashes_match": false`, then `Explicit axiom/admission tokens, all copied sources: 11`; the contract policy test printed 13 dots and `OK`, and the final line was `45 work items: ownership, contract registration and task cards consistent.` These are repository-wide baseline diagnostics; the lane files themselves have no forbidden-token matches.
* Non-vacuity probe `lake env lean ../research/T17/probes/rev369_nonvacuity.lean`: exit 0, zero output.
* Substantive negative mutation (widening `r + ρ ≤ 1` to `r + ρ ≤ 2`) in `research/T17/probes/rev369_negative_widened_ball.lean`: exit 1 with the expected error:

  ```text
  ../research/T17/probes/rev369_negative_widened_ball.lean:13:41: error: Application type mismatch: The argument
    hr
  has type
    r + ρ ≤ 2
  but is expected to have type
    r + ρ ≤ 1
  in the application
    @latticeLift_iteratedFDeriv_eq w x₀ ρ r hs hr
  ```

  `verification/` was not touched, so the conditional `scripts/gates.sh` and `check_contracts.py --base-ref origin/erenup/integration-section3` gate was not applicable. `git diff --check` was clean; the branch diff contains only the new T17 module/records plus the lane's status note, while the reviewer probes/report are untracked working-tree additions.

Verdict: REJECT

Fixes required:

1. Add the arbitrary-`z` nearby-copy theorem with `∃ k`, the shifted derivative equality, and the zero/no-copy case.
2. Extend the `ℝ≥0∞` `⨆` corollary to that general statement (and match the intended operator/directional norm spelling).
3. Update the lane probe/report with the nonzero bump instance, exact gate output, and a recorded substantive negative mutation.

---

## Fix note (lane 369 r1, 2026-09-18)

All three required fixes are delivered in `Section3/T17/LatticeDeriv.lean` (module
builds, 0 errors; four declarations `[propext, Classical.choice, Quot.sound]`):

1. **Arbitrary-`z` `∃ k` theorem, shifted RHS, zero case.** New
   `latticeLift_iteratedFDeriv_eq_shift`: for every `z`, `∃ k`,
   `‖iteratedFDeriv ℝ n (latticeLift w) z u‖ = ‖iteratedFDeriv ℝ n w (z - (0, latticeVector k)) u‖`;
   copy present → the shift `k`; no copy → `k = 0`, both sides `0`.  Proof:
   `isPeriodicOn_sub_latticeVector` + `latticeLift_eq_of_ball` for a single-translate
   neighbourhood, `Filter.EventuallyEq.iteratedFDeriv`, `iteratedFDeriv_comp_sub`;
   the zero case is a `ball z.2 (r-ρ)` of vanishing lattice terms.  One added honest
   hypothesis `hlt : ρ < r` (strict separation; downstream `ε·θRadius < r`).
2. **General `ℝ≥0∞`/`⨆` corollary.** New `latticeLift_iteratedFDeriv_norm_le_iSup'`,
   all-`z`, same `ENNReal.ofReal … ≤ ⨆ z', ENNReal.ofReal …` spelling as the
   existing ball corollary and matching `CorrectionAPI.correction_derivative_bound`
   (arbitrary `u : Fin n → SpaceTime` subsumes its `Fin.append` tuple).
3. **Lane probe/report/negative evidence.** `research/T17/probes/lattice_deriv_closes.lean`
   is now a concrete non-vacuous instance on the reviewer bump: `∃ k` exercised
   off-cube at `z = (0, latticeVector k₁)` (`k₁ = (1,0,0)`), with
   `lift_nonzero_offcube` proving the lift is genuinely nonzero there; the `⨆`
   corollary and the `k = 0` form also close.  New negative probe
   `rev369r1_negative_lt.lean` (exit 1) shows `hlt : ρ < r` is load-bearing.
   `ATTEMPTS_U1.md` / `REPORT_369.md` record the exact gate output.

Note on the two existing declarations: `latticeLift_iteratedFDeriv_eq` and
`latticeLift_iteratedFDeriv_norm_le_iSup` are kept **verbatim** (they are the
`k = 0` fundamental-ball specialization, and the reviewer probes
`rev369_nonvacuity.lean` / `rev369_negative_widened_ball.lean` reference them), so
the general result is added as the new siblings above rather than by restating the
existing names.

Gates re-run: `lake build NSFormalization.Section3.T17.LatticeDeriv` (exit 0);
`lake env lean` on module / `lattice_deriv_closes.lean` / `axioms_u1.lean` (exit 0);
`rev369_negative_widened_ball.lean` and `rev369r1_negative_lt.lean` (exit 1 as
designed); `rev369_nonvacuity.lean` (exit 0); `make check` (exit 0).
