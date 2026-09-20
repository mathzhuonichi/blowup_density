ACCEPT-WITH-NOTES

## 1. What the lane claims

The report claims five audited declarations: the unrestricted and `Inv` all-order cylinder
theorems, the unrestricted and `Inv` combined constructor exports, and a genuine zero-data
producer of the all-order bound (`research/A01/REPORT_192.md:9-89`). All five exist with the
reported statements:

- `cylinderPair_of_bounds` has one `U`, `U 0 = a.toLp`, and for every `q ≥ 6` one `u` carrying
  `hU`, `hdiv`, angle invariance, and the canonical order-`q` Duhamel equation, followed by the
  all-`j`, all-`m` datum family (`formalization/NSFormalization/Section4/A01/CylinderWiring.lean:36-57`).
- `cylinderPair_of_boundsInv` has the identical conclusion with `HasAprioriBoundInv`
  (`formalization/NSFormalization/Section4/A01/CylinderWiring.lean:86-107`).
- `constructorInputs_of_bounds` puts `U`, the order-`q` `u`, `U 0`, `hU`, `hdiv`, angle
  invariance, exact Duhamel, the derived `j = 0` family, and the full all-`j,m` family under one
  existential (`formalization/NSFormalization/Section4/A01/CylinderWiring.lean:139-164`).
  `constructorInputs_of_boundsInv` has the same shape (`CylinderWiring.lean:167-192`).
- `zero_all_order_bound` really proves radius-zero `HasAprioriBound` for zero datum and zero force
  (`research/A01/axioms_wiring_hsob.lean:61-87`), and the main theorem is instantiated from it
  without an assumed `hb` (`research/A01/axioms_wiring_hsob.lean:89-109`).

This is the mathematics asked for. The paper requires higher-order bounds on one common local
interval and then all `C^j_t H^k_x` regularity on that interval
(`paper/sections/appendix-a-local-theory.tex:65-75`). The two main theorems expose exactly one
ordinary carrier for all orders, while the fixed-order exports retain every constructor clause on
the same `U,u`. The Duhamel term agrees token-for-token in its meaningful arguments with
`localTheory_on_prescribed_horizon`: viscosity `ν`, proofs `hν`, `hS.le`, `le_rfl`,
`coefficients 1 hq (sobolevPath F hF q)`, canonical
`ordinarySobolev (q+1) a.toLp a.translation_contDiff`, and the same recursive path `u`
(`formalization/NSFormalization/Section4/A01/Horizon.lean:137-154`).

## 2. What is in Lean

The proof preserves witness identity rather than merely reproducing compatible types.
`compatible_carriers_of_bounds'` returns the one `U`, every-order `u`, angle invariance, and
Duhamel (`formalization/NSFormalization/Section4/A01/MildUniqueness.lean:212-230`). The lane uses
that call once (`CylinderWiring.lean:58-65`), constructs `hall` from those same witnesses
(`CylinderWiring.lean:66-79`), obtains the all-order paths for that same `U`
(`CylinderWiring.lean:80`), and adds divergence-freeness from the same Duhamel proof
(`CylinderWiring.lean:81-83`). The `Inv` proof repeats this exact route
(`CylinderWiring.lean:108-133`). The two combined exports destructure their respective main
theorem once and return `hsob 0` plus `hsob`, so the `j=0` field is genuinely a projection of the
full family (`CylinderWiring.lean:162-164,190-192`).

The cited supply lemmas match their uses: canonical force smoothness follows from `MemForceR`
(`formalization/NSFormalization/Section4/A01/ForcePathSmooth.lean:228-245`); the datum bootstrap
requires precisely the same-carrier `hU`, angular invariance, Duhamel, and smooth force path
(`formalization/NSFormalization/Section4/A01/DatumPathSmooth.lean:710-734`); and
`forced_mild_divergenceFree` consumes the exact Duhamel equation and `ha`
(`formalization/NSFormalization/Section4/A01/Continuation.lean:115-140`).

There is no hidden `ENNReal.toReal = 0` escape or empty-interval trick. `hS : 0 < S` makes the
export interval nonempty. `HasAprioriBound` fixes `R` before `T` and the mild solution, and its
conclusion is a direct real norm bound (`formalization/NSFormalization/Section4/A01/Horizon.lean:97-114`).
The named analytic hypotheses are used and isolated: `hf` supplies the force and its smoothness,
`hν` and `hb` supply the compatible mild paths, and `ha` supplies divergence-freeness.

The zero producer is genuine. For `T > 0` it applies `quadratic_mild_unique`; this is exactly the
primitive used in the body of lane 188's `mildUniqueness`
(`formalization/NSFormalization/Section4/A01/MildUniqueness.lean:185-188`). It treats `T = 0`
directly, proves `u = 0`, and concludes `‖u‖ ≤ 0`
(`research/A01/axioms_wiring_hsob.lean:67-85`). Thus the lead's uniqueness and non-vacuity check
is satisfied even though the proof invokes the primitive directly rather than the one-line named
wrapper.

`rev192_combined_full_fail.lean` now passes for both unrestricted and `Inv` exports with the full
same-witness statement (`research/A01/probes/rev192_combined_full_fail.lean:19-75`).
`rev192_named_exports_fail.lean` still fails because the unsafe split declarations are absent
(`research/A01/probes/rev192_named_exports_fail.lean:19-40`). The positive constructor probe
destructures and consumes every output, including `hinv`, `hduh`, `hsob`, and `hpaths`
(`research/A01/probes/rev192_constructor_positive.lean:88-92`). Its locally copied `joint190`
type is exactly the merged theorem's type
(`origin/erenup/integration:formalization/NSFormalization/Section4/A01/JointRepresentative.lean:552-562`),
but the probe does not yet import that module for real. This is explicitly nonblocking under the
lead's checkpoint.

Hygiene is clean. The only production Lean diff is the new 194-line
`CylinderWiring.lean`; no pre-existing Lean module is modified. The changed Lean/audit/probe files
contain no `sorry`, `admit`, declaration `axiom`, `native_decide`, or `maxHeartbeats`. The five
`#print axioms` commands are at `research/A01/axioms_wiring_hsob.lean:27-30,87`, and every result
is exactly `[propext, Classical.choice, Quot.sound]`.

## 3. Gaps

There is no blocking gap in lane 192. The full-tree search for the report's remaining analytic
input found no production theorem constructing an all-order `HasAprioriBound` family. The matches
under `formalization/NSFormalization/Section4` are definitions or consumers in `Horizon.lean`,
`AprioriInvariance.lean`, `CommonHorizon.lean`, `MildUniqueness.lean`, `SliceWiring.lean`, and this
new module; no theorem concludes `∀ q ≥ 6, HasAprioriBound ...`. The report's non-circular route
is honest: it fixes the order-six radius first, lowers higher-order solutions to order six, uses
uniqueness, obtains the order-two integral cap from that fixed base radius, and only then chooses
higher-order radii (`research/A01/ATTEMPTS_WIRING_HSOB.md:70-92`). It explicitly rejects routing
through this theorem, which would already assume `hb`.

Lane 190 is now present on current integration as `exists_joint_smooth_representative`
(`JointRepresentative.lean:552-562` above), although this worktree is behind integration and does
not contain the file. The pressure-gradient regularity input remains absent: the tree only proves
results conditional on joint/slice smoothness and symmetry
(`formalization/NSFormalization/Section4/A01/ConstructorPressure.lean:70-217`), not a producer of
the constructor's `hpg` package.

Nonblocking exact fix: after updating this branch onto current integration, add
`import NSFormalization.Section4.A01.JointRepresentative` to `rev192_constructor_positive.lean`
and replace the `joint190` parameter call by
`exists_joint_smooth_representative hS U hpaths`.

## 4. Commands and results

All Lean commands sourced `scripts/lean-env.sh`; every Lake command ran from `verification/` with
`LEAN_NUM_THREADS=6`.

1. `lake build NSFormalization.Section4.A01.CylinderWiring` — exit 0. The exact capture is
   `/tmp/rev192_build.out` (205 lines, 11970 bytes,
   SHA-256 `6bd7fade47711f496f030531b1c24374c519508e5d4d4a981f4f522be80ea9a6`). It contains only
   replayed warnings from pre-existing dependencies and ends exactly with:

   ```text
   Build completed successfully (10246 jobs).
   ```

   There is no `CylinderWiring` warning or diagnostic, so the target module itself is silent.

2. `lake env lean ../formalization/NSFormalization/Section4/A01/CylinderWiring.lean` — exit 0,
   exact output: empty.

3. `lake env lean ../research/A01/axioms_wiring_hsob.lean` — exit 0, exact output:

   ```text
   'NSFormalization.Section4.A01.cylinderPair_of_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section4.A01.cylinderPair_of_boundsInv' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section4.A01.constructorInputs_of_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section4.A01.constructorInputs_of_boundsInv' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section4.A01.zero_all_order_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

4. The following all exited 0 with exact output empty:

   ```text
   lake env lean ../research/A01/probes/rev192_constructor_positive.lean
   lake env lean ../research/A01/probes/rev192_combined_full_fail.lean
   lake env lean ../research/A01/probes/rev192_zero_nonvacuity.lean
   ```

5. `lake env lean ../research/A01/probes/rev192_named_exports_fail.lean` — expected exit 1,
   exact output:

   ```text
   ../research/A01/probes/rev192_named_exports_fail.lean:38:33: error(lean.unknownIdentifier): Unknown identifier `hsob_of_bounds`
   ../research/A01/probes/rev192_named_exports_fail.lean:38:9: error: Tactic `rcases` failed: `x✝ : ?m.104` is not an inductive datatype
   ```

6. `lake env lean ../research/A01/probes/rev192_mutation_fail.lean` — expected exit 1. This
   substantively changes the cylinder order `q+1` to `q+2`, rather than dropping an argument
   (`research/A01/probes/rev192_mutation_fail.lean:18-39`). Exact output:

   ```text
   ../research/A01/probes/rev192_mutation_fail.lean:39:9: error: Application type mismatch: The argument
     u
   has type
     C(↑(Icc 0 S), { x : SobolevWord (q + 1) → ↥(LiftL2 1) // x ∈ SobolevSpace 1 (q + 1) })
   but is expected to have type
     C(↑(Icc 0 S), { x : SobolevWord (q + 2) → ↥(LiftL2 1) // x ∈ SobolevSpace 1 (q + 2) })
   in the application
     Exists.intro u
   ```

7. `make check` — exit 0. Full stdout was captured exactly at
   `/tmp/rev192_make_check.out` (28229 lines, 1159494 bytes,
   SHA-256 `0fb3597fd250970087d6f1f73ef53caa5ad4f2fce2eca736e31b1847cf275800`). Its stderr and final
   stdout are exactly:

   ```text
   .............
   ----------------------------------------------------------------------
   Ran 13 tests in 0.045s

   OK
   python3 experiments/test_contract_policy.py
   python3 experiments/check_work_queue.py
   30 work items: ownership, contract registration and task cards consistent.
   ```

8. `git diff --check origin/erenup/integration...HEAD` — exit 0, exact output: empty.
   The changed-path audit reports one new production module, research records, and probes only;
   no path under `verification/` is touched. Therefore the brief's conditional
   `scripts/gates.sh` and `check_contracts.py --base-ref origin/erenup/integration` gates are not
   applicable (ordinary `check_contracts.py` nevertheless ran successfully inside `make check`).
