ACCEPT-WITH-NOTES

# 1. What the lane claims

The lane claims a continuous linear reconstruction

```lean
datumSobolevCLM q : RealVectorSobolev (q : ℝ) →L[ℝ] SobolevSpace 1 q
```

which agrees with the vendor's exact cylinder carrier on every datum representing a smooth
physical field, and uses it to prove the canonical force-side `hfs` input for every `q` (hence in
particular every `q ≥ 6`).  It also extends the lane-167 force package by this input.  These
declarations exist with the statements printed in the worker report at
`formalization/NSFormalization/Section4/A01/ForcePathSmooth.lean:213-224`, `:232-245`, and
`:252-266`.  The statements in `research/A01/REPORT_187.md:5-41` match them.

The mathematics matches the requested bridge.  The paper defines
`f ∈ C∞([0,∞);H∞)` with every integer-order `L¹_t H^m_x` and `L²_t H^m_x` norm finite at
`paper/sections/02-preliminaries.tex:17-25`; it explicitly explains repeated time differentiation
and one-sided initial regularity at `paper/sections/appendix-a-local-theory.tex:71-76`.
`D01.MemForceR` represents precisely this supply by an order-`m` datum path smooth on
`futureTimes = Ici 0` at `formalization/NSFormalization/Section4/D01/ForceClass.lean:141-164`.

There is no vacuity:

- `hS : 0 < S` makes `Icc 0 S` nonempty and is used both in `extendPath` and
  `projIcc_of_mem` (`ForcePathSmooth.lean:232-245`).
- `hf` and `q` are used.  The package's `_hq` is intentionally unnecessary because the proved
  result is stronger; `_hF` is a proof argument only, and proof irrelevance makes the resulting
  `sobolevPath` independent of it (`ForcePathSmooth.lean:247-266`).
- No `ENNReal.toReal`, empty-interval trick, or silently strengthened hypothesis appears.
- The zero-force check has a positive, inhabited horizon at
  `research/A01/axioms_hfs.lean:30-56`.  The additional reviewer check
  `research/A01/probes/rev187_lane186_consumer.lean:58-60` proves both
  `D01.MemForceR (0 : A02.SpaceTimeField)` and `Nonempty (Icc (0 : ℝ) 1)`.

# 2. What is in Lean

## Reconstruction and agreement

The map is genuinely defined on **all** of `RealVectorSobolev (q : ℝ)`, not merely on data
coming from smooth fields:

- `jetOfDatumCLM` bundles `D01.jetOfDatum` by `LinearMap.mkContinuous`, using the explicit bound
  `D01.norm_jetOfDatum_le` and constant `D01.jetDatumConst` at
  `ForcePathSmooth.lean:35-65`.  The bound itself is
  `‖jetOfDatum m j hj A‖ ≤ jetDatumConst j m * ‖A‖` at
  `formalization/NSFormalization/Section4/D01/DatumToJets.lean:218-234`.
- The remaining steps are continuous linear maps: multilinear evaluation and `ordinaryLift`
  (`ForcePathSmooth.lean:75-81`), followed by the finite product CLM
  (`ForcePathSmooth.lean:85-87`).
- Schwartz data are dense (`ForcePathSmooth.lean:122-160`).  They represent the explicit smooth
  fields (`:163-198`), so the reconstructed array belongs to the closed vendor Sobolev subspace
  on the dense family and hence on every datum (`:200-210`).  `codRestrict` therefore gives the
  advertised total CLM (`:212-216`).

The agreement theorem uses exactly

```lean
ordinarySobolev q A.toLp A.translation_contDiff
```

at `ForcePathSmooth.lean:220-224`, not a different representative or orbit proof.  Its coordinate
proof uses the vendor's `ordinarySobolev_coordinate` and the same translated orbit
(`ForcePathSmooth.lean:91-112`; vendor definition at
`vendor/NavierStokesAndEuler/Euler/MeanOrbitSobolev.lean:70-82`).  The vendor `sobolevPath` is
definitionally the same ordinary carrier at
`vendor/NavierStokesAndEuler/Euler/SmoothFieldSobolevTime.lean:40-42`.

For the canonical force, `C01.forcePath` has field exactly `f(t,·)` and its continuity proof uses
the same order-`n` datum path and `jetOfDatum_ae` at
`formalization/NSFormalization/Section4/C01/JetPaths.lean:82-110`.  In the new proof,
`hpath t ht.1` is applied at each individual `t ∈ Icc 0 S`, then the agreement theorem identifies
the Sobolev elements exactly (`ForcePathSmooth.lean:237-245`).  Thus

```lean
sobolevPath (C01.forcePath hf) (C01.forcePath_jetLp_continuous hf) q t
  = datumSobolevCLM q (G t.1)
```

holds pointwise in `t`, not merely almost everywhere.  The internal jet comparison is an `Lp`
equality obtained by `Lp.ext`, which is the correct carrier equality.

The datum path need not be canonical by construction.  `hf.2 q` is eliminated existentially at
`ForcePathSmooth.lean:237`; no chosen `G` appears in the theorem statement.  Any two possible data
for the same slice are equal by `D01.isSobolevDatum_unique`
(`formalization/NSFormalization/Section4/D01/ForceClass.lean:282-294`), and more directly both
reconstruct to the same `ordinarySobolev`.  The reviewer example proving this latter fact is
`research/A01/probes/rev187_lane186_consumer.lean:46-54`.

## Time smoothness and packaging

The time proof composes the all-space `ContDiff` CLM with `hGc : ContDiffOn ℝ ∞ G (Ici 0)`,
then restricts by set monotonicity from `Ici 0` to `Icc 0 S`
(`ForcePathSmooth.lean:237-240`).  It does **not** infer closed-interval smoothness via a derivative
lemma and therefore needs no `UniqueDiffOn`.  `ContDiffOn.congr` is used only for pointwise equality,
and `projIcc_of_mem` removes clamping on the target set (`:240-245`; vendor `extendPath` at
`vendor/NavierStokesAndEuler/Euler/VolterraConvolution.lean:19-25`; Mathlib
`Order/Interval/Set/ProjIcc.lean:102-103`).

The first three conjuncts of `forcePath_of_memForceR_smooth` at
`ForcePathSmooth.lean:253-256` are token-identical to
`formalization/NSFormalization/Section4/A01/ForceBridge.lean:64-68`.  Its fourth conjunct really is
`∀ q (_hq : 6 ≤ q), ∀ hF, ...` (`ForcePathSmooth.lean:257-262`) and can be instantiated by
lane 186 with `F := C01.forcePath hf`.  The reviewer probe applies the actual merged
`compatible_carriers_of_bounds` theorem to precisely that carrier and supplies
`forcePath_sobolevPath_contDiffOn hf hS q` as `hfs`:
`research/A01/probes/rev187_lane186_consumer.lean:18-44`.  It typechecks with zero output.

## Hygiene

- The module has exactly 17 public declarations (`ForcePathSmooth.lean:35-266`), and all 17 print
  exactly `[propext, Classical.choice, Quot.sound]`.
- No `sorry`, `admit`, `axiom`, or `native_decide` occurs in the new Lean module or conformance
  file.  There is no `maxHeartbeats` setting.
- `git diff --name-status origin/erenup/integration...HEAD` shows one new Lean module only;
  no pre-existing Lean module, vendor file, contract, or test was modified.  `B1_LADDER.md` is a
  research record, not a Lean module.
- The checked paper citations above are accurate.  The construction citations to
  `D01.norm_jetOfDatum_le`, `C01.forcePath_jetLp_continuous`, vendor `ordinarySobolev`, vendor
  `sobolevPath`, and vendor `extendPath` all point to declarations with the claimed types.

# 3. Gaps and findings

1. **Note — stale gap sentence in the worker report.**
   `research/A01/REPORT_187.md:58-60` says the common-horizon/cross-order construction is still
   missing.  A whole-tree search in this checkout confirms it was absent on the lane's old base,
   but the required comparison against current `origin/erenup/integration` finds
   `CommonHorizon.lean:202-221`, `MildUniqueness.lean:185-230`, and
   `DatumPathSmooth.lean:710-734`.  Lanes 186/188 now provide the common carrier and discharge
   fixed-order uniqueness; all-order a-priori bounds remain an input.  The joint smooth
   representative remains a genuine gap: `ConstructorPieces.lean:14-17` still lists it as needed.
   The pressure construction likewise still assumes joint gradient smoothness rather than deriving
   it (`ConstructorPressure.lean:199-217`).  Interior pressure-gradient jet continuity alone is
   present at `formalization/NSFormalization/Section4/C01/PressureJetPath.lean:227-278`.

2. **Note — branch is behind the current compatibility base.**
   The lane changes no file under `verification/`, so the lane brief's conditional contract
   compatibility gate is not applicable.  I nevertheless ran it and the full gate script.  They
   fail because current `origin/erenup/integration` has stable contract
   `verification/Contracts/V2/GradientL6.lean`, while this old checkout predates that file.  At the
   end of review `git rev-list --left-right --count HEAD...origin/erenup/integration` printed
   `1 43`.  This is a stale-checkout failure, not a failure of the new Lean theorem.  The module was
   also recompiled against the integration build in a temporary olean overlay, and the lane-186
   consumer probe passed.

3. **Substantive negative check.**
   `research/A01/probes/rev187_negative_widen_interval.lean:22-36` widens the main theorem's set
   from `Icc 0 S` to `Icc (-1) S` and replays the proof.  It fails at the expected load-bearing
   boundary, because `MemForceR` only gives datum smoothness on `futureTimes = Ici 0`:

   ```text
   ../research/A01/probes/rev187_negative_widen_interval.lean:30:73: error: Type mismatch
     ht.left
   has type
     -1 ≤ x†
   but is expected to have type
     x† ∈ futureTimes
   ```

   The two later `omega could not prove the goal` errors are the same mutation propagating to the
   pointwise force slice: a negative `t` cannot form the required `Icc 0 S` subtype or satisfy
   `hpath t (0 ≤ t)`.  This mutation changes the interval; it does not merely drop an argument.

# 4. Commands and results

Every Lean command sourced `. scripts/lean-env.sh`; every `lake` invocation was launched from
`verification/` with `LEAN_NUM_THREADS=6`.

1. Module build:

   ```text
   $ cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A01.ForcePathSmooth
   ... dependency-facet linter replays only; no line names ForcePathSmooth.lean ...
   Build completed successfully (10232 jobs).
   [exit 0]
   ```

   The replayed warnings are from existing `FiniteHilbertBochner`, `RealSobolev`, Paper3, and
   HeliCorgi/vendor facets; none is from the reviewed module.

2. Direct module check:

   ```text
   $ cd verification && LEAN_NUM_THREADS=6 lake env lean \
       ../formalization/NSFormalization/Section4/A01/ForcePathSmooth.lean
   <zero output>
   [exit 0]
   ```

3. Axiom file:

   ```text
   $ cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/A01/axioms_hfs.lean
   'NSFormalization.Section4.A01.jetOfDatumCLM' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section4.A01.jetOfDatumCLM_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section4.A01.datumWordCLM' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section4.A01.datumArrayCLM' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section4.A01.datumArrayCLM_eq_ordinarySobolev' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section4.A01.schwartzDatum' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section4.A01.denseRange_schwartzDatum' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section4.A01.schwartzRealField' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section4.A01.schwartzRealField_smooth' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section4.A01.schwartzSmoothField' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section4.A01.schwartzSmoothField_field' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section4.A01.schwartzDatum_isSobolevDatum' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section4.A01.datumArrayCLM_mem_sobolevSubspace' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section4.A01.datumSobolevCLM' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section4.A01.datumSobolevCLM_eq_ordinarySobolev' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section4.A01.forcePath_sobolevPath_contDiffOn' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section4.A01.forcePath_of_memForceR_smooth' depends on axioms: [propext, Classical.choice, Quot.sound]
   [exit 0]
   ```

4. Repository check:

   ```text
   $ make check
   python3 experiments/check_formalization_plan.py --check
   ... "missing_copied_imports": [], "tracked_cache_free": true ...
   python3 experiments/check_contracts.py
   ... "base_compatibility_checked": false,
       "scope": "Architecture checks only; run lake test for Lean type and axiom checks." ...
   python3 experiments/test_contract_policy.py
   .............
   ----------------------------------------------------------------------
   Ran 13 tests in 0.044s

   OK
   python3 experiments/check_work_queue.py
   30 work items: ownership, contract registration and task cards consistent.
   [exit 0]
   ```

5. Positive integration consumer and datum-choice/non-vacuity probe:

   ```text
   $ cd verification && LEAN_NUM_THREADS=6 lake env env LEAN_PATH=<integration-overlay> \
       lean -R .. ../research/A01/probes/rev187_lane186_consumer.lean
   <zero output>
   [exit 0]
   ```

   The overlay contains the current integration build plus this lane's module recompiled against
   it; it was needed only because the read-only lane checkout predates `CommonHorizon.lean`.

6. Negative interval mutation:

   ```text
   $ cd verification && LEAN_NUM_THREADS=6 lake env lean \
       ../research/A01/probes/rev187_negative_widen_interval.lean
   ../research/A01/probes/rev187_negative_widen_interval.lean:30:73: error: Type mismatch
     ht.left
   has type
     -1 ≤ x†
   but is expected to have type
     x† ∈ futureTimes
   ../research/A01/probes/rev187_negative_widen_interval.lean:35:71: error: omega could not prove the goal:
   No usable constraints found. You may need to unfold definitions so `omega` can see linear arithmetic facts about `Nat` and `Int`, which may also involve multiplication, division, and modular remainder by constants.
   ../research/A01/probes/rev187_negative_widen_interval.lean:36:17: error: omega could not prove the goal:
   No usable constraints found. You may need to unfold definitions so `omega` can see linear arithmetic facts about `Nat` and `Int`, which may also involve multiplication, division, and modular remainder by constants.
   [exit 1, expected]
   ```

7. Hygiene:

   ```text
   $ git diff --check origin/erenup/integration...HEAD
   <zero output>
   [exit 0]

   $ git diff --name-status origin/erenup/integration...HEAD
   A formalization/NSFormalization/Section4/A01/ForcePathSmooth.lean
   A research/A01/ATTEMPTS_HFS.md
   M research/A01/B1_LADDER.md
   A research/A01/REPORT_187.md
   A research/A01/axioms_hfs.lean
   ```

8. Extra full gate script and explicit base check:

   ```text
   $ BASE_REF=origin/erenup/integration scripts/gates.sh \
       NSFormalization.Section4.A01.ForcePathSmooth
   == make check
   ... PASS ...
   == lake build NSFormalization.Section4.A01.ForcePathSmooth
   Build completed successfully (10232 jobs).
   == make test
   ... all listed contracts: checked; standard logical axioms only ...
   == make test-mutations
   extra_axiom: rejected as required
   weakened_hypothesis: rejected as required
   Mutation suite passed. This is an infrastructure check, not a PDE proof.
   == check_contracts
   AssertionError: Removed stable specification: verification/Contracts/V2/GradientL6.lean
   [exit 1]

   $ python3 experiments/check_contracts.py --base-ref origin/erenup/integration
   Traceback (most recent call last):
     File ".../experiments/check_contracts.py", line 62, in check_compatibility
       assert (root / path).is_file(), f'Removed stable specification: {path}'
   AssertionError: Removed stable specification: verification/Contracts/V2/GradientL6.lean
   [exit 1]
   ```

## Exact fixes before merge

1. Update this lane onto current `origin/erenup/integration`, then rerun
   `BASE_REF=origin/erenup/integration scripts/gates.sh NSFormalization.Section4.A01.ForcePathSmooth`;
   no Lean proof change is indicated by the failure.
2. Replace `research/A01/REPORT_187.md:58-60` with the single line:
   `This lane closes only force-side hfs; current integration now supplies common-horizon/cross-order R3 via lanes 178/186/188 given the all-order bounds, while the joint smooth representative and B2 joint pressure-gradient regularity remain.`
