ACCEPT-WITH-NOTES

## 1. What the lane claims

The paper defines `J = (I-Δ)^(1/2)`, `Y = ‖u‖_{H^(1/2)}`,
`Z = ‖∇u‖_{H^(1/2)}`, and `B = ‖f‖_{H^(-1/2)}` at
`paper/sections/04-whole-space.tex:146-151`; it then states the exact weight
identity and the two force bounds at `paper/sections/04-whole-space.tex:152-159`.
The worker report claims precisely those three static datum-level results at
`research/R44/REPORT_218.md:5-21`, and lists the exported declarations at
`research/R44/REPORT_218.md:25-49`.

The report is accurate about the deliberate correction to the brief's literal
stored-data formula. `SobolevHilbert s` is an `L²` carrier whose order affects
realization rather than its underlying data space
(`formalization/NSFormalization/Paper3/SobolevHilbertModel.lean:19-25`), and
`RealSobolevHilbert s` uses a closed subspace whose definition is independent
of `s` (`formalization/NSFormalization/Source/RealSobolev.lean:116-124`). Thus a
physical `J : H^s → H^(s-1)` is identity/order reindexing on the stored
weighted datum. Multiplying that stored arbitrary `L²` datum by the unbounded
square-root weight would not be a total isometry. The lane exposes both the
carrier identity and the physical unweighted symbol, so the correction is
mathematically faithful rather than a weakening.

## 2. What is in Lean

Every declaration claimed in the report exists with the claimed statement:

- `Jmul`, its stored-data identity, its physical symbol, and its norm/enorm
  isometries are at
  `formalization/NSFormalization/Section4/R44/JWeight.lean:43-93`. In
  particular, `Jmul_symbol` removes the order weights on both sides and states
  multiplication by `(1+‖ξ‖²)^(1/2)` at lines 57-87.
- The one named input structure is exactly `JWeightDatum`; it contains genuine
  order `1/2`, `3/2`, derivative-order `1/2`, and force-order `-1/2` realization
  data plus the weak derivative identity
  (`formalization/NSFormalization/Section4/R44/JWeight.lean:103-115`). There is
  no interval binder, top-valued norm premise, or free abstract proposition.
- `Y`, `Z`, `B`, and the pinned real datum pairing are defined at
  `formalization/NSFormalization/Section4/R44/JWeight.lean:121-134`. The `Z`
  definition uses the existing vector-gradient norm, whose definition and
  sum-of-coordinate-squares theorem are at
  `formalization/NSFormalization/Section4/A03/OuterTameProduct.lean:86-108`.
- Norm attainment and the three datum spellings are proved at
  `formalization/NSFormalization/Section4/R44/JWeight.lean:140-170`. In
  particular, `B_eq_norm` prevents a hidden `⊤.toReal = 0` interpretation.
- `weight_identity` has exactly
  `(sobolevENorm (3/2) u).toReal^2 = Y u^2 + Z u^2` at
  `formalization/NSFormalization/Section4/R44/JWeight.lean:178-197`. It reduces
  to the existing sharp raising identity
  `formalization/NSFormalization/Section4/D01/FiniteOrderNorm.lean:378-397`.
- `force_pairing_le` and `force_pairing_le'` have exactly the square-root and
  `Y+Z` conclusions at
  `formalization/NSFormalization/Section4/R44/JWeight.lean:207-227`. The left
  side cannot be made trivially zero by an implementation choice:
  `forceJPairing` is definitionally the real inner product of the unique
  negative-half force datum with `Jmul` of the three-halves velocity datum
  (`formalization/NSFormalization/Section4/R44/JWeight.lean:131-134`).

The combined structure is stronger than any one conclusion needs in isolation,
but this is the single explicitly advertised consumer package required by the
brief, not a concealed premise. Its fields are used across the three main
results, and its satisfiability is independently demonstrated. The zero datum
is constructed at `research/R44/axioms_s1a.lean:27-54`; the compact-smooth
field is proved nonzero at `research/R44/axioms_s1a.lean:58-73`, packaged as a
standard datum at `research/R44/axioms_s1a.lean:75-124`, and passed through the
weight identity and final force form at `research/R44/axioms_s1a.lean:126-145`;
the universal square-root theorem applies to that same witness. Hence the
theorem is not vacuous.

The axiom audit covers every exported declaration and every named witness
(`research/R44/axioms_s1a.lean:149-182`). Every printed set is exactly
`[propext, Classical.choice, Quot.sound]`.

## 3. Gaps and findings

1. **Documentation only, exact one-line fix.** The claim that negative-order
   force-path "measurability ... remain[s] open" at
   `research/R44/REPORT_218.md:53-57` and `research/R44/R44_SPLIT.md:238` is too
   broad. The whole-tree search finds `isSobolevPath_lower`, which constructs
   the lowered path (`formalization/NSFormalization/Section4/D01/HalfOrder.lean:117-127`),
   and `forceSobolevENorm_ne_top` explicitly constructs its `MemLp` and
   `AEStronglyMeasurable` evidence
   (`formalization/NSFormalization/Section4/D01/HalfOrder.lean:151-173`). Replace
   the report's lines 55-57 and the G3 cell with this exact sentence:
   **"A named continuous order-`-1/2` force-datum path in the R44 consumer
   shape, and its prefix-integral/time-norm-square identity, remain to be
   packaged."** No Lean change is required.

2. The other absence claims survive whole-tree searches. `R44` currently has
   only `JWeight.lean` and `Pieces.lean`; `Pieces.lean` explicitly treats the
   PDE `eq:Rcritical2` input as separate
   (`formalization/NSFormalization/Section4/R44/Pieces.lean:5-21`). Searches for
   the exact J-weighted momentum derivative/pressure cancellation,
   inhomogeneous critical trilinear estimate, and final R44 absorption found
   only the homogeneous R43 or higher-order C01/A04 analogues, not the R44
   statements. Searches under `verification/` found no `JWeight`,
   `weight_identity`, or `force_pairing_le` registration, confirming the
   report's contract/binding gap.

3. Hygiene passes. Relative to `origin/erenup/integration`, the lane adds one
   new formalization module and research deliverables; it modifies no existing
   Lean module. The only existing-file change is the required research split
   record. The implementation and axiom file contain no `sorry`, `admit`,
   `axiom`, `native_decide`, or `set_option maxHeartbeats` occurrence.

## 4. Commands and results

All Lean commands were run after `. scripts/lean-env.sh`; every `lake` command
was run from `verification/` with `LEAN_NUM_THREADS=6`.

### Module build and direct typecheck

```text
$ LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.R44.JWeight
⚠ [8777/8854] Replayed NSFormalization.Source.FiniteHilbertBochner
warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'
...
⚠ [9912/9928] Replayed NSFormalization.Paper3.SobolevDirectionalDerivative
warning: NSFormalization/Paper3/SobolevDirectionalDerivative.lean:103:16: `SchwartzMap.smul_apply` has been deprecated: Use `smul_apply` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.smul_apply` to `smul_apply x`).
Build completed successfully (9928 jobs).
[exit 0]
```

The omitted middle consists only of replayed warnings from pre-existing source
and vendor modules. There is no `JWeight.lean` diagnostic (the standard gate
log contains zero matches for `JWeight.lean:`), so the new module itself is
silent.

```text
$ LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section4/R44/JWeight.lean
[no output]
[exit 0]
```

### Axiom and non-vacuity file

```text
$ LEAN_NUM_THREADS=6 lake env lean ../research/R44/axioms_s1a.lean
'NSFormalization.Section4.R44.Jmul' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.Jmul_weighted_symbol' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.Jmul_symbol' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.Jmul_norm' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.Jmul_enorm' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.JWeightDatum' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.Y' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.Z' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.B' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.forceJPairing' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.sobolevENorm_eq_of_isSobolevDatum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.R44.Y_eq_norm' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.Z_sq_eq_sum_norm' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.B_eq_norm' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.weight_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.force_pairing_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.force_pairing_le'' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lane218S1AAudit.zeroJWeightDatum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lane218S1AAudit.bumpField_smooth' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lane218S1AAudit.bumpField_compact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lane218S1AAudit.bumpField_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lane218S1AAudit.bumpSmoothL2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lane218S1AAudit.bumpVelocityHalf' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lane218S1AAudit.bumpVelocityThreeHalf' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lane218S1AAudit.bumpVelocityThreeHalf_isDatum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lane218S1AAudit.bumpGradientSmoothL2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lane218S1AAudit.bumpGradientHalf' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lane218S1AAudit.bump_gradient_pairing' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lane218S1AAudit.bumpGradientHalf_isDatum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lane218S1AAudit.bumpJWeightDatum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lane218S1AAudit.nonzero_bump_satisfies_S1a' depends on axioms: [propext, Classical.choice, Quot.sound]
[exit 0]
```

### Repository gates

`make check` exited 0. Its JSON contract closures are very large; the exact
decisive tail was:

```text
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.045s

OK
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.
```

The full standard gate log was 1,176,009 bytes / 28,482 lines. Its exact phase
markers and tail were:

```text
== make check
== lake build NSFormalization.Section4.R44.JWeight
== make test
== make test-mutations
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
== check_contracts
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
== gates OK
[exit 0]
```

Although `verification/` was not touched, `scripts/gates.sh` still ran
`python3 experiments/check_contracts.py --base-ref origin/erenup/integration`;
the displayed `base_compatibility_checked: true` is its exact terminal result.

### Hygiene, diff, whole-tree search, and negative mutation

```text
$ rg -n '(^|[[:space:]])(sorry|admit|axiom|native_decide)($|[[:space:]])' \
    formalization/NSFormalization/Section4/R44/JWeight.lean research/R44/axioms_s1a.lean
[no output]
$ rg -n 'set_option[[:space:]]+maxHeartbeats' \
    formalization/NSFormalization/Section4/R44/JWeight.lean research/R44/axioms_s1a.lean
[no output]

$ git diff --name-status origin/erenup/integration...HEAD
A formalization/NSFormalization/Section4/R44/JWeight.lean
A research/R44/ATTEMPTS_S1A.md
M research/R44/R44_SPLIT.md
A research/R44/REPORT_218.md
A research/R44/axioms_s1a.lean
```

The required substantive mutation is
`research/R44/probes/rev218_weight_identity_plus_one.lean:7-10`: it changes the
main identity by adding the constant `1`, without removing any argument. Exact
result:

```text
$ LEAN_NUM_THREADS=6 lake env lean ../research/R44/probes/rev218_weight_identity_plus_one.lean
../research/R44/probes/rev218_weight_identity_plus_one.lean:10:2: error: Type mismatch
  weight_identity h
has type
  (NSFormalization.Section4.D01.sobolevENorm (3 / 2) u).toReal ^ 2 = Y u ^ 2 + Z u ^ 2
but is expected to have type
  (NSFormalization.Section4.D01.sobolevENorm (3 / 2) u).toReal ^ 2 = Y u ^ 2 + Z u ^ 2 + 1
[exit 1, expected]
```

The required whole-Section4 gap searches included the following exact focused
results (broader synonym searches gave only the already cited R43/C01/A04
analogues):

```text
$ grep -rnE 'isSobolevPath_lower|forceSobolevENorm_ne_top|AEStronglyMeasurable' formalization/NSFormalization/Section4/D01/HalfOrder.lean
formalization/NSFormalization/Section4/D01/HalfOrder.lean:120:theorem isSobolevPath_lower {s r : ℝ} (hrs : r ≤ s) {f : VelocityField}
formalization/NSFormalization/Section4/D01/HalfOrder.lean:143:      IsSobolevPath s f G ∧ AEStronglyMeasurable G forceTimeMeasure},
formalization/NSFormalization/Section4/D01/HalfOrder.lean:156:theorem forceSobolevENorm_ne_top {f : VelocityField} (hf : MemForceR f)
formalization/NSFormalization/Section4/D01/HalfOrder.lean:165:    isSobolevPath_lower hsm hpath
formalization/NSFormalization/Section4/D01/HalfOrder.lean:169:        IsSobolevPath s f G ∧ AEStronglyMeasurable G forceTimeMeasure} =>
formalization/NSFormalization/Section4/D01/HalfOrder.lean:170:      Homogeneous.bochnerDatumENorm q s G.1) ⟨_, hpath', hmem.aestronglyMeasurable⟩

$ grep -rnE 'JWeight|forceJPairing|weight_identity|force_pairing_le|rcritical2|Rcritical2' formalization/NSFormalization/Section4/R44
formalization/NSFormalization/Section4/R44/Pieces.lean:9:`eq:Rcritical2`, the `J = (I-Δ)^{1/2}` weight identity, and the
formalization/NSFormalization/Section4/R44/Pieces.lean:32:/-- The universal small constants needed after `eq:Rcritical2`.
formalization/NSFormalization/Section4/R44/Pieces.lean:37:positive exponential rate dominating the rate `C₂` from `eq:Rcritical2`.
formalization/NSFormalization/Section4/R44/Pieces.lean:40:theorem exists_rcritical2_constants {C₀ C₁ Cemb C₂ C₃ : ℝ}
formalization/NSFormalization/Section4/R44/Pieces.lean:70:/-- The radius formula produced by `exists_rcritical2_constants` implies the
formalization/NSFormalization/Section4/R44/JWeight.lean:16:The single structure `JWeightDatum` is the datum-level restriction consumed by
formalization/NSFormalization/Section4/R44/JWeight.lean:103:structure JWeightDatum (u f : Space → Space) where
formalization/NSFormalization/Section4/R44/JWeight.lean:133:def forceJPairing {u f : Space → Space} (h : JWeightDatum u f) : ℝ :=
formalization/NSFormalization/Section4/R44/JWeight.lean:149:theorem Y_eq_norm {u f : Space → Space} (h : JWeightDatum u f) :
formalization/NSFormalization/Section4/R44/JWeight.lean:155:theorem Z_sq_eq_sum_norm {u f : Space → Space} (h : JWeightDatum u f) :
formalization/NSFormalization/Section4/R44/JWeight.lean:168:theorem B_eq_norm {u f : Space → Space} (h : JWeightDatum u f) :
formalization/NSFormalization/Section4/R44/JWeight.lean:178:theorem weight_identity {u f : Space → Space} (h : JWeightDatum u f) :
formalization/NSFormalization/Section4/R44/JWeight.lean:206:Cauchy--Schwarz followed by `weight_identity`. -/
formalization/NSFormalization/Section4/R44/JWeight.lean:207:theorem force_pairing_le {u f : Space → Space} (h : JWeightDatum u f) :
formalization/NSFormalization/Section4/R44/JWeight.lean:208:    |forceJPairing h| ≤ B f * Real.sqrt (Y u ^ 2 + Z u ^ 2) := by
formalization/NSFormalization/Section4/R44/JWeight.lean:210:    |forceJPairing h| ≤ ‖h.forceNegHalf‖ * ‖Jmul h.velocityThreeHalf‖ := by
formalization/NSFormalization/Section4/R44/JWeight.lean:214:      rw [← weight_identity h,
formalization/NSFormalization/Section4/R44/JWeight.lean:219:theorem force_pairing_le' {u f : Space → Space} (h : JWeightDatum u f) :
formalization/NSFormalization/Section4/R44/JWeight.lean:220:    |forceJPairing h| ≤ B f * (Y u + Z u) := by
formalization/NSFormalization/Section4/R44/JWeight.lean:226:  exact (force_pairing_le h).trans

$ grep -rnE 'forceJPairing|weight_identity|force_pairing_le|R44.JWeight' verification
[no output]
```

Fixes: replace the two overbroad G3 sentences identified in finding 1 with the
exact one-line wording supplied there; no Lean fix is required.
