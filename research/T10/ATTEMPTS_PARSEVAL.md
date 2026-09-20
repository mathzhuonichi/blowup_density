# Lane 286: Parseval proof attempts

## Successful route

- Read `CLAUDE.md`, current-state documents, the amended spec/API docstrings,
  `RECONCILIATION.md` §5, `CANONICAL.md`, `COMPARISON.md` “Needs a lemma”,
  and the first 40 lines of `logs/LESSONS.md`.
- Searched with `grep -rnE` in `Paper1/TorusCube.lean`, `Paper1/Periodic*.lean`,
  `Section4/D01/`, and Mathlib's `AddCircleMulti.lean`, `AddCircle.lean`,
  `MeasureTheory/Group/AddCircle.lean`, and `Analysis/Normed/Lp/lpSpace.lean`.
  Full local search output: `tmp/parseval/search.txt` (ignored build scratch).
- Reused `UnitAddTorus.mFourierBasis.repr` and `mFourierBasis_repr`. The latter
  is extended from the chosen `Lp` representative to the physical lift by
  `MemLp.coeFn_toLp` and `integral_congr_ae`.
- Bounded each complexified component by the Euclidean vector norm to get
  `MemLp`. Built the three coefficient sequences with `WithLp.toLp 2`.
- Proved reality directly with `integral_conj` and `mFourier_neg`. This fact
  even holds for totalized Fourier integrals without integrability assumptions.
- Reused the same local Haar instances as `Paper1.TorusCube`; product measure
  inference proves `periodicTorusMeasure_probability`. `hz.integrable` supplies
  the amended datum's integrability conjunct from L² on this finite measure.
- For forward Parseval, identify each datum component with the Hilbert basis
  representation and use `LinearIsometryEquiv.norm_map`.
- Prove the real squared-norm identity using `L2.inner_def`, finite additivity
  of the Bochner integral, and `PiLp.norm_sq_eq_of_L2`. This avoids separately
  re-proving the equivalent finite-lintegral/rpow identity: Mathlib's proved
  `Lp.enorm_toLp` already supplies the conversion to `eLpNorm`. Convert equal
  nonnegative real norms using `ofReal_norm`.
- Both exact API statements close. Zero-field and arbitrary constant-field
  examples exercise existence and the extended-norm identity.

## Residual hypotheses

None. No canonical definition blocks the proof, and neither target was weakened.
No heartbeat override or additional mathematical assumption was needed.

## Failed elaboration attempts (exact diagnostics)

The following diagnostics refer to intermediate versions, not the final files.
Repeated errors are retained so that each failed run is recorded.

### Initial component/reality bridge

```text
../formalization/NSFormalization/Section3/T10/Parseval.lean:26:42: error: Application type mismatch: The argument
  PiLp.continuous_apply ↑↑i
has type
  ∀ (β : ?m.42 → Type ?u.24) [inst : (i : ?m.42) → TopologicalSpace (β i)] (i_1 : ?m.42), Continuous fun f => f.ofLp i_1
but is expected to have type
  Continuous ?m.40
in the application
  Continuous.comp Complex.continuous_ofReal (PiLp.continuous_apply ↑↑i)
../formalization/NSFormalization/Section3/T10/Parseval.lean:29:6: error: Type mismatch: After simplification, term
  PiLp.norm_apply_le (torusLift z y) i
 has type
  |(torusLift z y).ofLp i| ≤ ‖torusLift z y‖
but is expected to have type
  ‖torusLift (fun x => ↑((z x).ofLp i)) y‖ ≤ ‖torusLift z y‖
../formalization/NSFormalization/Section3/T10/Parseval.lean:47:9: error: Tactic `unfold` failed to unfold `Paper1.periodicFourierCoeff` in
  periodicFourierCoeff (fun x => ↑(f x)) (-k) = star (periodicFourierCoeff (fun x => ↑(f x)) k)
```

Resolution: Supply both explicit PiLp parameters; expose the lifted component with `change`; unfold the T10 alias before the Paper1 definition.

### Conjugation rewrite

```text
../formalization/NSFormalization/Section3/T10/Parseval.lean:49:6: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  (starRingEnd ?m.15) (∫ (x : ?m.12), ?m.17 x ∂?m.14)
in the target expression
  ∫ (t : UnitAddTorus (Fin 3)), (UnitAddTorus.mFourier (- -k)) t • Paper1.torusLift (fun x => ↑(f x)) t =
    star (∫ (t : UnitAddTorus (Fin 3)), (UnitAddTorus.mFourier (-k)) t • Paper1.torusLift (fun x => ↑(f x)) t)

f : Space → ℝ
k : PeriodicFrequency
⊢ ∫ (t : UnitAddTorus (Fin 3)), (UnitAddTorus.mFourier (- -k)) t • Paper1.torusLift (fun x => ↑(f x)) t =
    star (∫ (t : UnitAddTorus (Fin 3)), (UnitAddTorus.mFourier (-k)) t • Paper1.torusLift (fun x => ↑(f x)) t)
```

Resolution: `star` is not the syntactic `conj` pattern expected by the rewrite; use `Complex.star_def` first.

### First complete forward proof

```text
../formalization/NSFormalization/Section3/T10/Parseval.lean:49:6: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  (starRingEnd ?m.15) (∫ (x : ?m.12), ?m.17 x ∂?m.14)
in the target expression
  ∫ (t : UnitAddTorus (Fin 3)), (UnitAddTorus.mFourier (- -k)) t • Paper1.torusLift (fun x => ↑(f x)) t =
    star (∫ (t : UnitAddTorus (Fin 3)), (UnitAddTorus.mFourier (-k)) t • Paper1.torusLift (fun x => ↑(f x)) t)

f : Space → ℝ
k : PeriodicFrequency
⊢ ∫ (t : UnitAddTorus (Fin 3)), (UnitAddTorus.mFourier (- -k)) t • Paper1.torusLift (fun x => ↑(f x)) t =
    star (∫ (t : UnitAddTorus (Fin 3)), (UnitAddTorus.mFourier (-k)) t • Paper1.torusLift (fun x => ↑(f x)) t)
../formalization/NSFormalization/Section3/T10/Parseval.lean:119:11: error(lean.invalidField): Invalid field `enorm_toLp`: The environment does not contain `And.enorm_toLp`, so it is not possible to project the field `enorm_toLp` from an expression
  hz
of type
  AEStronglyMeasurable (torusLift z) periodicTorusMeasure ∧ eLpNorm (torusLift z) 2 periodicTorusMeasure < ∞
../formalization/NSFormalization/Section3/T10/Parseval.lean:114:61: error: unsolved goals
z : SpatialField
A : ↥(PeriodicSobolev 0)
hA : IsPeriodicDatum 0 z A
hz : MemLp (torusLift z) 2 periodicTorusMeasure
hn : ‖A‖ = ‖MemLp.toLp (torusLift z) hz‖
⊢ ‖A‖ₑ = eLpNorm (torusLift z) 2 periodicTorusMeasure
```

Resolution: The conjugation issue remained in this run. `enorm_toLp` belongs to `Lp`, not `MemLp`; call `Lp.enorm_toLp hz`.

### Extended norm lemma name

```text
../formalization/NSFormalization/Section3/T10/Parseval.lean:119:26: error(lean.unknownIdentifier): Unknown identifier `enorm_eq_ofReal_norm`
../formalization/NSFormalization/Section3/T10/Parseval.lean:114:61: error: unsolved goals
z : SpatialField
A : ↥(PeriodicSobolev 0)
hA : IsPeriodicDatum 0 z A
hz : MemLp (torusLift z) 2 periodicTorusMeasure
hn : ‖A‖ = ‖MemLp.toLp (torusLift z) hz‖
⊢ ‖A‖ₑ = ‖MemLp.toLp (torusLift z) hz‖ₑ
```

Resolution: The suggested `enorm_eq_ofReal_norm` spelling is absent in this pin. Use the proved reverse identity `ofReal_norm`.

### First non-vacuity examples

```text
../research/T10/probes/parseval_closes.lean:26:4: error(lean.unknownIdentifier): Unknown identifier `memLp_zero`
../research/T10/probes/parseval_closes.lean:29:2: error: Type mismatch: After simplification, term
  parseval_forward (fun x => 0) A hA hz
 has type
  ‖A‖ₑ = eLpNorm (torusLift fun x => 0) 2 periodicTorusMeasure
but is expected to have type
  ‖A‖ₑ = 0
../research/T10/probes/parseval_closes.lean:34:2: warning: Try this:
  letI̵

The goal is a proposition, so `let` is preferred over `letI`.
The difference between `let` and `letI` is that `letI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
../research/T10/probes/parseval_closes.lean:39:2: error: Type mismatch: After simplification, term
  parseval_forward (fun x => c) A hA hz
 has type
  ‖A‖ₑ = eLpNorm (torusLift fun x => c) 2 periodicTorusMeasure
but is expected to have type
  ‖A‖ₑ = ‖c‖ₑ
```

Resolution: The zero lemma is `MemLp.zero`; expose the constant torus function with `change`. Use `let`, as requested by the instance linter.

### Constant normalization

```text
../research/T10/probes/parseval_closes.lean:26:7: error: `simp` made no progress
../research/T10/probes/parseval_closes.lean:43:2: error: Type mismatch: After simplification, term
  hn
 has type
  ‖A‖ₑ = eLpNorm (fun x => c) 2 periodicTorusMeasure
but is expected to have type
  ‖A‖ₑ = ‖c‖ₑ
```

Resolution: Use `MemLp.zero` directly. The constant Lp norm formula is not applied by bare `simp`.

### Explicit constant formula

```text
../research/T10/probes/parseval_closes.lean:43:27: error: unsolved goals
c : Space
this : IsProbabilityMeasure periodicTorusMeasure := periodicTorusMeasure_probability
hp : IsPeriodicSpatial fun x => c
hz : MemLp (torusLift fun x => c) 2 periodicTorusMeasure
A : ↥(PeriodicSobolev 0)
hA : IsPeriodicDatum 0 (fun x => c) A
hn : ‖A‖ₑ = eLpNorm (fun x => c) 2 periodicTorusMeasure
⊢ ¬?m.78 = 0
../research/T10/probes/parseval_closes.lean:43:41: error: unsolved goals
c : Space
this : IsProbabilityMeasure periodicTorusMeasure := periodicTorusMeasure_probability
hp : IsPeriodicSpatial fun x => c
hz : MemLp (torusLift fun x => c) 2 periodicTorusMeasure
A : ↥(PeriodicSobolev 0)
hA : IsPeriodicDatum 0 (fun x => c) A
hn : ‖A‖ₑ = eLpNorm (fun x => c) 2 periodicTorusMeasure
⊢ ¬?m.78 = ∞
../research/T10/probes/parseval_closes.lean:43:2: error: Type mismatch: After simplification, term
  hn
 has type
  ‖A‖ₑ = eLpNorm (fun x => c) 2 periodicTorusMeasure
but is expected to have type
  ‖A‖ₑ = ‖c‖ₑ
```

Resolution: The exponent metavariable in a simp argument was unconstrained. Rewrite with an explicitly typed `(2 : ℝ≥0∞) ≠ 0` premise.

## Search-path correction

An exploratory search guessed the non-existent path
`Mathlib/Analysis/Normed/Group/ENorm.lean`. Exact diagnostic:

```text
rg: verification/.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/ENorm.lean: IO error for operation on verification/.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/ENorm.lean: No such file or directory (os error 2)
```

A recursive search in `Analysis/Normed` located `ofReal_norm` in
`Analysis/Normed/Group/Basic.lean`. This was a path correction, not a missing lemma.

## Final checks

See `REPORT_286.md` for command results. All failed proof attempts above were
resolved; module and probe elaborate with zero diagnostics in their final form.
