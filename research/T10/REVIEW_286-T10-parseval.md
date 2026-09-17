ACCEPT

## 1. What the lane claims

The worker claims the exact canonical `TorusDataAPI.parseval_forward` and
`TorusDataAPI.parseval_backward` fields, seven supporting theorems, no residual
hypotheses, standard axioms only, and five new files
(`research/T10/REPORT_286.md:3-48`).  Those claims are accurate.

Statement fidelity is exact:

1. The canonical forward field is
   `research/T10/probes/api_on_canonical.lean:70-73`; the delivered theorem is
   token-for-token the same proposition at
   `formalization/NSFormalization/Section3/T10/Parseval.lean:120-123`.
2. The canonical backward field is
   `research/T10/probes/api_on_canonical.lean:82-85`; the delivered theorem is
   token-for-token the same proposition at
   `formalization/NSFormalization/Section3/T10/Parseval.lean:64-67`.
3. The closure examples copy both fields with the same quantifier order and no
   extra premise at `research/T10/probes/parseval_closes.lean:12-20`.
4. The paper defines the normalized unit-torus Fourier coefficient and
   inhomogeneous norm with the exact `2π` convention at
   `paper/sections/01-introduction.tex:83-97`, identifies `H⁰` with `L²` at
   `paper/sections/01-introduction.tex:99-103`, and specifies componentwise
   squared-norm summation at `paper/sections/01-introduction.tex:103`.
   The torus proof also explicitly invokes Parseval at
   `paper/sections/03-torus.tex:69-72`.  Thus the two Lean statements express
   the requested order-zero vector Parseval/Riesz--Fischer equivalence, with
   the correct normalization.
5. The amendment is present rather than silently weakened:
   `IsPeriodicDatum` contains Haar integrability at
   `formalization/NSFormalization/Section3/T10/PeriodicData.lean:100-106`,
   forward has the added physical `MemLp … 2` premise, and backward derives
   integrability from that premise on the probability torus.  This agrees with
   `research/T10/RECONCILIATION.md:46-63`.

## 2. What is in Lean

All nine declarations claimed in the report exist:

- `periodicTorusMeasure_probability`:
  `formalization/NSFormalization/Section3/T10/Parseval.lean:25-27`;
- `memLp_torusLift_component`:
  `formalization/NSFormalization/Section3/T10/Parseval.lean:29-39`;
- `fourier_repr_toLp`:
  `formalization/NSFormalization/Section3/T10/Parseval.lean:41-51`;
- `periodicFourierCoeff_real_neg`:
  `formalization/NSFormalization/Section3/T10/Parseval.lean:53-61`;
- `parseval_backward`:
  `formalization/NSFormalization/Section3/T10/Parseval.lean:63-81`;
- `norm_toLp_sq_integral`:
  `formalization/NSFormalization/Section3/T10/Parseval.lean:83-90`;
- `datum_component_norm_sq`:
  `formalization/NSFormalization/Section3/T10/Parseval.lean:92-103`;
- `datum_norm_sq_integral`:
  `formalization/NSFormalization/Section3/T10/Parseval.lean:105-117`;
- `parseval_forward`:
  `formalization/NSFormalization/Section3/T10/Parseval.lean:119-128`.

The proof content supports the prose claims:

1. The normalized Haar probability instance is established at
   `Parseval.lean:21-27`.  Backward constructs each component with
   `UnitAddTorus.mFourierBasis.repr` at `Parseval.lean:69-74`, proves the real
   conjugate-reflection condition at `Parseval.lean:75-78`, and uses both the
   named periodicity premise and `hz.integrable` at `Parseval.lean:79-81`.
2. Mathlib defines `mFourierBasis` as an isometric equivalence to `ℓ²` at
   `verification/.lake/packages/mathlib/Mathlib/Analysis/Fourier/AddCircleMulti.lean:263-267`
   and identifies `repr` with `mFourierCoeff` at the same file's lines 274-283.
   The pre-existing local continuous Parseval model is exactly
   `formalization/NSFormalization/Paper1/TorusCube.lean:86-98`.
3. Forward identifies each datum component with the Hilbert-basis image at
   `Parseval.lean:93-103`, sums the three squared component norms at
   `Parseval.lean:106-117`, and converts the resulting real norm identity to
   the requested extended norm equality at `Parseval.lean:125-128`.
4. No premise is vacuous or dishonestly isolated.  Backward uses `hp` and `hz`;
   forward uses the coefficient part of `hA` and uses `hz` for the actual L²
   representative and norm.  There is no `.toReal`, no `⊤` totalization, no
   interval, no unused target binder, and no added named bridge hypothesis in
   either target (`Parseval.lean:64-81,120-128`).
5. Non-vacuity is stronger than the minimum requested.  The zero-field
   existence/norm example is `research/T10/probes/parseval_closes.lean:22-31`,
   and the universally quantified constant-field example (hence including
   nonzero constants) is at `research/T10/probes/parseval_closes.lean:33-44`.
   The entire probe elaborates with zero output.

Hygiene also passes.  Before reviewer artifacts, the base-range diff contained
exactly the five additions listed in `REPORT_286.md:27-39`; no existing module
or `verification/` file was modified.  Searches over all delivered/reviewer
Lean files found no `sorry`, `admit`, `axiom`, or `native_decide`, and no
`maxHeartbeats`.  The nine `#print axioms` commands are enumerated at
`research/T10/axioms_parseval.lean:3-11` and each reports exactly
`[propext, Classical.choice, Quot.sound]`.  The cited canonical aliases are
indeed reused as documented in `research/T10/CANONICAL.md:91-105`.

## 3. Gaps

There is no proof or statement gap and no fix is required.

The worker makes no mathematical "not in the tree" claim
(`research/T10/REPORT_286.md:46-54`).  Consequently there is no missing-lemma
claim for which a whole-`Section4` grep is required.  The only absence discussed
in the attempts record is the guessed identifier `enorm_eq_ofReal_norm`; the
record locates and uses `ofReal_norm`, explicitly classifying this as a resolved
name/path correction rather than a missing lemma
(`research/T10/ATTEMPTS_PARSEVAL.md:110-123,198-208`).

The substantive reviewer mutation is at
`research/T10/probes/rev286_parseval_p1_mutation.lean:11-15`: it replaces the
physical `L²` norm in the main forward conclusion by `L¹`, without removing
any argument.  It fails as expected:

```text
../research/T10/probes/rev286_parseval_p1_mutation.lean:15:61: error: Type mismatch
  parseval_forward
has type
  ∀ (z : SpatialField) (A : ↥(PeriodicSobolev 0)),
    IsPeriodicDatum 0 z A →
      MemLp (torusLift z) 2 periodicTorusMeasure → ‖A‖ₑ = eLpNorm (torusLift z) 2 periodicTorusMeasure
but is expected to have type
  ∀ (z : SpatialField) (A : ↥(PeriodicSobolev 0)),
    IsPeriodicDatum 0 z A →
      MemLp (torusLift z) 2 periodicTorusMeasure → ‖A‖ₑ = eLpNorm (torusLift z) 1 periodicTorusMeasure
```

## 4. Commands and results

All Lean commands sourced `scripts/lean-env.sh`, used
`LEAN_NUM_THREADS=6`, and invoked Lake only from `verification/`.

### Module build

Command:

```sh
cd verification
. ../scripts/lean-env.sh
LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T10.Parseval
```

Exit 0.  Exact output follows; every diagnostic is a replayed warning in an
older imported module, and none points to `Parseval.lean`:

```text
⚠ [8778/9113] Replayed NSFormalization.Source.FiniteHilbertBochner
warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
warning: NSFormalization/Source/FiniteHilbertBochner.lean:23:37: This simp argument is unused:
  PiLp.single_apply

Hint: Omit it from the simp argument list.
  [apply] simp [h]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: NSFormalization/Source/FiniteHilbertBochner.lean:39:23: This simp argument is unused:
  PiLp.single_apply

Hint: Omit it from the simp argument list.
  [apply] simp [insert, coord]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
⚠ [9318/9353] Replayed NSFormalization.Source.RealSobolev
warning: NSFormalization/Source/RealSobolev.lean:90:30: This simp argument is unused:
  Complex.smul_re

Hint: Omit it from the simp argument list.
  [apply] simp [Complex.smul_im]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: NSFormalization/Source/RealSobolev.lean:90:47: This simp argument is unused:
  Complex.smul_im

Hint: Omit it from the simp argument list.
  [apply] simp [Complex.smul_re]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: NSFormalization/Source/RealSobolev.lean:90:64: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
⚠ [9322/9353] Replayed NSFormalization.Paper3.SpatiallyCompactTime
warning: NSFormalization/Paper3/SpatiallyCompactTime.lean:88:19: `ContinuousLinearMap.sub_apply` has been deprecated: Use `sub_apply` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.sub_apply` to `sub_apply x`).
⚠ [9329/9353] Replayed NSFormalization.Paper3.RealPositiveDensity
warning: NSFormalization/Paper3/RealPositiveDensity.lean:67:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:76:63: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:88:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:100:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
⚠ [9332/9353] Replayed NSFormalization.Paper3.RealVectorPositiveDensity
warning: NSFormalization/Paper3/RealVectorPositiveDensity.lean:29:5: Variable name `hc` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hc

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [9342/9353] Replayed NSFormalization.Source.PacketForceExtension
warning: NSFormalization/Source/PacketForceExtension.lean:44:25: `if_pos` has been deprecated: Use `ite_eq_left` instead
⚠ [9345/9353] Replayed NSFormalization.Source.ViscosityPacket
warning: NSFormalization/Source/ViscosityPacket.lean:34:63: This simp argument is unused:
  Function.comp_def

Hint: Omit it from the simp argument list.
  [apply] simp [viscosityVelocity, dilateField, viscosityHomeomorph, Prod.map]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
Build completed successfully (9353 jobs).
```

### Direct elaboration and closure

These commands each exited 0 with exactly zero output:

```sh
LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T10/Parseval.lean
LEAN_NUM_THREADS=6 lake env lean ../research/T10/probes/parseval_closes.lean
```

### Axiom audit

Command:

```sh
LEAN_NUM_THREADS=6 lake env lean ../research/T10/axioms_parseval.lean
```

Exit 0, exact output:

```text
'NSFormalization.Section3.T10.periodicTorusMeasure_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T10.memLp_torusLift_component' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.fourier_repr_toLp' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.periodicFourierCoeff_real_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.parseval_backward' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.norm_toLp_sq_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.datum_component_norm_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.datum_norm_sq_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.parseval_forward' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Repository check

Command:

```sh
. scripts/lean-env.sh
LEAN_NUM_THREADS=6 make check
```

Exit 0.  The raw output is 42,730 lines / 1,759,574 bytes, SHA-256
`9495627ca894d5268bdfe68ad80dd1431508075521d44f5cdd512aae80748648`.
The middle is the mechanically generated registered-contract closure list.
The exact head and tail are pasted separately rather than inserting 1.76 MB
into the review.  Exact head:

```text
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 45,
  "source_counts": {
    "formalization": 552,
    "vendor/NavierStokesAndEuler": 2486,
    "vendor/HeliCorgi": 129
  },
  "source_manifest_entries": 2975,
  "missing_copied_imports": [],
  "citation_interfaces_reachable": [],
  "tokens_in_copied_umbrella_closure": [
    {
      "module": "NSFormalization.Paper1.BoundaryCorollary",
      "path": "formalization/NSFormalization/Paper1/BoundaryCorollary.lean",
      "line": 90,
      "token": "sorry"
    }
  ],
  "tracked_cache_free": true,
  "source_hashes_match": false
}
Explicit axiom/admission tokens, all copied sources: 11
python3 experiments/check_contracts.py
{
  "registered_contracts": 37,
  "closures": {
    "R41.threshold_arithmetic": [
```

Exact tail:

```text
      "NavierStokes.WeightedQuotients",
      "NavierStokes.WeightedRadialPrimitive",
      "NavierStokes.ZerothStressIdentity",
      "TestSupport.Axioms",
      "Tests.CompletedDensity"
    ]
  },
  "base_compatibility_checked": false,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.044s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
```

The copied-source `BoundaryCorollary.lean` token shown by the global plan report
is pre-existing and is not in this module's dependency axioms; the direct axiom
audit above remains exactly standard.

### Diff and hygiene

`git diff --check origin/erenup/integration-section3...HEAD` exited 0 with zero
output.  Before the reviewer files, the exact base-range name list was:

```text
formalization/NSFormalization/Section3/T10/Parseval.lean
research/T10/ATTEMPTS_PARSEVAL.md
research/T10/REPORT_286.md
research/T10/axioms_parseval.lean
research/T10/probes/parseval_closes.lean
```

Both hygiene searches produced zero matches/output (`rg` status 1 is its
normal no-match status):

```sh
rg -n --glob '*.lean' '\b(sorry|admit|axiom|native_decide)\b' \
  formalization/NSFormalization/Section3/T10/Parseval.lean \
  research/T10/probes/parseval_closes.lean \
  research/T10/axioms_parseval.lean \
  research/T10/probes/rev286_parseval_p1_mutation.lean
rg -n --glob '*.lean' 'set_option\s+maxHeartbeats|maxHeartbeats' \
  formalization/NSFormalization/Section3/T10/Parseval.lean \
  research/T10/probes/parseval_closes.lean \
  research/T10/axioms_parseval.lean \
  research/T10/probes/rev286_parseval_p1_mutation.lean
```

Because the base-range diff contains no `verification/` path, the conditional
`scripts/gates.sh` and
`check_contracts.py --base-ref origin/erenup/integration-section3` gates do not
apply.  No git-mutating command was run.

Fixes: none.
