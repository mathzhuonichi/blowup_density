ACCEPT

## 1. What the lane claims

The worker report claims the explicit Peetre constant, its positivity, the base
Japanese-bracket inequality, its nonnegative `Real.rpow` lift, the all-real-order
weight-ratio theorem, the `peetreConst` restatement, and two bridges to the D01
`sobolevBesselWeight` spelling (`research/T22/REPORT_386.md:5-9`).  It also claims
that the module/probe compile, all seven theorem audits have exactly the standard
three axioms, and `make check` passes (`research/T22/REPORT_386.md:17-18`).

The mathematical target is the all-`s : Real` ratio with explicit constant
`2 ^ (|s| / 2)` (`research/T22/T22_SPLIT.md:102-106`).  The paper states the
equivalent ratio estimate and its use in the Fourier-convolution/Young argument
at `paper/sections/03-torus.tex:616-624`.

## 2. What is in Lean

Statement fidelity is complete.

- `peetreConst s := 2 ^ (|s| / 2)` and
  `peetreConst_pos (s) : 0 < peetreConst s` occur exactly at
  `formalization/NSFormalization/Section3/T22/WeightRatio.lean:43-47`.
- `one_add_normSq_le (xi eta)` has exactly
  `1 + ||xi||^2 <= 2 * (1 + ||eta||^2) * (1 + ||xi-eta||^2)` at
  `formalization/NSFormalization/Section3/T22/WeightRatio.lean:49-61`.
- `rpow_base_le {t} (ht : 0 <= t) (xi eta)` has the claimed nonnegative lift,
  with no extra premise, at
  `formalization/NSFormalization/Section3/T22/WeightRatio.lean:63-78`.
  Its sole hypothesis `ht` is used to establish `0 <= t/2` and hence rpow
  monotonicity (`:71-75`).
- `weight_ratio_le (s) (xi eta)` is exactly the brief's theorem, for arbitrary
  real `s` and arbitrary `Space` points and with no hypotheses, at
  `formalization/NSFormalization/Section3/T22/WeightRatio.lean:80-90`.
  The nonnegative and negative branches are both implemented (`:91-126`), so
  this is not made vacuous by a sign guard or unused binder.
- `weight_ratio_le_const` is the identical inequality with `peetreConst s` at
  `formalization/NSFormalization/Section3/T22/WeightRatio.lean:128-133`.
- `sobolevBesselWeight_norm` has exactly the reported norm identity at
  `formalization/NSFormalization/Section3/T22/WeightRatio.lean:135-141`.
- `sobolevBesselWeight_norm_ratio_le` has exactly the three-factor D01-spelled
  inequality at
  `formalization/NSFormalization/Section3/T22/WeightRatio.lean:143-152`.

This is the requested mathematics: the paper's denominator is strictly positive,
and moving it to the right gives the delivered multiplication form.  The
repository weight really is the complex-valued real scalar
`((1 + ||xi||^2) ^ (s/2) : Real)`
(`formalization/NSFormalization/Paper3/SobolevHilbertModel.lean:23-25`), while
D01 identifies this same spelling as its inhomogeneous weight
(`formalization/NSFormalization/Section4/D01/FiniteOrderDatum.lean:16-23` and
`:59-62`).  Thus an `ENNReal` version is neither the D01 spelling nor needed by
U-A3; the complex norm bridge supplies the real nonnegative factor directly.

The related lattice theorem is indeed `torusWeightPeetre` at
`formalization/NSFormalization/Section3/T11/PairingBound.lean:233-263` and is
consumed in `formalization/NSFormalization/Section3/T12/TameProduct.lean:656-663`.
The new module cites the defining location accurately at
`formalization/NSFormalization/Section3/T22/WeightRatio.lean:26-31`.

There are no interval, `top.toReal`, existence, or named-`Prop` hypotheses in
the main theorem.  A concrete nonzero instance (`s = 2`, `xi = 2 e_0`,
`eta = e_0`) typechecks in `research/T22/probes/rev386_nonvacuity.lean:6-17`.

Hygiene also passes.  Against `origin/erenup/integration-section3`, the only
formalization module is a new file, not a modification:

```text
A formalization/NSFormalization/Section3/T22/WeightRatio.lean
A research/T22/ATTEMPTS_UA1.md
A research/T22/REPORT_386.md
M research/T22/T22_SPLIT.md
A research/T22/axioms_ua1.lean
A research/T22/probes/weight_ratio_closes.lean
```

There is no `sorry`, `admit`, `axiom` declaration, or `native_decide` in the
delivered Lean; the sole singular-token grep hit is the prose phrase
`Transitive-axiom audit` in `research/T22/axioms_ua1.lean:4`.  There is no
`maxHeartbeats` setting.  `git diff --check` exits 0.

## 3. Gaps

No U-A1 mathematical gap remains.  The report explicitly declares none
(`research/T22/REPORT_386.md:14-15`), and its remaining items are only
pin-specific identifier notes documented at
`research/T22/ATTEMPTS_UA1.md:30-44`.  Therefore there is no claimed
"not in the Section4 tree" lemma to grep; the mandatory missing-lemma audit is
not applicable.

The constant mutation is load-bearing.  In
`research/T22/probes/rev386_mutation.lean:8-21`, changing the main constant base
from `2` to `1` at `s = 2`, `xi = 2 e_0`, `eta = e_0` changes the numerical
claim from a true bound to `5 <= 4`.  Lean rejects it after normalization with
the expected contradiction:

```text
../research/T22/probes/rev386_mutation.lean:16:32: error: unsolved goals
hdiff : 2 • coordinateVector 0 - coordinateVector 0 = coordinateVector 0
⊢ False
MUTATION_STATUS=1
```

No fixes are required.

## 4. Commands and results

All Lean commands were run after `. ../scripts/lean-env.sh`, from
`verification/`, with `LEAN_NUM_THREADS=6`.

```text
$ LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T22.WeightRatio
Build completed successfully (8790 jobs).
build_exit=0

$ LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T22/WeightRatio.lean
module_exit=0

$ LEAN_NUM_THREADS=6 lake env lean ../research/T22/probes/weight_ratio_closes.lean
probe_exit=0
```

The last two Lean invocations produced no diagnostic output.  The axiom audit
produced exactly:

```text
'NSFormalization.Section3.T22.peetreConst_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T22.one_add_normSq_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T22.rpow_base_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T22.weight_ratio_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T22.weight_ratio_le_const' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T22.sobolevBesselWeight_norm' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T22.sobolevBesselWeight_norm_ratio_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
axioms_exit=0
```

The reviewer non-vacuity probe was silent and successful:

```text
$ LEAN_NUM_THREADS=6 lake env lean ../research/T22/probes/rev386_nonvacuity.lean
NONVACUITY_STATUS=0
```

`make check` was run from the repository root and exited 0.  Its JSON closure
listing is 46,316 lines, so the exact beginning and end are recorded rather
than duplicating 1.9 MB into this review:

```text
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 45,
  "source_counts": {
    "formalization": 611,
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
...
  "base_compatibility_checked": false,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.046s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
MAKE_CHECK_STATUS=0
```

No path under `verification/` appears in the base diff.  Under the review rule,
`scripts/gates.sh` and
`python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3`
are therefore conditional gates and were not run.  The unconditional
`make check` did run `experiments/check_contracts.py` successfully, as shown
above.
