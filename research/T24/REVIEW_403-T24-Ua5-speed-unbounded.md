ACCEPT

## 1. What the lane claims

`research/T24/REPORT_403.md:8` claims exactly this theorem, present at
`formalization/NSFormalization/Section3/T24/AffineSpeed.lean:24`:

```lean
theorem speed_unbounded {U : VelocityField} (c : Space) (r τ₀ τ₁ : ℝ)
    (hτ₁ : τ₁ < 1) (hspeed : SpeedUnboundedAtOne U) :
    ∀ b : VelocityField, AffineAdmissible c r τ₀ τ₁ b →
      SpeedUnboundedAtOne (affineVelocity U b)
```

This is Ua5 (`research/T24/T24_SPLIT.md:109`, ledger at :182), not the full affine API.
The status edits at :111 and :203 correctly record that scope.

## 2. What is in Lean

1. **Statement fidelity passes.** Opened `paper/sections/03-torus.tex:668-696`
with `sed -n`: :670 supplies the strict window; :684-686 gives late agreement
and the same unbounded-speed limit. The conclusion matches
`research/T24/Spec.lean:1069` with the raw velocity substituted. The raw
predicate is `vendor/NavierStokesAndEuler/NavierStokes/ProblemStatement.lean:94`;
the registered copy at `verification/Contracts/V1/Packet.lean:145` has identical
quantifiers: every positive M and δ, witnesses t∈(0,1), x, 1−δ<t and M<‖U(t,x)‖.
The brief's `formalization/NSFormalization/Source/Packet.lean` does not exist;
this is a brief path error, not a lane defect.
2. **Hypotheses are honest.** `AffineBasics.lean:26` (under
`formalization/NSFormalization/Section3/T24/`) contains smoothness, compact
support, cylinder support and zero divergence, without a time-window inequality.
Its `window` at :58 requires that inequality as an input. Thus the lane uses
the explicit hypothesis allowed by the brief. At `AffineSpeed.lean:29-38`,
min δ (1−τ₁)>0 gives a witness both in the requested neighborhood and past τ₁;
`AffineBasics.lean:78` supplies precisely the equality used at
`AffineSpeed.lean:39`. No named analytic input, unused binder, extended-real
conversion, or vacuous interval is used to discharge the result. The weaker
geometric assumptions make this a valid generalization of the paper clause.
3. **Bridge and non-vacuity pass.**
`research/T24/probes/affine_speed_closes.lean:34-40` checks the copied spec
admissibility and affine velocity by `rfl`; :44-51 closes the field using
`Bindings.packet`; :55-69 constructs admissibility of b=0 and proves its
unbounded-speed conclusion. The packet is constructed at
`verification/Bindings/Packet.lean:104-130`, not assumed as an uninhabited API.
Positive viscosity can be instantiated by ν=1 and the geometry by
c=0, r=1, τ₀=1/4, τ₁=1/2. No additional non-vacuity probe was needed.
4. **Hygiene and axioms pass.** `AffineSpeed.lean:1` imports the required
canonical module without restating definitions. The only new named theorem
is at :24; `research/T24/axioms_ua5.lean:5` prints exactly the three standard
axioms. Forbidden-token/maxHeartbeats scan of the three delivered Lean files
returns no matches. No existing Lean module or `verification/` file changed;
the only modified existing record is the specifically requested split ledger.
CI covers changed formalization modules through
`experiments/build_changed_lean.py:18-20` and `.github/workflows/contracts.yml:81`.
5. **Substantive mutation fails as expected.**
`research/T24/probes/rev403_negative_speed.lean:27-29` expands the original
conclusion and changes its speed bound from M<‖U+b‖ to M<−‖U+b‖, retaining all
hypotheses and the original proof. Lean fails exactly at :42, where the final
positive-norm inequality cannot prove the negative-norm inequality. This is
a sign mutation of the statement, not a missing argument. It is false for
positive M because norms are nonnegative.

## 3. Gaps

No blocking gap or required fix. `research/T24/REPORT_403.md:41-42` explicitly
leaves Ua4 and Ua6 outside scope and makes no claim of a missing tree lemma.
Nevertheless, searched the entire Section4 tree with `grep -rnE
'force_smooth|force_support|energy_finite|affineForce|AffineAdmissible|speed_unbounded'
formalization/NSFormalization/Section4`. The five hits are
`D01/ForceClass.lean:351,415,420,421` and `I01/Quiet.lean:60`; they concern
packet/correction support, not an affine Ua4/Ua6 theorem. A narrower search
for `affineForce|AffineAdmissible|energy_finite` has no matches (exit 1).
These searches do not assert that no differently named reusable analysis exists.

The transient namespace error recorded at `research/T24/REPORT_403.md:48`
is resolved: the final probe imports `Contracts.V1.Data` at :2 and compiles.
The module emits no warnings; Lake itself emits its usual successful-build
summary. `scripts/gates.sh` and the base-ref contract check are conditional
on changes to `verification/` in this review brief; that condition is false.

## 4. Commands and results

All Lean commands below ran after `. scripts/lean-env.sh`, with
`LEAN_NUM_THREADS=6` and Lake only in `verification/`. Exact outputs follow;
for the very large `make check` JSON dump only the first 20 and last 40 lines
are reproduced, with the omission explicitly marked. Its exit status is 0.
The pre-existing broad source scan includes copied-source admissions outside
this lane; the new theorem's kernel axiom audit is clean.

`lake build NSFormalization.Section3.T24.AffineSpeed` (cwd `verification`), exit 0:

```text
Build completed successfully (3007 jobs).
```

`lake env lean ../formalization/NSFormalization/Section3/T24/AffineSpeed.lean` (cwd `verification`), exit 0:

```text
(0 output)
```

`lake env lean ../research/T24/probes/affine_speed_closes.lean` (cwd `verification`), exit 0:

```text
(0 output)
```

`lake env lean ../research/T24/axioms_ua5.lean` (cwd `verification`), exit 0:

```text
'NSFormalization.Section3.T24.speed_unbounded' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`lake env lean ../research/T24/probes/rev403_negative_speed.lean` (cwd `verification`), exit 1:

```text
../research/T24/probes/rev403_negative_speed.lean:42:4: error: Type mismatch
  ht_large
has type
  M < ‖U (t, x)‖
but is expected to have type
  M < -‖U (t, x)‖
```

`make check` (cwd `.`), exit 0:

```text
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 45,
  "source_counts": {
    "formalization": 628,
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
[... 47503 bulk JSON lines omitted ...]
      "NavierStokes.TransitionRamp",
      "NavierStokes.TransportPrimitive",
      "NavierStokes.TrueConeLoop",
      "NavierStokes.UniformAngularReset",
      "NavierStokes.UniformBlockBounds",
      "NavierStokes.UniformCone",
      "NavierStokes.UniformFourierAlias",
      "NavierStokes.UniformHarmonicInteraction",
      "NavierStokes.UniformPrimaryWeights",
      "NavierStokes.ValidBandGluing",
      "NavierStokes.ValidDyadicBandCover",
      "NavierStokes.VariableGaugeMean",
      "NavierStokes.ViscousPropagator",
      "NavierStokes.VolterraAnalyticBounds",
      "NavierStokes.VolterraParity",
      "NavierStokes.VolterraRegularity",
      "NavierStokes.WaveEdgeExtension",
      "NavierStokes.WaveEnvelopeTransport",
      "NavierStokes.WaveInteractionBounds",
      "NavierStokes.WaveStateRegularity",
      "NavierStokes.WeightedClasses",
      "NavierStokes.WeightedODEJets",
      "NavierStokes.WeightedQuotients",
      "NavierStokes.WeightedRadialPrimitive",
      "NavierStokes.ZerothStressIdentity",
      "TestSupport.Axioms",
      "Tests.Localization"
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

`git diff --name-only origin/erenup/integration-section3...HEAD` (cwd `.`), exit 0:

```text
formalization/NSFormalization/Section3/T24/AffineSpeed.lean
research/T24/ATTEMPTS_UA5.md
research/T24/REPORT_403.md
research/T24/T24_SPLIT.md
research/T24/axioms_ua5.lean
research/T24/probes/affine_speed_closes.lean
```

`git diff --check` (cwd `.`), exit 0:

```text
(0 output)
```

Additional read-only checks:

```sh
rg -n '\b(sorry|admit|axiom|native_decide)\b|maxHeartbeats' formalization/NSFormalization/Section3/T24/AffineSpeed.lean research/T24/probes/affine_speed_closes.lean research/T24/axioms_ua5.lean
```

No output (exit 1: no matches). Git HEAD: `19943095`.
Only this new review and `rev403_negative_speed.lean` were written by the reviewer;
no git state changes or lane-source edits were made.

Fixes: none.
