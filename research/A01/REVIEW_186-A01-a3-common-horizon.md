ACCEPT

## 1. What the lane claims

The lane claims a conditional, not unconditional, A3-U reduction: assuming the single named
proposition `MildUniqueness`, the order-six ordinary carrier can be used for every order.  That is
what the worker report says at `research/A01/REPORT_186.md:5-10` and again, with the remaining gap
made explicit, at `research/A01/REPORT_186.md:98-106`.

Statement fidelity is good.

- The four exact statements printed in the worker report match the source: `MildUniqueness` is
  `formalization/NSFormalization/Section4/A01/CommonHorizon.lean:156-162`, the invariant-bound
  result is `:166-199`, the unrestricted-bound result is `:202-221`, and the lane-178 export is
  `:224-249`.  No reported theorem name or conclusion is missing.
- `MildUniqueness` is exactly the requested order-six statement: state space
  `SobolevSpace 1 7`, force space `SobolevSpace 1 6`, arbitrary datum `a`, arbitrary continuous
  force `f`, and two fixed points of the same `quadraticDuhamel` map on all of `[0,S]`
  (`CommonHorizon.lean:156-162`).  It has no ball, invariance, divergence, small-horizon, or
  canonical-datum premise.  `hS : 0 < S` rules out an empty interval.  There is no ENNReal
  `.toReal` premise or other `top`-vacuity device.
- The exact proof-instance choices match the consumer: both equations in `MildUniqueness` use
  `hS.le` and `le_rfl` (`CommonHorizon.lean:160-161`), while the order-six solution and the
  lowered solution are supplied with precisely those proofs at `:189-195`.  The direct
  application at `:195` typechecks, so there is no hidden proof-parameter mismatch with
  `localTheory_on_prescribed_horizon_of_boundInv`.
- Every named premise is used honestly.  `ha` enters the prescribed-horizon constructor at
  `CommonHorizon.lean:185-188`; `hb` enters the enlarged-radius bound at `:188`; `huniq` identifies
  the two order-six paths at `:195`; and `hfs` supplies exactly the force-smoothness conjunct at
  `:196`.  The internal `max (R q) ‖u₀‖` at `:184-188` repairs the continuation API's radius
  side conditions without strengthening the theorem statement.
- The canonical-zero fixed-point premises are inhabited, and `MildUniqueness` specializes to
  them without an instance mismatch.  The checks are
  `research/A01/probes/rev186_compatibility.lean:43-65`; the probe typechecks with zero output.
- The paper supports the intended mathematics: `paper/sections/appendix-a-local-theory.tex:62-70`
  states local existence, uniqueness, and one interval shared by every spatial order, and
  `:71-76` gives the all-order time-regularity bootstrap.  Thus a common carrier obtained by
  fixed-order mild uniqueness is the requested content, not a weakened surrogate.

Lane 178 compatibility is exact.  At the commit named by the brief, the consumer's `hall` is
`afc5422:formalization/NSFormalization/Section4/A01/DatumPathSmooth.lean:736-745`.  Its binder order
and terms are identical to `CommonHorizon.lean:234-243`: `q`, `hq`, then `u₀`, `f`, `u`; the same
fixed `U`; the same `extendPath`, `ordinaryLift`, `sobolevTranslation`, `quadraticDuhamel`, and
`coefficients` spellings.  (The current lane-178 tip moved the unchanged block to `:717-726`.)
The token-for-token local copy and an actual application of lane 186's output are at
`research/A01/probes/rev186_compatibility.lean:14-41`; it typechecks with zero output.

## 2. What is in Lean

The mathematical heart is proved rather than assumed.

- Heat commutation is `restrict_heat` (`CommonHorizon.lean:20-25`), using the real restriction
  identity `value_restrictOperator` from `Euler/SobolevRestriction.lean:31-32` and the heat value
  formula from `Euler/SobolevHeat.lean:32-35`.
- The actual forced coefficient/source commutation is `restrict_forced_source`
  (`CommonHorizon.lean:30-51`).  Its proof expands the genuine advection, proves equality of the
  quadratic values, and then transports the full Leray-projected `f - (u·∇)u`; it does not assume
  a source-compatibility hypothesis.
- The ordinary Duhamel integral commutes with restriction in `restrict_duhamel`
  (`CommonHorizon.lean:54-63`).  The gained path commutes in `restrict_mildPath` (`:68-82`), using
  the proved vendor truncation formula `Euler/GainedMildFormula.lean:43-50`.
- `quadraticDuhamel_eq_mildPath` identifies the full fixed-point expression with the gained path
  (`CommonHorizon.lean:92-99`).  In `lower_forced_mild`, restriction of the canonical force is
  proved inline at `:121-125`, restriction of the evaluated coefficient/source at `:127-133`, and
  restriction of the canonical datum by the real theorem `restrict_sobolev`
  (`Euler/SmoothFieldSobolevTime.lean:44-50`) at `CommonHorizon.lean:146-150`.  The resulting
  lowered path is therefore a fixed point of the order-six map with exactly
  `sobolevPath F hF 6` and `ordinarySobolev 7 a.toLp a.translation_contDiff`, not merely some
  force and datum (`CommonHorizon.lean:104-151`).
- The common-carrier construction chooses the order-six output once (`CommonHorizon.lean:189-190`),
  lowers each order-`q` solution (`:193-194`), applies fixed-order uniqueness (`:195`), and retains
  the original high-order solution, its angular invariance, canonical force, and canonical datum
  (`:196-199`).  The unrestricted result is the honest `HasAprioriBound.toInv` specialization
  (`:202-221`), and `compatible_carriers_hall` chooses the canonical existential witnesses
  explicitly (`:244-249`).

The eleven public declarations are present at `CommonHorizon.lean:20`, `:30`, `:54`, `:68`, `:85`,
`:92`, `:104`, `:156`, `:166`, `:202`, and `:224`.  The audit lists exactly those eleven at
`research/A01/axioms_a3_common_horizon.lean:13-23`; every one prints exactly
`[propext, Classical.choice, Quot.sound]`.  Its two positive-horizon zero examples are at
`:25-39` and `:41-74`.

Hygiene is clean.  The only Lean module in the branch diff is the new
`CommonHorizon.lean`; no pre-existing Lean module, vendor file, contract, or build configuration
was modified.  There is no whole-word `sorry`, `admit`, `axiom`, or `native_decide` in the module
or audit.  The three local heartbeat settings are exactly `400000`, each attached to one
declaration and preceded by an explanatory comment (`CommonHorizon.lean:27-30`, `:65-68`,
`:101-104`).

The substantive negative mutation is
`research/A01/probes/rev186_negative_force_sign.lean:14-28`: it changes the lower equation's
canonical force from `sobolevPath F hF q` to its negative.  Lean rejects the attempted reuse of
`lower_forced_mild` with the expected force mismatch, so the proof is sensitive to the canonical
force and not merely to the presence of an argument.

## 3. Gaps

The single analytic gap is exactly the named input `MildUniqueness`; it is a `def` of a
proposition and an explicit theorem parameter, not an added axiom (`CommonHorizon.lean:153-166`).
The all-order a-priori bounds and `hfs` also remain inputs, as the brief required.  The records are
honest about this at `research/A01/A3_SPLIT.md:59` and `research/A01/B1_LADDER.md:98-106`.

The required whole-tree negative search was run:

```text
$ grep -rnE 'MildUniqueness|mild_solution_unique|unique.*mild|mild.*unique|quadratic.*unique|unique.*quadratic' formalization/NSFormalization/Section4
formalization/NSFormalization/Section4/HeliCorgiPort.lean:28:/-- Local existence with closed-ball uniqueness for the R³ endpoint-safe projected mild
formalization/NSFormalization/Section4/A01/CommonHorizon.lean:6:input is fixed-order, unrestricted mild uniqueness, explicitly named below. -/
formalization/NSFormalization/Section4/A01/CommonHorizon.lean:156:def MildUniqueness : Prop :=
formalization/NSFormalization/Section4/A01/CommonHorizon.lean:166:theorem compatible_carriers_of_boundsInv (huniq : MildUniqueness)
formalization/NSFormalization/Section4/A01/CommonHorizon.lean:202:theorem compatible_carriers_of_bounds (huniq : MildUniqueness)
formalization/NSFormalization/Section4/A01/CommonHorizon.lean:224:theorem compatible_carriers_hall (huniq : MildUniqueness)
formalization/NSFormalization/Section4/A01/ContinuationInvariant.lean:12:No *global* mild uniqueness is used.  `EulerBoundedMildContinuation.exists_global_mild_of_bound`
formalization/NSFormalization/Section4/A01/ContinuationInvariant.lean:15:continuation's own windows are the uniqueness regime of `mild_solution_unique`.**  On each such
formalization/NSFormalization/Section4/A01/ContinuationInvariant.lean:140:  have huv := mild_solution_unique T hT (heatKernel 1 q ν hν) (parabolicKernelBound ν)
formalization/NSFormalization/Section4/A01/Continuation.lean:53:No *global* mild uniqueness is required to remove it — that framing (in an earlier draft of
formalization/NSFormalization/Section4/A01/Continuation.lean:63:  uniqueness regime of `mild_solution_unique`.**  `kernelMass S · L < 1` being false for large
```

This confirms there is no existing theorem in the full Section4 tree with the exact forced
cylinder statement.

The worker's vendor theorem is
`EulerVolterraConvolution.mild_solution_unique` at
`vendor/NavierStokesAndEuler/Euler/VolterraUniqueness.lean:20-43`.  It requires both path bounds
and the smallness condition `kernelMass T k * L < 1` at `:24-31`.  For this equation the needed
Lipschitz constant on an `R`-ball is `C.ballLipschitz R`, and the actual estimate is
`Coefficients.apply_sub_bound` at
`vendor/NavierStokesAndEuler/Euler/QuadraticCoefficients.lean:67-73`.  Arbitrarily short
contraction horizons are supplied by `exists_positive_time_budget` at
`Euler/VolterraUniqueness.lean:68-92`.  The existing order-`q` window application at
`formalization/NSFormalization/Section4/A01/ContinuationInvariant.lean:89-101,140-145` verifies
that these pieces already compose on a short interval.

Accordingly, `MildUniqueness` is mathematically true in this carrier and is feasible for lane
188 by continuity/patching.  Compactness bounds both continuous competitors; choose a common
`R`, obtain a uniform short contraction horizon from the preceding lemmas, restart both paths at
each already-agreed endpoint, and iterate finitely to `S`.  A compiled proof template already
exists for another carrier in
`formalization/FormalPatched/EndpointSafeTwoSpaceUniqueness.lean:117-224`: it takes compact bounds
at `:123-131`, chooses the short contraction horizon at `:132-146`, restarts and applies local
uniqueness at `:147-217`, then closes by the Archimedean step at `:218-224`.  Its generic contract
does not directly encode the present time-dependent forced `Coefficients`, so lane 188 still
needs the corresponding forced restart identity (the existing forward pasting theorem is
`vendor/NavierStokesAndEuler/Euler/QuadraticMildPasting.lean:38-58`).  This is a formal adapter/proof
task, not a missing analytic estimate or a reason to strengthen `MildUniqueness`.

The worker also correctly declined the classical PDE uniqueness detour:
`formalization/NSFormalization/Source/OrdinaryViscousUniqueness.lean:26-47` requires smooth paths,
time derivatives, pressures, divergence, and pointwise PDE equations, which are downstream
constructor obligations here.

## 4. Commands and results

All Lean commands sourced `scripts/lean-env.sh`, used `LEAN_NUM_THREADS=6`, and ran `lake` only
from `verification/`.

Exact module build:

```text
$ lake build NSFormalization.Section4.A01.CommonHorizon
Build completed successfully (3945 jobs).
```

Quiet build and direct module check:

```text
$ lake -q build NSFormalization.Section4.A01.CommonHorizon
[no output; exit 0]
$ lake env lean ../formalization/NSFormalization/Section4/A01/CommonHorizon.lean
[no output; exit 0]
```

Axiom audit (exit 0; the two examples also elaborated):

```text
'NSFormalization.Section4.A01.restrict_heat' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.restrict_forced_source' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.restrict_duhamel' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.restrict_mildPath' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.commonSource' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.quadraticDuhamel_eq_mildPath' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.lower_forced_mild' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.MildUniqueness' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.compatible_carriers_of_boundsInv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.compatible_carriers_of_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.compatible_carriers_hall' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`make check` was first run unfiltered and exited 0; it emits a 25,427-line generated architecture
closure listing.  The exact terminal tail from the pipefail-protected rerun was:

```text
.............
----------------------------------------------------------------------
Ran 13 tests in 0.046s

OK
      "NavierStokes.ResidualCalculus",
      "NavierStokes.SpatialCurl",
      "TestSupport.Axioms",
      "Tests.HomogeneousNorm"
    ]
  },
  "base_compatibility_checked": false,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.
```

`make test` exited 0.  It replayed pre-existing linter warnings only; the exact final output was:

```text
ℹ [10515/10528] Replayed Tests.HomogeneousNorm
info: Tests/HomogeneousNorm.lean:17:0: Contract BlowupDensity.Tests.checkedHomogeneousNorm: checked; standard logical axioms only
ℹ [10520/10528] Replayed Tests.HomogeneousPartialV2
info: Tests/HomogeneousPartialV2.lean:35:0: Contract BlowupDensity.Tests.checkedHomogeneousPartialV2: checked; standard logical axioms only
ℹ [10523/10528] Replayed Tests.MaximalPartialV2
info: Tests/MaximalPartialV2.lean:24:0: Contract BlowupDensity.Tests.checkedMaximalPartialV2: checked; standard logical axioms only
ℹ [10526/10528] Replayed Tests.InsertionLifespanV2
info: Tests/InsertionLifespanV2.lean:32:0: Contract BlowupDensity.Tests.checkedInsertionLifespanV2: checked; standard logical axioms only
ℹ [10527/10528] Replayed Tests.TameProduct
info: Tests/TameProduct.lean:14:0: Contract BlowupDensity.Tests.checkedTameProduct: checked; standard logical axioms only
ℹ [10528/10528] Replayed Tests.EnergyAbsorptionPartialV3
info: Tests/EnergyAbsorptionPartialV3.lean:41:0: Contract BlowupDensity.Tests.checkedEnergyAbsorptionPartialV3: checked; standard logical axioms only
```

Positive compatibility/non-vacuity probe:

```text
$ lake env lean ../research/A01/probes/rev186_compatibility.lean
[no output; exit 0]
```

Negative force-sign mutation (expected exit 1):

```text
../research/A01/probes/rev186_negative_force_sign.lean:28:2: error: Type mismatch
  lower_forced_mild hp hq h hν hS a F hF u hu
has type
  have v := (ContinuousLinearMap.compLeftContinuous ℝ (↑(Icc 0 S)) (restrictOperator 1 ⋯)) u;
  ∀ (t : ↑(Icc 0 S)),
    v t = quadraticDuhamel 1 ν hν hS ⋯ (coefficients 1 hq (sobolevPath F hF q)) (ordinarySobolev (q + 1) a.toLp ⋯) v t
but is expected to have type
  let v := (ContinuousLinearMap.compLeftContinuous ℝ (↑(Icc 0 S)) (restrictOperator 1 ⋯)) u;
  ∀ (t : ↑(Icc 0 S)),
    v t = quadraticDuhamel 1 ν hν hS ⋯ (coefficients 1 hq (-sobolevPath F hF q)) (ordinarySobolev (q + 1) a.toLp ⋯) v t
```

Hygiene commands:

```text
$ rg -n --pcre2 '\b(sorry|admit|axiom|native_decide)\b' formalization/NSFormalization/Section4/A01/CommonHorizon.lean research/A01/axioms_a3_common_horizon.lean
[no output; exit 1, meaning no matches]
$ git diff --check origin/erenup/integration...HEAD
[no output; exit 0]
$ git diff --name-only origin/erenup/integration...HEAD -- verification
[no output; exit 0]
```

The branch diff before reviewer-created probes/report was exactly:

```text
formalization/NSFormalization/Section4/A01/CommonHorizon.lean
research/A01/A3_SPLIT.md
research/A01/ATTEMPTS_A3_COMMON_HORIZON.md
research/A01/B1_LADDER.md
research/A01/REPORT_186.md
research/A01/axioms_a3_common_horizon.lean
```

Because `verification/` was untouched, the brief's conditional `scripts/gates.sh` and
`check_contracts.py --base-ref origin/erenup/integration` gates are not applicable.  The required
unconditional module build, direct Lean check, axiom audit, `make check`, and lead-requested
`make test` all passed.

Fixes required: none.
