ACCEPT-WITH-NOTES

## 1. What the lane claims

The theorem inventory in `research/A01/REPORT_168.md:8-102` is an exact copy of
the declarations in Lean.  The correspondence is:

| Reported declaration | Lean source |
|---|---|
| `pressureOfVelocity_basepoint` | `formalization/NSFormalization/Section4/A01/ConstructorPressure.lean:64-66` |
| `pressureGradientOfVelocity_memLp` | `formalization/NSFormalization/Section4/A01/ConstructorPressure.lean:70-74` |
| `pressureGradient_pressureOfVelocity` | `formalization/NSFormalization/Section4/A01/ConstructorPressure.lean:78-84` |
| `pressureGradient_pressureOfVelocity_lerayComplement` | `formalization/NSFormalization/Section4/A01/ConstructorPressure.lean:90-120` |
| `pressureGradient_pressureOfVelocity_lerayComplement_order` | `formalization/NSFormalization/Section4/A01/ConstructorPressure.lean:127-150` |
| `pressure_gradient_memLp_slice` | `formalization/NSFormalization/Section4/A01/ConstructorPressure.lean:154-167` |
| `pressure_gradient_memLp` | `formalization/NSFormalization/Section4/A01/ConstructorPressure.lean:170-184` |
| `pressureOfVelocity_slice_smooth` | `formalization/NSFormalization/Section4/A01/ConstructorPressure.lean:189-195` |
| `pressure_smooth_of_velocity_smooth` | `formalization/NSFormalization/Section4/A01/ConstructorPressure.lean:201-214` |
| `momentum_of_projected` | `formalization/NSFormalization/Section4/A01/ConstructorPressure.lean:218-241` |
| `pressureOfVelocity_zero` | `formalization/NSFormalization/Section4/A01/ConstructorPressure.lean:245-250` |

The three definitions summarized at `research/A01/REPORT_168.md:107-118` are
also exact: `momentumResidualOfVelocity`, `pressureGradientOfVelocity`, and
`pressureOfVelocity` are defined at
`formalization/NSFormalization/Section4/A01/ConstructorPressure.lean:50-61`.

The mathematical target is correct at the datum level.  The paper states
`∂ₜu-νΔu=-P∇·(u⊗u)+Pf` and
`∇p=(I-P)(f-∇·(u⊗u))` at
`paper/sections/02-preliminaries.tex:80-92`, then derives curl-freeness and the
radial potential at `paper/sections/02-preliminaries.tex:93-100`.  The lane sets

```text
R = f - (u·∇)u + νΔu,
G = R - ∂ₜu.
```

Thus the genuine projected identity `∂ₜu = R - (I-P)R` gives
`G=(I-P)R`.  This is precisely the datum hypothesis at
`ConstructorPressure.lean:97-99`, and the conclusion is the correct
`IsSobolevDatum` form at `:100-102`.  The order-`m` lift uses the actual tree
commutation theorem `lerayComplement_lowerVectorL`
(`formalization/NSFormalization/Section4/D01/LerayLowering.lean:150-188`) and
datum reflection theorem `isSobolevDatum_lower_iff` (`:210-223`).  The cited
consumer-side pin really does require an already constructed
`ClassicalSolutionR` (`formalization/NSFormalization/Section4/D01/PressureJets.lean:87-108`).

There is no hidden `⊤.toReal`, positivity, or post-datum constant choice.  The
interval theorems are valid for every `T`; they are not proved by choosing an
empty interval.  The reviewer probe gives a positive-horizon instance on
`Ioo 0 1` at `research/A01/probes/rev168_projected_redundant.lean:53-62`.
The lane's zero-force/zero-velocity instance is also present in the module at
`ConstructorPressure.lean:243-250` and in the conformance file at
`research/A01/axioms_pressure_p3.lean:21-25`.

## 2. What is in Lean

### Circularity

The construction is **not logically circular**, but it is still conditional on
unproved supply-side facts.

`pressureOfVelocity` uses only the candidate `velocity`, `f`, and the term
`temporalDerivative velocity`; it assumes neither an existing pressure nor a
classical momentum equation (`ConstructorPressure.lean:50-61`).  The upstream
`temporalDerivative` is the two-sided Fréchet derivative of the time slice
(`vendor/NavierStokesAndEuler/NavierStokes/ProblemStatement.lean:53-56`).  At an
interior time, c3's `ContDiffOn` hypothesis gives genuine differentiability;
the lane performs that restriction at `ConstructorPressure.lean:233-236`.
At `t=0`, however, c3 is only one-sided `ContDiffOn` on `Ico 0 T`
(`formalization/NSFormalization/Section4/A02/SolutionClass.lean:121-124`), so it
does not by itself identify the global two-sided `fderiv` used by
`temporalDerivative`.  The explicit `htime`/`hjoint` obligations therefore
remain real at the endpoint.

`pressureGradient_pressureOfVelocity_lerayComplement` assumes exactly the
order-zero projected datum equation, residual and time-derivative `MemLp`,
spatial smoothness, and curl-freeness (`ConstructorPressure.lean:90-102`).  It
does not assume `∇p`, a `ClassicalSolutionR`, or the classical residual.  Its
proof constructs the datum of `G` and then differentiates the radial potential
(`:103-120`).  This part traces cleanly to the desired mild equation once B1/T1
transports the Duhamel identity; the current mild output is still only the
`quadraticDuhamel` equality at
`formalization/NSFormalization/Section4/A01/Horizon.lean:143-153`.

There is one important naming/honesty issue.  The pointwise binder called
`hprojected` in `momentum_of_projected` (`ConstructorPressure.lean:226-229`) is
not the Leray/Duhamel equation.  Because `G` was defined as `R-∂ₜu`, that binder
follows algebraically from incompressibility and spatial differentiability.
The reviewer proved it with no pressure and no dynamics at
`research/A01/probes/rev168_projected_redundant.lean:15-32`, and proved the
momentum conclusion without that binder at `:34-51`; the probe typechecks with
zero output.  Therefore nothing in `momentum_of_projected` assumes the momentum
equation it concludes, but the worker's description that its binder is “the
pointwise projected equation” (`research/A01/ATTEMPTS_PRESSURE_P3.md:66-70`) is
misleading.  The genuine projected input is the datum equality at
`ConstructorPressure.lean:97-99`.

### Curl-free realization

`HasSymmetricJacobian G(t,·)` is not discharged.  The exact open obligations
for the c9 row and momentum row are respectively

```lean
hsym : ∀ t ∈ Ico (0 : ℝ) T,
  RadialPotential.HasSymmetricJacobian
    (fun x : Space => pressureGradientOfVelocity ν f velocity (t, x))

hgradient_symm : ∀ t ∈ Ioo (0 : ℝ) T,
  RadialPotential.HasSymmetricJacobian
    (fun x : Space => pressureGradientOfVelocity ν f velocity (t, x))
```

at `ConstructorPressure.lean:173-175` and `:223-225`.  The predicate includes
both differentiability and symmetry of all coordinate derivatives
(`formalization/NSFormalization/Section4/A01/RadialPotential.lean:98-104`).

The required whole-`Section4` search confirms the worker's gap claim.  The
closest results go only in the forward direction:

- curl-free physical field to longitudinal datum:
  `formalization/NSFormalization/Section4/D01/OrderZeroCurl.lean:478-487`;
- curl-free datum fixed by `(I-P)`:
  `formalization/NSFormalization/Section4/D01/OrderZeroCurl.lean:495-504` and
  `formalization/NSFormalization/Section4/D01/Longitudinal.lean:276-285`;
- idempotence of `(I-P)` on the abstract datum carrier:
  `formalization/NSFormalization/Section4/D01/LerayDatum.lean:280-290`.

There is no theorem in `formalization/NSFormalization/Section4` realizing an
arbitrary `lerayComplement` datum as a pointwise smooth field and proving that
representative has a symmetric Jacobian.  Consequently this is an open
constructor obligation, not a consequence already available from
`OrderZeroCurl.lean`, `LerayDatum.lean`, or `LerayLowering.lean`.

### Gauge

The gauge is fully compatible with A02.  This lane proves `p(t,0)=0`
(`ConstructorPressure.lean:63-66`).  A02's normalization is not a spatial mean
or decay condition: it replaces `p(t,x)` by `p(t,x)-p(t,x₀)`
(`formalization/NSFormalization/Section4/A02/Restrict.lean:244-274`).  Choosing
`x₀=0` gives exactly the lane's basepoint gauge.  `Patch.lean` uses only
time-dependent `PressureGaugeEquivOn` (`formalization/NSFormalization/Section4/A02/Patch.lean:63-98`)
and introduces no competing normalization.

### Joint pressure smoothness

`pressure_smooth_of_velocity_smooth` does not derive c4 from c3 plus
`MemForceR`.  It assumes the strictly stronger global statement

```lean
hjoint : ContDiff ℝ ∞ (pressureGradientOfVelocity ν f velocity)
```

at `ConstructorPressure.lean:201-205`.  By contrast, c3 is only `ContDiffOn` on
the half-open future slab (`SolutionClass.lean:121-124`), and `MemForceR`
supplies force smoothness only on the future domain
(`formalization/NSFormalization/Section4/D01/ForceClass.lean:155-164`).  The
available derivative regularity theorem requires an open set
(`vendor/NavierStokesAndEuler/NavierStokes/ResidualRegularity.lean:36-52`).
On `Ioo 0 T`, c3 and `MemForceR` can give joint smoothness of `G`; at `t=0`, the
global two-sided derivative needs an extension/compatibility result.  At finite
regularity this is the familiar extra time derivative (`C²` of `u` to make
`∂ₜu` `C¹`); for the stated `C∞` conclusion all time orders and the endpoint
extension must be controlled.  The hypothesis is explicit, so the theorem is
sound, but it does not close c4 from the constructor inputs currently listed.

## 3. Gaps and exact fixes

The substantive open mathematics is accurately isolated: transport the mild
Duhamel equation to the datum equality at `ConstructorPressure.lean:97-99`;
prove that the resulting Leray-complement field has the exact
`HasSymmetricJacobian` properties at `:173-175`/`:223-225`; and supply endpoint
`MemLp` plus joint regularity for the two-sided `temporalDerivative`.  Until
those are supplied, this module is a pressure assembly layer, not a complete
`CarrierConstructorFull`, exactly as the worker records at
`research/A01/REPORT_168.md:138-177`.

Exact fixes required by this verdict:

1. **N1 — honest projected-equation naming.** Delete the redundant
   `hprojected` binder from `momentum_of_projected` (derive its equation inline
   by `convectionDivergence_eq_advection` and `abel`) and replace the module,
   ATTEMPTS, and report wording with: “momentum follows once the explicitly
   defined `G=R-∂ₜu` is smooth and curl-free; the genuine mild/Leray projected
   input is the datum equality used by
   `pressureGradient_pressureOfVelocity_lerayComplement`.”
2. **N2 — regularity strength.** Replace “B1-strength input” at
   `ConstructorPressure.lean:197-200` and `REPORT_168.md:175` with “additional
   global extension regularity, not implied by c3 plus `MemForceR`; B1/T1 must
   still prove an endpoint-compatible version.”
3. **N3 — future CI closure.** `experiments/build_changed_lean.py --base-ref
   origin/erenup/integration --dry-run` currently selects exactly
   `NSFormalization.Section4.A01.ConstructorPressure`, but it is not in a
   registered contract closure; add it to the next A01 contract bundle after
   merge.

No mathematical statement is false, and N1 is a removable redundant
hypothesis rather than circular reasoning, so these are notes rather than a
rejection.

## 4. Commands and results

All Lean commands were run after sourcing the lane's `scripts/lean-env.sh`,
with `lake` invoked only from `verification/` and `LEAN_NUM_THREADS=6`.

### Build and direct typechecks

```text
$ LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A01.ConstructorPressure
...
⚠ [9908/9929] Replayed Formal.R3LerayComplexFiberSymbol
warning: ../vendor/HeliCorgi/Formal/R3LerayComplexFiberSymbol.lean:42:2: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
Build completed successfully (9929 jobs).
```

Exit 0.  The omitted lines are replayed warnings from pre-existing
`NSFormalization.Source`, `NSFormalization.Paper3`, and `Formal` modules; there
is no warning from `ConstructorPressure.lean`.

```text
$ LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section4/A01/ConstructorPressure.lean
```

Exit 0, exactly zero output.

```text
$ LEAN_NUM_THREADS=6 lake env lean ../research/A01/axioms_pressure_p3.lean
'NSFormalization.Section4.A01.momentumResidualOfVelocity' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.pressureGradientOfVelocity' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.pressureOfVelocity' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.pressureOfVelocity_basepoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.pressureGradientOfVelocity_memLp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.pressureGradient_pressureOfVelocity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.pressureGradient_pressureOfVelocity_lerayComplement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.pressureGradient_pressureOfVelocity_lerayComplement_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.pressure_gradient_memLp_slice' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.pressure_gradient_memLp' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.pressureOfVelocity_slice_smooth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.pressure_smooth_of_velocity_smooth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.momentum_of_projected' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.pressureOfVelocity_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Exit 0.  Every printed declaration has exactly the required three axioms, and
the example at `axioms_pressure_p3.lean:23-25` typechecks.

### Root gate and hygiene

```text
$ LEAN_NUM_THREADS=6 make check
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 30,
  "source_counts": {
    "formalization": 473,
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
    ... 25,362-line closure inventory omitted ...
  "base_compatibility_checked": false,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.048s

OK
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.
```

Exit 0.  The raw stdout was 25,362 lines / 1,042,358 bytes.  The copied-source
`BoundaryCorollary.lean:90` token is pre-existing and is not imported by this
lane; `source_hashes_match: false` is a non-failing plan-metadata signal (the
lane adds a formalization source), not a gate failure.

```text
$ git diff --name-status origin/erenup/integration...HEAD
A formalization/NSFormalization/Section4/A01/ConstructorPressure.lean
M research/A01/A3_SPLIT.md
A research/A01/ATTEMPTS_PRESSURE_P3.md
A research/A01/REPORT_168.md
A research/A01/axioms_pressure_p3.lean

$ rg -n --glob '*.lean' '\b(sorry|admit|axiom|native_decide)\b|set_option\s+maxHeartbeats' \
    formalization/NSFormalization/Section4/A01/ConstructorPressure.lean \
    research/A01/axioms_pressure_p3.lean

$ git diff --check origin/erenup/integration...HEAD
```

Both hygiene commands have exactly zero output and exit 0.  No existing Lean
module was modified; the only formalization file is new.  There is no
`maxHeartbeats` declaration.

The whole-tree negative search was run before accepting the reported gap:

```text
$ grep -rnE 'theorem .*lerayComplement.*(curl|symmetric|gradient)|theorem .*(curl|symmetric|gradient).*lerayComplement|theorem .*orderZeroDatum_longitudinal_of_curl_free' formalization/NSFormalization/Section4 || true
formalization/NSFormalization/Section4/D01/OrderZeroCurl.lean:481:theorem orderZeroDatum_longitudinal_of_curl_free (hz : MemLp z 2 volume)
formalization/NSFormalization/Section4/D01/Longitudinal.lean:280:theorem lerayComplement_eq_self_of_curl_free {Z : EulerLpTranslation.SmoothL2Field Space}

$ grep -rnE 'gradient_of_curlFree|curlFree.*gradient|lerayComplement.*HasSymmetricJacobian|HasSymmetricJacobian.*lerayComplement' formalization/NSFormalization/Section4 || true
```

Both exit 0; the second has exactly zero output.  Reading the two hits confirms
they are the forward curl-free-to-longitudinal direction cited above.

`verification/` is untouched, so the conditional `scripts/gates.sh` and
`check_contracts.py --base-ref origin/erenup/integration` gates do not apply:

```text
verification/ untouched: scripts/gates.sh and check_contracts.py --base-ref origin/erenup/integration not applicable
```

### Reviewer probes

```text
$ LEAN_NUM_THREADS=6 lake env lean ../research/A01/probes/rev168_projected_redundant.lean
```

Exit 0, exactly zero output.  This proves the redundancy result and the
positive-horizon non-vacuity instance.

The substantive negative mutation changes the main gradient conclusion from
`∇p=G` to `∇p=G+coordinateVector 0`; it does not drop an argument
(`research/A01/probes/rev168_negative_gradient_shift.lean:11-22`).  Exact
result:

```text
$ LEAN_NUM_THREADS=6 lake env lean ../research/A01/probes/rev168_negative_gradient_shift.lean
../research/A01/probes/rev168_negative_gradient_shift.lean:22:2: error: Type mismatch
  pressureGradient_pressureOfVelocity ν f velocity t hsmooth hsym x
has type
  pressureGradient (pressureOfVelocity ν f velocity) t x = pressureGradientOfVelocity ν f velocity (t, x)
but is expected to have type
  pressureGradient (pressureOfVelocity ν f velocity) t x =
    pressureGradientOfVelocity ν f velocity (t, x) + coordinateVector 0
```

Exit 1, the expected failure: the original proof yields exactly `G`, not the
mutated nonzero shift.
