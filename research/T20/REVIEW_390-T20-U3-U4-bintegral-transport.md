ACCEPT

## 1. What the lane claims

The worker claims exactly two canonical T20 fields: `bIntegral` and
`constantTransportSkew` (`research/T20/REPORT_390.md:3-32`).  Both declarations
exist with the reported statements:

- `bIntegral` is at
  `formalization/NSFormalization/Section3/T20/BIntegral.lean:143-151`, and its
  type is textually the canonical `CriticalRegularityTAPI.bIntegral` field at
  `formalization/NSFormalization/Section3/T20/CriticalRegularity.lean:301-307`.
  It says, with the same `g,hg` quantifier order,
  `criticalBIntegral (meanFreeForce g) ≤ criticalRho g`.
- `constantTransportSkew` is at
  `formalization/NSFormalization/Section3/T20/ConstantTransport.lean:58-70`, and
  its type is textually the canonical field at
  `formalization/NSFormalization/Section3/T20/CriticalRegularity.lean:248-266`.
  It has exactly `m,v,w`, the two `SmoothPeriodicT` premises, the two concrete
  `Integrable` premises, and the minus sign in the pairing identity.

The mathematics agrees with the named paper lines.  The paper states that
constant transport commutes with Fourier multipliers and is skew-adjoint at
`paper/sections/03-torus.tex:407-411`; it defines `b(t)` at `:413-418` and states
the zero-mode contraction integral `∫₀∞b ≤ ρ` at `:441-444`.  The Lean
definitions are fail-safe extended quantities, not `toReal` totalizations:
`criticalBIntegral` and `criticalRho` are at
`formalization/NSFormalization/Section3/T20/CriticalRegularity.lean:76-88`, and
the datum-path infimum explicitly records strong measurability at
`formalization/NSFormalization/Section3/T10/PeriodicData.lean:218-230`.

No premise makes either result vacuous.  The `g ∈ forceClassT` proof binder is
unused in `bIntegral` (`BIntegral.lean:143-151`), but the proof is genuinely
stronger: for every represented path it constructs a slicewise homogeneous
datum and compares its norm.  The reviewer probe supplies a nonzero smooth,
positive-time compactly supported Fourier-mode force
(`research/T20/probes/rev390_nonvacuity.lean:24-68`), an explicit strongly
measurable half-order path proving `criticalRho force ≠ ⊤` (`:70-101`), and
instantiates `bIntegral` at that force (`:103-104`).

The two integrability premises of `constantTransportSkew` are unused at
`ConstantTransport.lean:71`; this is honestly disclosed in both the module
docstring (`:19-21`) and attempts log
(`research/T20/ATTEMPTS_U3_U4.md:26-27`).  They are redundant under the stronger
smooth-periodic premises rather than impossible premises: `SmoothPeriodicT`
means global smoothness plus physical periodicity
(`formalization/NSFormalization/Section3/T12/MeanZeroCalculus.lean:64-67`), and
the proof explicitly obtains those two facts at `ConstantTransport.lean:72-86`.
The worker's checked probe also exhibits a nonzero smooth periodic field at
`research/T20/probes/bintegral_transport_closes.lean:51-59`.

## 2. What is in Lean

The U3 proof implements the claimed zero-mode contraction rather than
repackaging the goal.  Its multiplier is the homogeneous weight divided by the
inhomogeneous Bessel weight (`BIntegral.lean:40-70`).  For each datum slice it
constructs an `IsPeriodicHomogeneousDatum` for the mean-free field, handles the
zero frequency separately, and preserves the nonzero Fourier coefficients
(`BIntegral.lean:79-127`).  It then applies the public bounded reweighting norm
estimate and the pointwise infimum (`BIntegral.lean:128-139`) before transporting
the bound through `lintegral` and the path infimum (`:143-151`).

The cited ingredients have the claimed statements: `reweightDatum`, its norm
bound, and real-subspace preservation are at
`formalization/NSFormalization/Section3/T12/SpectralGap.lean:124-189`;
constant and subtraction Fourier coefficients are at
`formalization/NSFormalization/Section3/T10/DatumBasics.lean:41-58`; and
`meanT_sub_const` is at
`formalization/NSFormalization/Section3/T11/MeanIdentity.lean:126-133`.  The
whole-space mirror really is the path-infimum contraction reported by the lane
(`formalization/NSFormalization/Section4/R43/ForcePath.lean:55-84`).

The U4 proof first identifies Haar pairing with the physical cube integral
(`ConstantTransport.lean:39-44`) and expands the constant derivative into its
three coordinate partials (`:46-54`).  It applies coordinatewise periodic
integration by parts (`:74-86`), moves the finite sums and constants through the
cube integral (`:87-118`), and obtains the exact negative pairing (`:119-123`).
The reused cube integration-by-parts theorem is present at
`vendor/NavierStokesAndEuler/NavierStokes/PeriodicUniqueness.lean:389-410`, and
the Haar/cube bridge is at
`formalization/NSFormalization/Paper1/TorusCube.lean:39-52`.

The conformance probe repeats both complete canonical field types and closes
them directly with the lane theorems
(`research/T20/probes/bintegral_transport_closes.lean:28-49`).  The axiom file
prints exactly those two declarations
(`research/T20/axioms_u3_u4.lean:9-10`), and both outputs are exactly
`[propext, Classical.choice, Quot.sound]`.

## 3. Gaps, hygiene, and negative check

There is no residual for U3 or U4.  The report's only out-of-scope note is the
remaining T20 analytic core (`research/T20/REPORT_390.md:48-55`).  As required,
I searched the whole `formalization/NSFormalization/Section4` tree before
accepting that note.  Section 4 contains the whole-space
`velocityCriticalL3` analogue at
`formalization/NSFormalization/Section4/A05/CriticalL3.lean:390-409` and the R³
critical trilinear assembly at
`formalization/NSFormalization/Section4/R43/Trilinear.lean:332-345`; these are
not the missing torus T12/T20 statements.  There is no Section 4 declaration
named `gradientLambdaCriticalL3` or `gradientLSix`; the sole `gradientLSix`
text hit is explanatory prose at
`formalization/NSFormalization/Section4/A05/HessianLaplacian.lean:9-18`.

Hygiene passes.  The worker commit adds, rather than modifies, the two
formalization modules; `git diff --name-status HEAD^ HEAD -- formalization`
prints only:

```text
A	formalization/NSFormalization/Section3/T20/BIntegral.lean
A	formalization/NSFormalization/Section3/T20/ConstantTransport.lean
```

The mandated triple-dot check warns that the current base has two merge bases
and selects `b66b913d`, then lists the two lane modules plus the already merged
lane-381 canonical/research files; no formalization path has status `M`.
The canonical file is byte-identical to the current integration copy, and the
only relevant dependency drift is the addition of two unrelated T12 modules.
The worker commit has no `verification/` path.

There is no executable `sorry`, `admit`, `axiom`, or `native_decide` in either
module, the worker probe, or the axiom audit.  The sole heartbeat override is
the per-declaration, commented
`set_option maxHeartbeats 400000 in` at `BIntegral.lean:72-79`, exactly at the
allowed limit.  `git diff --check HEAD^ HEAD` produces no output.

The substantive negative probe flips the main skew identity's minus sign to a
plus sign without dropping any argument
(`research/T20/probes/rev390_sign_flip.lean:20-33`).  Direct reuse fails for
exactly that mutation:

```text
../research/T20/probes/rev390_sign_flip.lean:33:2: error: Type mismatch
  constantTransportSkew
has type
  ∀ (m : Space) (v w : SpatialField),
    SmoothPeriodicT v →
      SmoothPeriodicT w →
        Integrable (fun y => ⟪torusLift (constantTransportSpatialT m v) y, torusLift w y⟫_ℝ) periodicTorusMeasure →
          Integrable (fun y => ⟪torusLift v y, torusLift (constantTransportSpatialT m w) y⟫_ℝ) periodicTorusMeasure →
            periodicPairing (constantTransportSpatialT m v) w = -periodicPairing v (constantTransportSpatialT m w)
but is expected to have type
  ∀ (m : Space) (v w : SpatialField),
    SmoothPeriodicT v →
      SmoothPeriodicT w →
        Integrable (fun y => ⟪torusLift (constantTransportSpatialT m v) y, torusLift w y⟫_ℝ) periodicTorusMeasure →
          Integrable (fun y => ⟪torusLift v y, torusLift (constantTransportSpatialT m w) y⟫_ℝ) periodicTorusMeasure →
            periodicPairing (constantTransportSpatialT m v) w = periodicPairing v (constantTransportSpatialT m w)
```

## 4. Commands and results

All Lean commands were run after `. scripts/lean-env.sh`; every `lake` command
was run from `verification/` with `LEAN_NUM_THREADS=6`.

```text
$ LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T20.BIntegral NSFormalization.Section3.T20.ConstantTransport
exit=0
[Lake replayed pre-existing dependency linter warnings; neither lane module emitted a warning.]
Build completed successfully (10593 jobs).

$ LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T20/BIntegral.lean
exit=0, output bytes=0, output lines=0

$ LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T20/ConstantTransport.lean
exit=0, output bytes=0, output lines=0

$ LEAN_NUM_THREADS=6 lake env lean ../research/T20/probes/bintegral_transport_closes.lean
exit=0, output bytes=0, output lines=0

$ LEAN_NUM_THREADS=6 lake env lean ../research/T20/probes/rev390_nonvacuity.lean
exit=0, output bytes=0, output lines=0
```

The axiom command exited 0 and printed exactly:

```text
'NSFormalization.Section3.T20.bIntegral' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T20.constantTransportSkew' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`make check` exited 0.  Its architecture JSON reported `task_count: 45`,
`registered_contracts: 42`, `base_compatibility_checked: false` for the plain
invocation, and the informational `source_hashes_match: false`; its exact final
checks were:

```text
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.046s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
```

The negative command exited 1 with the expected type mismatch quoted in part 3.
The worker commit does not touch `verification/`, so the brief makes
`scripts/gates.sh` and the explicit `check_contracts.py --base-ref
origin/erenup/integration-section3` conditional and they are not applicable.
The plain `make check` did run `experiments/check_contracts.py` successfully.

Verdict: ACCEPT.  Fixes: none.
