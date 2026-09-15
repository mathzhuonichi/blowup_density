ACCEPT

## 1. What the lane claims

This second review judges the consumer-facing rework at commit `c78a39c`. The report claims five
public declarations: a zero-outside-horizon reader, its pointwise in-horizon evaluation, the
pointwise round trip for the canonical global force, a package containing the canonical path plus
the two downstream facts, and the cylinder-to-physical initial-class bridge
(`research/A01/REPORT_167.md:3-33`). Every declaration exists with the displayed proposition type:

| declaration | report | Lean source | result |
|---|---:|---:|---|
| `forceOfPath` | `research/A01/REPORT_167.md:6-7` | `formalization/NSFormalization/Section4/A01/ForceBridge.lean:41-42` | exact |
| `forceOfPath_apply` | `research/A01/REPORT_167.md:9-12` | `formalization/NSFormalization/Section4/A01/ForceBridge.lean:45-47` | exact |
| `forceOfPath_forcePath_eq_on_horizon` | `research/A01/REPORT_167.md:14-16` | `formalization/NSFormalization/Section4/A01/ForceBridge.lean:52-56` | exact |
| `forcePath_of_memForceR` | `research/A01/REPORT_167.md:18-23` | `formalization/NSFormalization/Section4/A01/ForceBridge.lean:64-70` | exact |
| `initialClassR_of_smoothL2` | `research/A01/REPORT_167.md:25-33` | `formalization/NSFormalization/Section4/A01/ForceBridge.lean:81-106` | exact |

The reorientation matches the superseding brief and the real consumer. The paper defines
`F_R = C^∞([0,∞);H^∞) ∩ ⋂_m(L¹_tH^m_x ∩ L²_tH^m_x)` and explicitly permits whole-space forces
which are nonzero at zero and not compactly supported
(`paper/sections/02-preliminaries.tex:17-26`; opened with `sed -n '17,26p'`). Lean's
`D01.MemForceR` has exactly the physical smoothness and per-order smooth datum-path, `MemLp 1`, and
`MemLp 2` clauses (`formalization/NSFormalization/Section4/D01/ForceClass.lean:155-164`). From that
global input, `C01.forcePath` is the physical slice and its jets are continuous
(`formalization/NSFormalization/Section4/C01/JetPaths.lean:82-110`), while
`A04.memL1Hm_of_memForceR` supplies the retained force's `MemL1Hm`
(`formalization/NSFormalization/Section4/A04/Forcing.lean:132-147`). Thus no force is invented.

The package has the exact data consumed by both A01 APIs: `HasAprioriBound` takes an explicit
`F : Icc 0 S → SmoothL2Field Space` immediately followed by
`hF : ∀ n, Continuous fun t => (F t).jetLp n`
(`formalization/NSFormalization/Section4/A01/Horizon.lean:106-114`), and
`localTheory_on_prescribed_horizon` takes the same pair
(`formalization/NSFormalization/Section4/A01/Horizon.lean:137-142`). The reviewer wiring probe
unpacks the existential and uses its facts at the canonical path verbatim
(`research/A01/probes/rev167_wiring.lean:17-22`). The form
`∃ F, F = C01.forcePath hf ∧ …` is therefore usable. As a non-blocking API note, the direct
conjunction on `C01.forcePath hf` is more ergonomic than existentially naming an already canonical
path; the probe shows that this is only one `rcases`, not a mathematical or consumer-shape defect.

The on-horizon identity is pointwise, not a.e.: it quantifies over each subtype time and each
spatial point (`formalization/NSFormalization/Section4/A01/ForceBridge.lean:52-56`). Outside
`Icc 0 S`, the definition takes the `else 0` branch
(`formalization/NSFormalization/Section4/A01/ForceBridge.lean:39-42`). Both the module and report
state that this zero extension is only a comparison device and make no `MemForceR` claim for it
(`formalization/NSFormalization/Section4/A01/ForceBridge.lean:14-17,39-40`;
`research/A01/REPORT_167.md:44-46,63-66`). This resolves the first review's endpoint objection
without an a.e. weakening.

The datum half is faithful to lane 162. `initialClassR_of_smoothL2` takes exactly the six inputs of
`divergence_ae_of_cylinder`—`u`, `U`, angular invariance, ordinary-lift equality,
`divergenceFreeSpace`, and the smooth representative's a.e. equality
(`formalization/NSFormalization/Section4/A01/ConstructorDivergence.lean:66-75`)—then upgrades the
a.e. coordinate sum to an everywhere identity by continuity
(`formalization/NSFormalization/Section4/A01/ForceBridge.lean:90-106`). Its first component is honest:
`SmoothL2Field.integrable` contains every jet order
(`vendor/NavierStokesAndEuler/Euler/LpSmoothField.lean:31-34`), and
`D01.memHInfty_of_contDiff_memLp` converts precisely those all-order data into `MemHInfty`
(`formalization/NSFormalization/Section4/D01/SmoothDatum.lean:295-312`). The target is exactly
`MemHInfty ∧ IsSolenoidal` (`formalization/NSFormalization/Section4/A02/SolutionClass.lean:88-97`).

At `t = 0`, the prescribed-horizon theorem returns `U 0 = a.toLp`, the ordinary-lift equality,
divergence-free membership, and angle invariance
(`formalization/NSFormalization/Section4/A01/Horizon.lean:143-153`). Together with
`SmoothL2Field.toLp_ae` (`vendor/NavierStokesAndEuler/Euler/LpSmoothField.lean:42-44`), these are
exactly the premises of `initialClassR_of_smoothL2`; the reviewer probe derives
`a.field ∈ initialClassR` from only those returned clauses
(`research/A01/probes/rev167_wiring.lean:32-50`). Thus setting `a' := a.field` needs no extra
post-output hypothesis. For clarity about upstream scope, `localTheory_on_prescribed_horizon`
itself still takes a pointwise divergence premise on its input `a`
(`formalization/NSFormalization/Section4/A01/Horizon.lean:137-140`); this lane does not claim to
remove that separate supply-side premise.

No hypothesis is silently vacuous or dead. Every named theorem binder occurs in the proof; the
module's zero-output typecheck emits no unused-variable warning. There is no `.toReal`, hence no
`⊤.toReal = 0` loophole. Although the horizon-polymorphic identities also make sense when
`Icc 0 S` is empty, substantive instances use `S = 2` with a nonzero endpoint
(`research/A01/axioms_force_bridge.lean:24-86`) and `S = 1` for the required zero force
(`research/A01/probes/rev167_wiring.lean:24-30`).

## 2. What is in Lean

The finished module provides the correct constructor data:

1. Given the paper's original `f` and `hf : D01.MemForceR f`, the constructor may take
   `F := C01.forcePath hf`, feed the packaged jet continuity to `HasAprioriBound` and
   `localTheory_on_prescribed_horizon`, retain `f' := f` and `hf`, and use the packaged
   `A04.MemL1Hm f` (`formalization/NSFormalization/Section4/A01/ForceBridge.lean:58-70`).
2. Reading that path agrees with `f` at every `(t,x)` on `Icc 0 S`, while the arbitrary zero value
   outside the horizon is explicitly outside the theorem's claim
   (`formalization/NSFormalization/Section4/A01/ForceBridge.lean:39-56`).
3. A smooth all-jet-`L²` representative of the initial cylinder slice belongs to
   `A02.initialClassR` using lane 162's genuine divergence bridge
   (`formalization/NSFormalization/Section4/A01/ForceBridge.lean:72-106`).

The previous `ForcePathSmoothness`, carrier-to-global membership theorems, reverse round trip, and
dead `hF` premise are absent. The report and lane note describe the corrected direction honestly
(`research/A01/REPORT_167.md:38-56`; `research/A01/A3_SPLIT.md:273`).

Non-vacuity is stronger than the minimum. The committed conformance file constructs a concrete
nonzero compact spacetime bump, proves it lies in `F_R`, applies `forcePath_of_memForceR`, and checks
the pointwise identity at its nonzero endpoint
(`research/A01/axioms_force_bridge.lean:24-86`). The reviewer additionally instantiated
`forcePath_of_memForceR` with `f := 0` and `A04.memForceR_zero` on inhabited `Icc 0 1`
(`research/A01/probes/rev167_wiring.lean:24-30`). Both compile.

Hygiene passes. Against `origin/erenup/integration`, the sole formalization change is the new
`ForceBridge.lean`; the remaining four changed files are the requested records/conformance files.
No existing Lean module and no `verification/` file changed. The production module contains no
`sorry`, `admit`, `axiom`, or `native_decide`, and neither lane Lean file contains a heartbeat
override. `git diff --check` is clean.

## 3. Gaps

There is no remaining force-interface gap in reworked row (v). The global paper force supplies the
canonical local carrier, and the exact pointwise field identity supplies the return comparison.

The report correctly limits `forceOfPath F`: an arbitrary finite path does not thereby acquire a
global smooth extension or `F_R` membership (`research/A01/REPORT_167.md:63-66`). The required
whole-tree negative search found no force-specific smooth-extension declaration:

```text
$ grep -rn -E '(force|Force).*(smooth.*exten|exten.*smooth)|(smooth.*exten|exten.*smooth).*(force|Force)' formalization/NSFormalization/Section4
force_extension_search_exit=1
```

The only broader `Section4` smooth-extension candidate is `I01.extension_smoothOn`; it assumes an
already spacetime-smooth field which vanishes on a quiet interval and extends it toward negative
time (`formalization/NSFormalization/Section4/I01/Extension.lean:29-38`). It cannot extend arbitrary
finite-horizon carrier data through the right endpoint.

The broader mild-to-classical carrier constructor remains outside this lane, as the report says at
`research/A01/REPORT_167.md:68-71`; lane 162 exposes `Z`, `hslice`, and spatial `ContDiff` as named
inputs (`formalization/NSFormalization/Section4/A01/ConstructorDivergence.lean:147-161`). A second
whole-tree declaration search found no theorem/definition named as a carrier constructor:

```text
$ grep -rn -E 'theorem .*([Cc]arrier.*[Cc]onstructor|[Cc]onstructor.*[Cc]arrier)|def .*([Cc]arrier.*[Cc]onstructor|[Cc]onstructor.*[Cc]arrier)' formalization/NSFormalization/Section4
carrier_constructor_search_exit=1
```

This is not a defect in the force bridge. The existing `SliceWiring` module likewise records that
it consumes a given classical solution and `hslice`, rather than constructing them
(`formalization/NSFormalization/Section4/A01/SliceWiring.lean:49-53,166-190`).

## 4. Commands and results

All Lean commands ran from `verification/` after `. ../scripts/lean-env.sh`, with
`LEAN_NUM_THREADS=6`; only one Lake command ran at a time.

### Required build and typecheck gates

```text
$ LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A01.ForceBridge
exit 0
```

The lane module itself was silent: the full 205-line output consists of replayed dependency
warnings plus Lake's completion line, and searching it for `ForceBridge.lean` returned no match.
Exact capture metadata and terminal tail:

```text
  205 11970 /tmp/rev167_rework_lake_build.out
166e1bb42ae40e0009e4708bf6d69c792a7df8e054101027c7745f9d8e9f182a  /tmp/rev167_rework_lake_build.out
forcebridge_warning_search_exit=1
warning: NSFormalization/Source/ViscosityPacket.lean:34:63: This simp argument is unused:
  Function.comp_def

Hint: Omit it from the simp argument list.
  [apply] simp [viscosityVelocity, dilateField, viscosityHomeomorph, Prod.map]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
⚠ [10176/10231] Replayed NSFormalization.Paper3.SobolevDirectionalDerivative
warning: NSFormalization/Paper3/SobolevDirectionalDerivative.lean:103:16: `SchwartzMap.smul_apply` has been deprecated: Use `smul_apply` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.smul_apply` to `smul_apply x`).
Build completed successfully (10231 jobs).
```

```text
$ LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section4/A01/ForceBridge.lean
```

Exit 0, exactly zero output.

```text
$ LEAN_NUM_THREADS=6 lake env lean ../research/A01/axioms_force_bridge.lean
'NSFormalization.Section4.A01.forceOfPath' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.forceOfPath_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.forceOfPath_forcePath_eq_on_horizon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.forcePath_of_memForceR' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.initialClassR_of_smoothL2' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Exit 0. Every exported declaration has exactly the required three axioms.

`make check` exited 0. Its architecture JSON is 1,042,470 bytes, so the complete output was
captured and hashed; exact capture metadata and terminal output follow:

```text
$ make check
  25367 1042470 /tmp/rev167_rework_make_check.out
2afd345589484df4ab7d05735b3905255e75a567e8d2e925cd5a2b19701dc28e  /tmp/rev167_rework_make_check.out
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
      "Tests.EnergyAbsorptionPartialV3"
    ]
  },
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

The conditional contract gates do not apply because `verification/` was untouched:

```text
$ git diff --name-only origin/erenup/integration...HEAD -- 'verification/**'
```

Exit 0, zero output. Accordingly, the brief did not require `scripts/gates.sh` or
`python3 experiments/check_contracts.py --base-ref origin/erenup/integration` for this lane.

### Reviewer probes

The consumer/zero-force/initial-output wiring probe passed:

```text
$ LEAN_NUM_THREADS=6 lake env lean ../research/A01/probes/rev167_wiring.lean
```

Exit 0, exactly zero output.

The substantive mutation flips the sign in the main pointwise on-horizon statement
(`research/A01/probes/rev167_mutation.lean:10-14`). It fails for the expected changed conclusion,
not because an argument was dropped:

```text
$ LEAN_NUM_THREADS=6 lake env lean ../research/A01/probes/rev167_mutation.lean
../research/A01/probes/rev167_mutation.lean:14:2: error: Type mismatch: After simplification, term
  forceOfPath_forcePath_eq_on_horizon hf t x
 has type
  forceOfPath (C01.forcePath hf) (↑t, x) = f (↑t, x)
but is expected to have type
  forceOfPath (C01.forcePath hf) (↑t, x) = -f (↑t, x)
```

Exit 1, expected.

### Hygiene

```text
$ git diff --name-only origin/erenup/integration...HEAD
formalization/NSFormalization/Section4/A01/ForceBridge.lean
research/A01/A3_SPLIT.md
research/A01/ATTEMPTS_FORCE_BRIDGE.md
research/A01/REPORT_167.md
research/A01/axioms_force_bridge.lean

$ git diff --name-only origin/erenup/integration...HEAD -- 'formalization/**/*.lean'
formalization/NSFormalization/Section4/A01/ForceBridge.lean

$ rg -n '\b(sorry|admit|axiom|native_decide)\b' formalization/NSFormalization/Section4/A01/ForceBridge.lean

$ rg -n 'maxHeartbeats' formalization/NSFormalization/Section4/A01/ForceBridge.lean research/A01/axioms_force_bridge.lean

$ git diff --check origin/erenup/integration...HEAD
```

The last three commands produced zero output; both `rg` searches exited 1 (no match), and
`git diff --check` exited 0. `ForceBridge.lean` is added, not a modification of an integration
module. The untracked `REVIEW_167-A01-force-bridge.md` and `rev167_*` files are the reviewer-only
writes expressly permitted by the review brief.

Fixes required: none.
