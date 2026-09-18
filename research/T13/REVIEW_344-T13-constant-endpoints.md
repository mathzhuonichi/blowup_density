ACCEPT

# Review of lane 344 — T13 constant and endpoints

## 1. What the lane claims

The worker claims three fields of `LocalizationAPI`, with no named input:
`constant_pos_finite`, `endpoint_zero`, and `endpoint_one`
(`research/T13/REPORT_344.md:3-26`).  It explicitly leaves
`wholeSpace_identity`, `torus_identity`, and `localization` outside this lane
(`research/T13/REPORT_344.md:60-64`).

These are the requested mathematical claims.  The paper says that the concrete
constant

```text
c_s = integral_R3 |exp(i h_1)-1|^2 / |h|^(3+2s) dh
```

is positive and finite, with the near-zero radial exponent `1-2s` and the
far-field exponent `-1-2s` (`paper/sections/03-torus.tex:35-39`).  It separately
states equality of the `L²` norms at order zero and of the `L²` gradient norms
at order one (`paper/sections/03-torus.tex:22-29`,
`paper/sections/03-torus.tex:95-98`).  This is exactly the interpretation in the
worker report (`research/T13/REPORT_344.md:10-26`).

The canonical definitions also have the right content: `fundamentalCube` is
the closed unit cube, `SupportedInBall` is a topological-support inclusion, and
`periodize` is the actual lattice sum
(`formalization/NSFormalization/Section3/T13/Localization.lean:25-43`);
`fractionalRadialKernel` and `cFrac` are the concrete `ℝ≥0∞` kernel and integral
with no hidden `2π` (`formalization/NSFormalization/Section3/T13/Localization.lean:47-57`);
and `gradientENorm` is the Hilbert--Schmidt `L²` gradient norm
(`formalization/NSFormalization/Section3/T13/Localization.lean:82-88`).

## 2. What is in Lean

### Statement fidelity

The three exported theorems occur at
`formalization/NSFormalization/Section3/T13/ConstantEndpoints.lean:401-422`.
Their types are exactly the corresponding API fields at
`research/T13/probes/api_on_canonical.lean:32-39` and
`research/T13/probes/api_on_canonical.lean:82-106`.  The independent
field-by-field conformance examples typecheck at
`research/T13/probes/constant_endpoints_closes.lean:134-154`, and the full
record constructor places the three theorems in precisely their intended slots
at `research/T13/probes/constant_endpoints_closes.lean:156-184`.

There is no arbitrary chosen constant and no `.toReal` collapse.  The proof of
finiteness establishes the paper's two bounds and radial integrability at
`formalization/NSFormalization/Section3/T13/ConstantEndpoints.lean:65-192`;
positivity uses a nonempty open slab on which the concrete integrand is nonzero
at `formalization/NSFormalization/Section3/T13/ConstantEndpoints.lean:194-222`.
Thus a wrong or vacuous implementation cannot satisfy the constant theorem.

The endpoint mechanism is also substantive.  Nonzero lattice translates vanish
on the closed cube and the lattice sum reduces to its zero term at
`formalization/NSFormalization/Section3/T13/ConstantEndpoints.lean:306-338`.
The neighborhood equality needed for derivatives is at lines 340-347, and the
two norm identities are proved at lines 361-397.  The named API hypotheses are
honest: `hball` and support are used.  The API's `0 < r` and `ContDiff` binders
are not needed by the stronger internal endpoint lemmas, so the final wrappers
ignore them at lines 407-422; they were not added by this lane and are copied
unchanged from the API.  This strengthens the result rather than making it
vacuous.

The probe supplies an admissible ball, a smooth compact bump, and a field that
is provably nonzero at its center
(`research/T13/probes/constant_endpoints_closes.lean:201-256`), then instantiates
both endpoint identities on that field at lines 258-268.  It also instantiates
the constant theorem at `s = 1/2` at lines 192-199.  Hence neither the ball
condition nor the endpoint conclusions are vacuous.

The Fourier lemmas named in the brief do exist with the advertised content:
`periodicFourierCoeff_gradient_sq` is at
`formalization/NSFormalization/Section3/T10/FourierCalculus.lean:265-276`, and
`gradientTensor_parseval` is at
`formalization/NSFormalization/Section3/T10/ForcePaths.lean:206-225`.  Lane 344
does not claim to use them; its direct single-copy derivative proof is the
paper's endpoint argument and is sufficient.

### Hygiene and negative test

The lane commit adds the new implementation module; it does not modify an
existing formalization module.  Its commit-local file list is one new module,
four new lane records/probes, and the required append to `COMPARISON.md`.  The
required triple-dot command currently warns that the moving integration branch
has two merge bases and also shows the already-merged lane-339 additions, but
every formalization entry is status `A`, not `M`:

```text
$ git diff --name-status origin/erenup/integration-section3...HEAD
warning: origin/erenup/integration-section3...HEAD: multiple merge bases, using 84490fdc1decddd20be4a91935bdb5e4b666f579
A formalization/NSFormalization/Section3/T11/ClassicalRegularity.lean
A formalization/NSFormalization/Section3/T13/ConstantEndpoints.lean
A research/T11/ATTEMPTS_CLASSICAL_REGULARITY.md
A research/T11/REPORT_339.md
M research/T11/T11_SPLIT.md
A research/T11/axioms_classical_regularity.lean
A research/T11/probes/classical_regularity_closes.lean
A research/T13/ATTEMPTS_CONSTANT_ENDPOINTS.md
M research/T13/COMPARISON.md
A research/T13/REPORT_344.md
A research/T13/axioms_constant_endpoints.lean
A research/T13/probes/constant_endpoints_closes.lean
```

No declaration-level `sorry`, `admit`, `axiom`, `native_decide`, or
`maxHeartbeats` occurs in the implementation, conformance probe, or axiom file:

```text
$ rg -n '^\s*axiom\b|\bsorry\b|\badmit\b|\bnative_decide\b|set_option\s+maxHeartbeats' formalization/NSFormalization/Section3/T13/ConstantEndpoints.lean research/T13/probes/constant_endpoints_closes.lean research/T13/axioms_constant_endpoints.lean
(no output; exit 1)
```

The substantive negative probe flips `0 < cFrac s` to `cFrac s < 0`
(`research/T13/probes/rev344_constant_mutation.lean:7-12`).  Lean rejects the
proof for the expected changed conclusion, not because an argument was removed:

```text
../research/T13/probes/rev344_constant_mutation.lean:12:2: error: Type mismatch
  constant_pos_finite s hs0 hs1
has type
  0 < cFrac s ∧ cFrac s < ⊤
but is expected to have type
  cFrac s < 0 ∧ cFrac s < ⊤
```

## 3. Gaps

The lane honestly does not prove the other three API fields.  Their exact
statements remain visible as explicit arguments of the conformance record
constructor at `research/T13/probes/constant_endpoints_closes.lean:159-177`;
they are not smuggled into the shipped module as named assumptions.  This is
the scope stated by the brief, not a defect in the three delivered fields.

The worker's report says Mathlib has no `lintegral` radial-reduction theorem and
records its Bochner-integrability workaround
(`research/T13/REPORT_344.md:70-72`).  Searches found the Bochner declarations
used by the implementation but no radial `lintegral` counterpart.  The required
whole-Section4 gap search was also empty:

```text
$ rg -n -i 'wholeSpace_identity|torus_identity|LocalizationAPI|cFrac|periodicKernel|IReal|ITorus|single.copy|periodiz.*support|lintegral.*radial|radial.*lintegral' formalization/NSFormalization/Section4
(no output; exit 1)
```

The broader required-tree search finds these names only in T13's canonical
vocabulary and this new module, not an overlooked Section4 theorem.  The report
does not otherwise claim that a needed endpoint or constant lemma is absent
from the tree.

No target gap remains for lane 344.

## 4. Commands and results

All Lean commands were run after `. scripts/lean-env.sh`, from `verification/`,
with `LEAN_NUM_THREADS=6`.

### Module build

```text
$ cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T13.ConstantEndpoints
⚠ [8778/9159] Replayed NSFormalization.Source.FiniteHilbertBochner
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
⚠ [9319/9357] Replayed NSFormalization.Source.RealSobolev
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
⚠ [9323/9357] Replayed NSFormalization.Paper3.SpatiallyCompactTime
warning: NSFormalization/Paper3/SpatiallyCompactTime.lean:88:19: `ContinuousLinearMap.sub_apply` has been deprecated: Use `sub_apply` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.sub_apply` to `sub_apply x`).
⚠ [9330/9357] Replayed NSFormalization.Paper3.RealPositiveDensity
warning: NSFormalization/Paper3/RealPositiveDensity.lean:67:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:76:63: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:88:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:100:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
⚠ [9333/9357] Replayed NSFormalization.Paper3.RealVectorPositiveDensity
warning: NSFormalization/Paper3/RealVectorPositiveDensity.lean:29:5: Variable name `hc` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hc

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [9343/9357] Replayed NSFormalization.Source.PacketForceExtension
warning: NSFormalization/Source/PacketForceExtension.lean:44:25: `if_pos` has been deprecated: Use `ite_eq_left` instead
⚠ [9346/9357] Replayed NSFormalization.Source.ViscosityPacket
warning: NSFormalization/Source/ViscosityPacket.lean:34:63: This simp argument is unused:
  Function.comp_def

Hint: Omit it from the simp argument list.
  [apply] simp [viscosityVelocity, dilateField, viscosityHomeomorph, Prod.map]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
Build completed successfully (9357 jobs).
```

All warnings above are replayed from dependencies; none names
`ConstantEndpoints.lean`.  The target module has zero errors and zero warnings.

### Direct typechecks

```text
$ LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T13/ConstantEndpoints.lean
(no output; exit 0)

$ LEAN_NUM_THREADS=6 lake env lean ../research/T13/probes/constant_endpoints_closes.lean
(no output; exit 0)
```

### Axiom audit

```text
$ LEAN_NUM_THREADS=6 lake env lean ../research/T13/axioms_constant_endpoints.lean
'NSFormalization.Section3.T13.continuous_spaceCoord' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T13.abs_spaceCoord_le_norm' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T13.npow_mul_rpow_of_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T13.norm_exp_sub_one_sq_le_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T13.norm_exp_sub_one_sq_le_four' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T13.norm_exp_sub_one_sq_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T13.cFracRadial' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T13.cFracRadial_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T13.integrableOn_cFracRadial_Ioo' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T13.integrableOn_cFracRadial_Ici' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T13.integrable_cFracRadial' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T13.measurable_cFrac_integrand' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T13.cFrac_integrand_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T13.cFrac_lt_top' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T13.cFrac_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T13.fundamentalCubeInterior' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T13.isOpen_fundamentalCubeInterior' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T13.isClosed_fundamentalCube' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T13.measurableSet_fundamentalCube' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T13.convex_fundamentalCube' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T13.volume_frontier_fundamentalCube' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T13.fundamentalCubeInterior_subset_interior' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T13.interior_subset_fundamentalCubeInterior' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T13.interior_fundamentalCube' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T13.latticeVector_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T13.eq_zero_of_mem_cube' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T13.periodize_eq_of_mem_cube' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T13.periodize_eventuallyEq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T13.tsupport_subset_cube' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T13.fderiv_eq_zero_of_notMem_tsupport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T13.endpoint_zero_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T13.endpoint_one_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T13.constant_pos_finite' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T13.endpoint_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T13.endpoint_one' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Every one of the 35 lines is exactly `[propext, Classical.choice, Quot.sound]`.

### Repository check

`make check` exited 0.  Its full output is a 1785368-byte architecture JSON;
the exact first and last lines were:

```text
$ make check
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 45,
  "source_counts": {
    "formalization": 590,
    "vendor/NavierStokesAndEuler": 2486,
    "vendor/HeliCorgi": 129
  },
  "source_manifest_entries": 2975,
  "missing_copied_imports": [],
  "citation_interfaces_reachable": [],
  "tokens_in_copied_umbrella_closure": [
...
      "NavierStokes.WeightedQuotients",
      "NavierStokes.WeightedRadialPrimitive",
      "NavierStokes.ZerothStressIdentity",
      "TestSupport.Axioms",
      "Tests.TorusData"
    ]
  },
  "base_compatibility_checked": false,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.054s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
```

Neither the lane commit nor the required triple-dot diff touches
`verification/`.  Therefore the brief's conditional `scripts/gates.sh` and
`check_contracts.py --base-ref origin/erenup/integration-section3` gates are not
applicable to this lane.

Fixes required: none.
