ACCEPT

## 1. What the lane claims

The worker report claims nine declarations, and all nine exist with the reported statements:

- `laplacianField_divergence_zero`: pointwise `div (ΔU) = 0` from pointwise `div U = 0`
  (`formalization/NSFormalization/Section4/C01/EnstrophyIdentity.lean:48`).
- `laplacian_pressure_pairing_zero`: `⟪Δu, ∇p⟫ = 0` at `t ∈ Ioo 0 T`
  (`formalization/NSFormalization/Section4/C01/EnstrophyIdentity.lean:72`).
- `inner_enstrophy_identity_deriv`: the reported abstract inner-product identity, including all
  three hypotheses and the signs `+2`, `-2ν`, `-2`
  (`formalization/NSFormalization/Section4/C01/EnstrophyIdentity.lean:93`).
- `enstrophyDerivative_value_classical`: the carrier-B value identity
  (`formalization/NSFormalization/Section4/C01/EnstrophyIdentity.lean:111`).
- `enstrophyIdentity_classical`: the raw-integral `HasDerivAt` identity
  (`formalization/NSFormalization/Section4/C01/EnstrophyIdentity.lean:144`).
- `enstrophyIdentity_gradientSq`: the local spec-vocabulary identity
  (`formalization/NSFormalization/Section4/C01/EnstrophyIdentity.lean:165`).
- `h2TimeIntegral_strict`: real-power lower-integral finiteness for `0 < S < T`
  (`formalization/NSFormalization/Section4/C01/EnstrophyIdentity.lean:199`).
- `squaredHTwoIntegral_strict`: the same result with A04's natural-power square
  (`formalization/NSFormalization/Section4/C01/EnstrophyIdentity.lean:231`).
- `h2TimeIntegral_of_absorption`: the real-power strict-interior result with the instantiated C01
  absorption hypothesis (`formalization/NSFormalization/Section4/C01/EnstrophyIdentity.lean:246`).

This agrees with the worker's own precise qualification: E6 and the algebraic E7 row are DONE,
whereas the quantitative `h2TimeIntegral` is PARTIAL
(`research/C01/REPORT_170.md:78`, `research/C01/REPORT_170.md:94`,
`research/C01/ENERGY_SPLIT.md:117`).

### E6 fidelity

The requested draft field is

```lean
2 * advectionWork (slice w.velocity t)
  - 2 * ν * laplacianSq (slice w.velocity t)
  - 2 * pairing (slice f t) (laplacian (slice w.velocity t))
```

at `research/C01/Spec.lean:487-494`. The local theorem has, sign by sign,
`+2·advectionWork`, `−2ν·laplacianSq`, and `−2·pairing(f, Δu)` at
`formalization/NSFormalization/Section4/C01/EnstrophyIdentity.lean:168-171`.

The sign calculation is load-bearing, not documentary. E5 supplies
`d = -2⟪Δu, ∂ₜu⟫` (`formalization/NSFormalization/Section4/C01/Enstrophy.lean:195-203`), and
`momentum_split_toLp` supplies `∂ₜu = νΔu − N − ∇p + f`
(`formalization/NSFormalization/Section4/C01/MomentumCarrierB.lean:199-206`). The abstract
calculation then gives the exact three terms at
`formalization/NSFormalization/Section4/C01/EnstrophyIdentity.lean:96-104`.

Pressure cancellation is proved, not assumed by either main theorem. The lane first proves
`div (Δu) = 0` from the curl-curl identity and `div curl = 0`
(`formalization/NSFormalization/Section4/C01/EnstrophyIdentity.lean:48-68`). It then applies
`EulerOrdinarySobolev.gradient_pairing_zero`, whose actual hypotheses are a smooth gradient and
a divergence-free second field
(`vendor/NavierStokesAndEuler/Euler/OrdinaryPressureCancellation.lean:98-102`), to the packaged
pressure gradient and `Δu` (`formalization/NSFormalization/Section4/C01/EnstrophyIdentity.lean:72-86`).
The value assembly obtains its pressure hypothesis from that theorem at
`formalization/NSFormalization/Section4/C01/EnstrophyIdentity.lean:131-135`.

The paper itself says to test against `−Δu`, gives the nonlinear estimate, and derives RH1 at
`paper/sections/04-whole-space.tex:106-116`; it does not separately typeset the full
pre-inequality identity. The exact expanded identity being audited is the project specification
at `research/C01/Spec.lean:475-494`, and its signs agree with that paper derivation.

There is one non-`rfl` vocabulary bridge: the draft/contract `gradientSq` uses the gradient-tensor
norm, whereas the formalization theorem uses the raw Frobenius sum. Their equality is already
proved at `verification/Bindings/EnergyAbsorptionPartialV2.lean:61-75`. The exact full draft field
shape, including registered data types and all nominal hypotheses, compiles in
`research/C01/probes/rev170_e6_exact_shape.lean:11-25` with no output.

### E7 / `h2TimeIntegral` fidelity

The gate taken by `h2TimeIntegral_of_absorption` is exactly

```lean
∀ t ∈ Ico (0 : ℝ) S,
  ENNReal.ofReal A05.gradientL6Const * criticalL3 (slice w.velocity t)
    ≤ ENNReal.ofReal (ν / 4)
```

at `formalization/NSFormalization/Section4/C01/EnstrophyIdentity.lean:250-252`. More precisely,
V1 registers the data field `C₁` at
`verification/Contracts/V1/EnergyAbsorptionPartial.lean:151-158`; the binding sets it to
`gradientL6.Csix` at `verification/Bindings/EnergyAbsorptionPartial.lean:92-102`, and that constant
is `A05.gradientL6Const` at `verification/Bindings/GradientL6.lean:41-44`. Thus the theorem uses
the exact instantiated C01 V1 constant and the full-draft gate shape from
`research/C01/Spec.lean:576-582`.

The conclusion is not the quantitative C01 field and not an endpoint theorem. For every
`0 < S < T`, `h2TimeIntegral_of_absorption` concludes only that the real-power lower integral is
not `⊤` (`formalization/NSFormalization/Section4/C01/EnstrophyIdentity.lean:246-255`). Separately,
`squaredHTwoIntegral_strict` gives A04's natural-power spelling for every `0 < S < T`
(`formalization/NSFormalization/Section4/C01/EnstrophyIdentity.lean:231-241`), matching the
integrand in `research/A04/Spec.lean:194-203`. In other words, this is finiteness on every compact
subwindow strictly inside the solution horizon; it does not cover `S = T`, while A04's
continuation criterion needs exactly `squaredHTwoIntegral S u ≠ ⊤` at the terminal horizon
(`paper/sections/02-preliminaries.tex:105-114`).

There is no `.toReal` in any of these H² conclusions. The proof identifies the ENNReal norm with
the enorm of the continuous order-two datum path and proves its lower integral is not top
(`formalization/NSFormalization/Section4/C01/EnstrophyIdentity.lean:203-226`). The hypotheses
`_hν`, `_ha`, `_hf`, and `_habs` are deliberately underscore-named and documented as unnecessary
for the stronger strict-interior continuity argument
(`formalization/NSFormalization/Section4/C01/EnstrophyIdentity.lean:243-255`); they are shape-only,
not silently used to make the conclusion vacuous.

The conformance file supplies actual witnesses: `A04.zeroSol 1 2`, `memForceR_zero`, interior
`t = 1`, and H² window `S = 1` (`research/C01/axioms_e6e7.lean:30-50`). The zero classical solution
is a genuine `ClassicalSolutionR` constructor (`formalization/NSFormalization/Section4/A04/ZeroSolution.lean:87-105`).
Hence the hypotheses and time intervals are jointly inhabitable.

## 2. What is in Lean

Lean now contains the exact raw E6 identity and a verified bridge to the exact draft/contract
vocabulary. The pressure pairing is derived from divergence-freeness through
`gradient_pairing_zero`; it is not a new axiom or an input to the final theorem. The lower-integral
result is genuine ENNReal finiteness on all strict compact subwindows, in both real-power and
A04 natural-power spellings.

No scalar Grönwall lemma was added in this lane: the new module's declarations are exactly the
nine listed above. The existing scalar comparison is `Paper1.sqrt_energy_le_primitive`
(`formalization/NSFormalization/Paper1/ScalarEnergy.lean:22`), and its already-existing C01
generalization is `sqrt_energy_le_primitive'`
(`formalization/NSFormalization/Section4/C01/EnergyBounds.lean:174-187`). The new lane neither
duplicates nor changes either lemma.

Hygiene is clean. The only formalization file in the diff is a newly added module; no existing
Lean module was modified. There are no `sorry`, `admit`, `axiom`, or `native_decide` declarations,
and no `maxHeartbeats` setting. `research/C01/axioms_e6e7.lean:20-28` audits every new theorem,
and every declaration prints exactly `[propext, Classical.choice, Quot.sound]`.

The substantive negative mutation flips the final force-pairing sign from `−2` to `+2` while
retaining every argument and hypothesis (`research/C01/probes/rev170_force_sign_mutation.lean:10-18`).
Lean rejects it with exactly the expected derivative-value mismatch; this is not an omitted-
argument test.

## 3. Gaps

The exact C01 `h2TimeIntegral` field remains open. It permits `S ≤ T` and gives an explicit finite
`ENNReal.ofReal (Cassembly * ...)` upper bound (`research/C01/Spec.lean:576-586`); the lane proves
only `≠ ⊤` under `S < T`. `h2TimeIntegralZeroDatum` likewise remains open
(`research/C01/Spec.lean:599-607`). This is stated accurately in the worker report
(`research/C01/REPORT_170.md:99-129`) and in the split table
(`research/C01/ENERGY_SPLIT.md:123`).

The required whole-tree searches found no declarations for either missing analytic input:

```text
$ grep -rn 'enstrophyIntegralBound' formalization/NSFormalization/Section4
<no output>

$ grep -rn 'sobolevTwoFourier' formalization/NSFormalization/Section4
formalization/NSFormalization/Section4/C01/EnstrophyIdentity.lean:24:`sobolevTwoFourier` bridge and the integrated enstrophy estimate.
formalization/NSFormalization/Section4/R43/Pieces.lean:58:to C01's `h2TimeIntegral`/`sobolevTwoFourier` (`sobolevENorm 2 _ ^ (2:ℝ)`,
```

Both matches for `sobolevTwoFourier` are documentation, not declarations. Broader searches for a
Sobolev-two/Laplacian Fourier inequality and for an interval integral of `laplacianSq` found no
equivalent theorem in the Section4 tree. The retained worker probe reproduces all three residuals
at `research/C01/probes/e7_endpoint_probe.lean:10-16`.

These gaps do not change the verdict because the brief explicitly allowed the strongest provable
precursor, and the report/records do not claim the quantitative endpoint field is complete.

## 4. Commands and results

All Lean commands were run after `. scripts/lean-env.sh`, from `verification/`, with
`LEAN_NUM_THREADS=6`.

```text
$ cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.C01.EnstrophyIdentity
Build completed successfully (10324 jobs).
exit 0
```

The full build output also replayed warnings from pre-existing imported modules. There was no
warning attributed to `NSFormalization/Section4/C01/EnstrophyIdentity.lean`.

```text
$ cd verification && LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section4/C01/EnstrophyIdentity.lean
<0 bytes of output>
exit 0
```

```text
$ cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/C01/axioms_e6e7.lean
'NSFormalization.Section4.C01.laplacianField_divergence_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.C01.laplacian_pressure_pairing_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.C01.inner_enstrophy_identity_deriv' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.C01.enstrophyDerivative_value_classical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.C01.enstrophyIdentity_classical' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.C01.enstrophyIdentity_gradientSq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.C01.h2TimeIntegral_strict' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.C01.squaredHTwoIntegral_strict' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.C01.h2TimeIntegral_of_absorption' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```

`make check` produced 25,367 lines (1,042,470 bytes), exited 0, and ended exactly:

```text
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
Ran 13 tests in 0.040s

OK
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.
exit 0
```

Exact-shape positive probe:

```text
$ cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/C01/probes/rev170_e6_exact_shape.lean
<0 bytes of output>
exit 0
```

Substantive sign mutation:

```text
$ cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/C01/probes/rev170_force_sign_mutation.lean
../research/C01/probes/rev170_force_sign_mutation.lean:18:2: error: Type mismatch
  enstrophyIdentity_gradientSq w hf ht
has type
  HasDerivAt (fun s => gradientSq (slice w.velocity s))
    (2 * advectionWork (slice w.velocity t) - 2 * ν * laplacianSq (slice w.velocity t) -
      2 * pairing (slice f t) (A05.lap (slice w.velocity t)))
    t
but is expected to have type
  HasDerivAt (fun s => gradientSq (slice w.velocity s))
    (2 * advectionWork (slice w.velocity t) - 2 * ν * laplacianSq (slice w.velocity t) +
      2 * pairing (slice f t) (A05.lap (slice w.velocity t)))
    t
exit 1 (expected)
```

Worker endpoint/gap probe:

```text
$ cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/C01/probes/e7_endpoint_probe.lean
../research/C01/probes/e7_endpoint_probe.lean:13:35: error: Application type mismatch: The argument
  hST
has type
  S ≤ T
but is expected to have type
  S < T
in the application
  h2TimeIntegral_strict w hS hST
../research/C01/probes/e7_endpoint_probe.lean:15:7: error(lean.unknownIdentifier): Unknown identifier `sobolevTwoFourier`
../research/C01/probes/e7_endpoint_probe.lean:16:7: error(lean.unknownIdentifier): Unknown identifier `enstrophyIntegralBound`
exit 1 (expected)
```

Hygiene and diff checks:

```text
$ git diff --name-status origin/erenup/integration...HEAD
A formalization/NSFormalization/Section4/C01/EnstrophyIdentity.lean
A research/C01/ATTEMPTS_E6E7.md
M research/C01/ENERGY_SPLIT.md
A research/C01/REPORT_170.md
A research/C01/axioms_e6e7.lean
A research/C01/probes/e7_endpoint_probe.lean

$ git diff --check origin/erenup/integration...HEAD
<0 bytes of output>

no sorry/admit/axiom/native_decide declarations
no maxHeartbeats settings
no existing Lean module modified
verification/ untouched
```

Because `verification/` is untouched, the brief's conditional `scripts/gates.sh` and
`python3 experiments/check_contracts.py --base-ref origin/erenup/integration` gates were not
triggered. `make check` did run the ordinary architecture-level `check_contracts.py` and passed.

Fixes required: none.
