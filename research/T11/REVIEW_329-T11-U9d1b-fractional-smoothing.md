ACCEPT-WITH-NOTES

## What the lane claims

The worker claims an unconditional fractional heat estimate, with no named
`Prop` input (`research/T11/REPORT_329.md:3-7`).  The claimed symbol is
`W(k)^(3/4) exp(-ν t Λ(k))`, with
`torusFracConst ν T = (ν*T + (3/4)*exp(-1))^(3/4)` and kernel
`(ν*t)^(-3/4)` (`research/T11/REPORT_329.md:9-31`).  The requested Sobolev
conventions agree with the paper's torus weight
`(1+4π²|k|²)^s` (`paper/sections/01-introduction.tex:80-102`) and the canonical
tree definition (`formalization/NSFormalization/Section3/T10/PeriodicData.lean:66-98`).

The lane further claims the order shift is the canonical reweighting of the
heat image, not an index-only equality (`research/T11/REPORT_329.md:33-57`), a
bounded linear map and operator bound (`research/T11/REPORT_329.md:59-71`), an
integrable endpoint kernel and exact interval mass (`research/T11/REPORT_329.md:73-84`),
and strong continuity on `Ioc 0 T` (`research/T11/REPORT_329.md:86-102`).  Those
are the right mathematical objects for the mild formula's heat factor in the
paper (`paper/sections/appendix-a-local-theory.tex:109-116`).

## What is in Lean

The module contains the claimed definitions and theorems.  In particular:

- `torusFracConst`, `torusFracKernel`, and `torusFracSymbol` are defined at
  `formalization/NSFormalization/Section3/T11/FractionalSmoothing.lean:81-92`;
  `torusFracSymbol_le` has precisely the stated hypotheses and conclusion at
  `:94-145`.
- The scalar maximum is stated without extra assumptions beyond `0 ≤ y` at
  `:56-77`.  The smoothing datum, coefficient identity, norm estimate, and
  reweighting relation are at `:198-235`.  The latter matches the tree's exact
  `IsPeriodicReweight` definition (`PeriodicData.lean:209-214`) and the existing
  heat/multiplier APIs (`LocalExistenceProbe.lean:43-64`, `:94-115`).
- Solenoidality, the CLM, its coefficient identity, pointwise estimate, and
  operator-norm estimate are at `:237-286`.  The CLM is genuinely bounded via
  `torusMultiplierCLM`; it is not an alias or an unproved field.
- Kernel factorization, `IntegrableOn`, interval integrability, and the exact
  integral are at `:288-329`.  The interval orientation is `0..t`, and the
  theorem correctly allows `t = 0` (both sides are zero).
- The total path and the consumer-facing continuity theorem are at `:331-394`.
  The proof factors through the already proved joint heat continuity rather
  than asserting continuity by an unproved coefficient limit.
- The module's constant-mode witness is at `:396-428`; the probe constructs a
  genuine conjugate pair at `k₀ = (1,0,0)` and proves a nonzero output for
  nonzero amplitude (`research/T11/probes/fractional_smoothing_closes.lean:28-82`).
  This is non-vacuous and respects the real-subspace condition
  (`PeriodicData.lean:78-92`).

No forbidden token or heartbeat option occurs in the new module; the scoped
check was clean.  The base-range name check shows only the new module and lane
records were added (`git diff --name-only origin/erenup/integration-section3...HEAD`);
no existing Lean module was edited.  The guarded axiom file lists all 32 named
module declarations (`research/T11/axioms_fractional_smoothing.lean:8-134`).

## Gaps

The worker is honest that `TorusHalfStepInput` remains open
(`research/T11/REPORT_329.md:125-133`).  This matches its own exact residual
statement in `Persistence.lean:165-186`: the endpoint Duhamel argument and the
real-order bilinear estimate are part of that input, not consequences of a
linear multiplier bound.  The nearest tree result is only the order-3 torus
convection estimate (`formalization/NSFormalization/Section3/T11/ConvolutionBound.lean:272-293`,
`:348-360`).  I grepped the complete required `Section4` tree and found no
torus real-order `H^r × H^r → H^(r-1)` heat/Duhamel theorem; the Section4 product
results are integer-order or different whole-space carriers
(`formalization/NSFormalization/Section4/A03/RealAngularProduct.lean:213-224`,
`formalization/NSFormalization/Section4/A03/OuterTameProduct.lean:319-331`).
The other declared gaps—no physical-field theorem and no gain-3/2 contract
instance—are accurately scoped in `REPORT_329.md:134-145` and do not contradict
the brief's coefficient-level deliverable.

The only required corrections are documentation-only:

1. `research/T11/REPORT_329.md:114-116` says “2 named local instances, 8 defs,
   22 theorems.”  The module actually has 2 local instances, 6 `def`s, and 24
   theorems (32 audited declarations); change that one table entry.
2. `research/T11/REPORT_329.md:155-156` says the build's only warnings are in
   `Paper1/PeriodicLocalLifespan.lean`.  The rerun also replayed pre-existing
   warnings in `Source/FiniteHilbertBochner`, `Paper1/PeriodicSobolevHilbert`,
   `Formal.EndpointSafeTwoSpacePicard`, `Paper1/LocalizationBoundary`,
   `Paper1/PeriodicH2Embedding`, `Source/RealSobolev`, and other dependency
   files; replace that sentence with “pre-existing dependency warnings; no
   warning originated in FractionalSmoothing.”
3. `research/T11/REPORT_329.md:70-71` says the CLM `_norm_le` is tied to the
   datum construction “by `rfl`.”  Only `_eq` and `_apply` are `rfl` in the
   module (`FractionalSmoothing.lean:262-278`); `_norm_le` is a theorem invoking
   the datum estimate.  Remove “by `rfl`” from that sentence.
4. `research/T11/REPORT_329.md:146-148` says “both new Lean files,” although
   the deliverables include the module, the closing probe, and the axiom-audit
   file (`REPORT_329.md:110-119`).  Change it to “all three new Lean files.”

These are exact one-line report fixes; no Lean change is required.

## Commands and results

All Lake commands below were run from `verification/` after sourcing
`. scripts/lean-env.sh`, with `LEAN_NUM_THREADS=6`.

```text
$ lake build NSFormalization.Section3.T11.FractionalSmoothing
Build completed successfully (9974 jobs).
```

The build replayed the pre-existing dependency warnings listed above; the new
module itself emitted none.

```text
$ lake env lean ../formalization/NSFormalization/Section3/T11/FractionalSmoothing.lean
(no output; exit 0)
$ lake env lean ../research/T11/probes/fractional_smoothing_closes.lean
(no output; exit 0)
$ lake env lean ../research/T11/axioms_fractional_smoothing.lean
(no output; exit 0; all 32 #guard_msgs checks pass)
```

The required root check passed.  Its exact final checks were:

```text
.............
----------------------------------------------------------------------
Ran 13 tests in 0.045s

OK
45 work items: ownership, contract registration and task cards consistent.
```

The broader gate command was also run with the integration-section3 base:

```text
$ BASE_REF=origin/erenup/integration-section3 LEAN_NUM_THREADS=6 scripts/gates.sh NSFormalization.Section3.T11.FractionalSmoothing
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
== check_contracts
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
== gates OK
```

The substantive negative probe was run independently.  It removes the
`(3/4)e^{-1}` term from the main constant and attempts to reuse the original
theorem; Lean rejects it with the expected statement mismatch:

```text
../research/T11/probes/rev329_negative_constant.lean:19:2: error: Type mismatch
  torusFracSymbol_le hν ht htT k
has type
  torusFracSymbol ν t k ≤ torusFracConst ν T * torusFracKernel ν t
but is expected to have type
  torusFracSymbol ν t k ≤ (ν * T) ^ (3 / 4) * torusFracKernel ν t
```

The mutation is substantive (the constant is strengthened), not an omitted
argument.  The lane's proof and all required gates therefore pass, subject only
to the two report-line corrections above.
