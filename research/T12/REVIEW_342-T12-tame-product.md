ACCEPT-WITH-NOTES

## What the lane claims

The worker claims the scalar torus half of `eq:Rproduct`, with an explicit
positive family `tameProductConst`, and says the API field is discharged
verbatim and without a named input (`research/T12/REPORT_342.md:5-26,
110-116`).  The paper target is exactly the scalar inequality for integer
`m ≥ 2` in `paper/sections/appendix-a-local-theory.tex:8-12`; the canonical
API fixes `Cproduct` and `Cproduct_pos` before the field and uses the stated
quantifier order in `research/T12/probes/api_on_canonical.lean:41-52,119-130`.

The report also claims an `L²`-representation route for extending the smooth
convolution identity, construction of the order-`m` product datum, and a
genuine two-mode non-vacuity witness (`research/T12/REPORT_342.md:28-86,
104-108`).

## What is in Lean

The declarations are present with the claimed statements:

- `tameProductConst` is exactly
  `4 ^ (m/2) * sqrt torusInverseWeightSum` at
  `formalization/NSFormalization/Section3/T12/TameProduct.lean:571-574`, and
  `tameProductConst_pos` proves positivity at `:575-580`.  The cited tail is
  positive and summable in `formalization/NSFormalization/Section3/T11/PairingBound.lean:221-231`,
  while the factor `4^a` is the available Peetre bound at `:233-238`.
- The main theorem has the exact API spelling and no additional hypothesis at
  `formalization/NSFormalization/Section3/T12/TameProduct.lean:587-595`.
  The proof obtains representing data from finite totalized norms
  (`:600-605`), proves the low-factor `ℓ¹` estimate from the order-two datum
  (`:410-443`), applies the lattice Young estimate (`:241-328`), and builds
  the product datum and its periodic/integrable witnesses (`:643-693`).
  Thus the left-hand norm is not made vacuous by silently assuming an empty
  product datum.
- The smooth-to-`H^m` convolution extension is stated at
  `:496-508` and proved from the a.e. Fourier-series identity at `:459-492`,
  then specialized to real scalar factors at `:552-567`.  This is the
  report's stated `L²`, not density, route.
- The non-vacuity constructor is at `:732-796`; the probe supplies the
  conjugate-symmetric two-mode family, proves membership at every order, and
  instantiates the API field at
  `research/T12/probes/tame_product_closes.lean:35-139`.
- The conformance file audits all 28 exported declarations listed at
  `research/T12/axioms_tame_product.lean:12-39`; the rerun printed only
  `[propext, Classical.choice, Quot.sound]` for each.  No declaration in the
  new TameProduct module uses `sorry`, `admit`, `axiom`, `native_decide`, or
  `maxHeartbeats`; the only textual `axiom` hit is the explanatory comment at
  `formalization/NSFormalization/Section3/T12/TameProduct.lean:59`.

The branch's own lane commit changes only the six paths shown by
`git diff --name-status HEAD^ HEAD`: the new T12 module, its probe, axioms and
attempts files, the report, and the append-only comparison row.  The broader
`git diff --name-only origin/erenup/integration-section3...HEAD` also shows the
six inherited T11/339 paths, because this lane is stacked on merge commit
`a67e3467`; those are not edits made by commit `f4978ce1`.

## Gaps

The report's remaining gaps are honest for this lane.  The vector/tensor
statement is not delivered in the T12 periodic carriers, and the one-sided
convolution helper deliberately has no symmetric wrapper
(`research/T12/REPORT_342.md:117-130`).  The whole Section 4 tree was grepped
before accepting this claim: it does contain R³ analogues
`scalarSobolevENorm_component_le` and
`sobolevENorm_le_sum_components` at
`formalization/NSFormalization/Section4/A03/VectorTameProduct.lean:94-107`
and `tameProductVector` at `:270-278`, but no `MemPeriodicHmVector` or
periodic scalar/vector carrier bridge.  Therefore the residual is specifically
the T³ component bridge, not an assertion that those R³ names do not exist.

The separate `L¹` Fourier-uniqueness item remains open exactly as reported;
the reconciliation lists it as dependency (2) at
`research/T12/COMPARISON.md:40-42`, while this proof only needs the `L²`
identity.  No residual named `Prop` input occurs in the delivered theorem or
module (`research/T12/ATTEMPTS_TAME_PRODUCT.md:105-108`).

Two report-level one-line fixes are requested.  First, change the claimed
“0 errors, 0 warnings” build result at `research/T12/REPORT_342.md:145-146`
to note that a fresh replay emitted dependency linter warnings (none from
TameProduct itself) while still completing successfully.  Second, qualify the
vector-gap sentence at `:117-123` as “T³ periodic carrier/component bridges
not proved here”; the R³ A03 declarations cited above are already in the tree.

## Commands and results

All commands used `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, and ran Lake
from `verification/`.

```
lake build NSFormalization.Section3.T12.TameProduct
Build completed successfully (9996 jobs).
```

The fresh build replay printed existing dependency linter warnings (for
example `FiniteHilbertBochner`, `PeriodicSobolevHilbert`, and vendor files),
but no warning from TameProduct and no error.  Direct typechecking was silent:

```
lake env lean ../formalization/NSFormalization/Section3/T12/TameProduct.lean
(no output; rc=0)
lake env lean ../research/T12/probes/tame_product_closes.lean
(no output; rc=0)
lake env lean ../research/T12/axioms_tame_product.lean
(stdout consists of the following 28 lines, each with exactly the standard
axiom set; the long convolution line wraps in Lean's terminal output)
'NSFormalization.Section3.T12.torusShift_summable_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.torusShift_tsum' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.torusConv_comm' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.conv_comm_summable' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.torusYoungConvolution' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.scalarAbsCoeff' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.scalarAbsCoeff_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.scalarDatum_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.periodicScalarSobolevENorm_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.exists_scalarDatum' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.scalarDatum_norm_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.scalarDatum_energy' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.scalarOrderDown' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.scalarOrderDown_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.scalarOrderDown_isDatum' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.scalarAbsCoeff_summable' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.memLp_lift_ofReal' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.torusLift_ae_eq_series' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.periodicFourierCoeff_mul_of_series' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.scalarCoeff_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.tameProductConst' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.tameProductConst_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.tameProduct' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.scalarOfCoeff' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.scalarOfCoeff_ofReal' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.scalarOfCoeff_periodic' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.scalarOfCoeff_coeff' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.memPeriodicHmScalar_ofCoeff' depends on axioms: [propext, Classical.choice, Quot.sound]
lake env lean ../research/T12/probes/api_on_canonical.lean
(no output; rc=0)
```

`make check` completed with the repository's existing architecture report and
ended with:

```
.............
----------------------------------------------------------------------
Ran 13 tests in 0.047s

OK
45 work items: ownership, contract registration and task cards consistent.
```

The full gate script was also run with the requested base:

```
BASE_REF=origin/erenup/integration-section3 scripts/gates.sh NSFormalization.Section3.T12.TameProduct
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
== gates OK
```

The required substantive negative probe is
`research/T12/probes/rev342_mutation.lean`.  It weakens the main guard from
`2 ≤ m` to `1 ≤ m`; Lean rejects `exact tameProduct` with the expected type
mismatch, showing that the order guard is load-bearing:

```
../research/T12/probes/rev342_mutation.lean:21:2: error: Type mismatch
  tameProduct
has type
  ∀ (m : ℕ),
    2 ≤ m →
      ∀ (a b : Space → ℝ),
        MemPeriodicHmScalar m a →
          MemPeriodicHmScalar m b →
            (periodicScalarSobolevENorm ↑m fun x => a x * b x) ≤
              ENNReal.ofReal (tameProductConst m) *
                (periodicScalarSobolevENorm 2 a * periodicScalarSobolevENorm (↑m) b +
                  periodicScalarSobolevENorm 2 b * periodicScalarSobolevENorm (↑m) a)
but is expected to have type
  ∀ (m : ℕ),
    1 ≤ m →
      ∀ (a b : Space → ℝ),
        MemPeriodicHmScalar m a →
          MemPeriodicHmScalar m b →
            (periodicScalarSobolevENorm ↑m fun x => a x * b x) ≤
              ENNReal.ofReal (tameProductConst m) *
                (periodicScalarSobolevENorm 2 a * periodicScalarSobolevENorm (↑m) b +
                  periodicScalarSobolevENorm 2 b * periodicScalarSobolevENorm (↑m) a)
```

The mutation is intentionally outside the committed lane code; it is the only
additional probe file created by this read-only review.
