REJECT

# 1. What the lane claims

The worker report is unusually explicit that it delivered the analytic core, not the
requested field: it claims Peetre × weighted-kernel mass × Young for an abstract
weighted convolution and its cutoff specialization (`research/T22/REPORT_397.md:18-33`),
then says verbatim `cutoffMultiplier` is **not** delivered (`research/T22/REPORT_397.md:35-45`).
The lane split records the same status as `PARTIAL` and lists the residual R1–R4
(`research/T22/T22_SPLIT.md:148-159`).

The required field is not merely the analytic estimate.  The specification requires

```lean
cutoffMultiplier : ∀ (s : ℝ) (χ : Space → ℝ),
  ContDiff ℝ ∞ χ → HasCompactSupport χ →
  ∃ C : ℝ, 0 < C ∧ ∀ A : RealVectorSobolev s,
    ∃ B : RealVectorSobolev s,
      IsCutoffDatum s χ A B ∧ ‖B‖ₑ ≤ ENNReal.ofReal C * ‖A‖ₑ
```

verbatim at `research/T22/Spec.lean:140-144`; the canonical structure has the same
field at `formalization/NSFormalization/Section3/T22/Domain.lean:64-68`.
This is the field used by the paper's cutoff argument at `paper/sections/03-torus.tex:615-624`.

# 2. What is in Lean

The declarations that actually exist, with their exact statements, are:

- `besselW`, `besselW_nonneg`, and `besselW_peetre` at
  `formalization/NSFormalization/Section3/T22/CutoffMultiplier.lean:61-74`.
  `besselW_peetre` is exactly the lane-386 constant form
  `besselW s ξ ≤ peetreConst s * besselW s (ξ - y) * besselW |s| y`.
- `eLpNorm_besselWeight_scalarConvolution_le` at
  `formalization/NSFormalization/Section3/T22/CutoffMultiplier.lean:86-91`.
  Its hypotheses are an integrable weighted kernel and `MemLp` of the weighted input;
  its conclusion is the stated `ENNReal.ofReal (peetreConst s * ∫ ...)` bound.
- `cutoffMultiplierConst` and `cutoffMultiplierConst_nonneg` at
  `formalization/NSFormalization/Section3/T22/CutoffMultiplier.lean:209-217`.
  The constant is exactly `peetreConst s` times the angular Fourier kernel mass.
- `eLpNorm_cutoff_multiplier_le` at
  `formalization/NSFormalization/Section3/T22/CutoffMultiplier.lean:225-238`,
  specializing the engine to `angularFourier (fun x => (χ x : ℂ))` using the U-A2
  integrability theorem.

The proof route is faithful to the paper's displayed ratio and Young reduction
(`paper/sections/03-torus.tex:618-624`): the cited tree lemmas are
`weight_ratio_le_const` (`formalization/NSFormalization/Section3/T22/WeightRatio.lean:129-133`),
`integrable_weighted_fourier_cutoff`
(`formalization/NSFormalization/Section3/T22/CutoffKernel.lean:131-139`), and
`memLp_convolution_one_two`
(`formalization/NSFormalization/Source/YoungConvolution.lean:65-70`).

There is no declaration named `cutoffMultiplier` in the new module (the declaration
list ends with `eLpNorm_cutoff_multiplier_le` at line 225).  The required field probe
therefore reproduces the blocking error after building `Domain`:

```text
../research/T22/probes/rev397_field_target.lean:18:8: error(lean.unknownIdentifier): Unknown identifier `NSFormalization.Section3.T22.cutoffMultiplier`
```

Thus the lane does not provide an inhabitant of `BoundedDomainNormAPI`, and the exact
goal in the brief is unfulfilled.

# 3. Gaps and hygiene

1. **Critical — missing required theorem.**  The abstract engine does not construct
   `B : RealVectorSobolev s`, prove its `IsCutoffDatum` graph, or assemble the vector
   norm.  The worker's residual R1 is the general datum-level angular
   product/convolution identity (`research/T22/ATTEMPTS_UA3.md:37-54`); R2 is
   real-subspace preservation (`:56-60`); R3 is the weighted datum norm/vector
   assembly (`:62-66`); R4 is strict positivity of the chosen constant (`:68-70`).
   At minimum, the lane must add the exact field theorem (or, under an explicitly
   amended brief, complete the promised smooth-datum fallback and state the remaining
   general-datum theorem separately).  The current `PARTIAL` entry must not be consumed
   by U-Z1 (`research/T22/T22_SPLIT.md:156-159`).

2. **Moderate — R3 is overstated as wholly absent.**  A generic `PiLp` square-sum
   assembly already exists in `D01/FiniteOrderNorm.lean:257-282` (and the order-zero
   instance at `:118-127`).  What is genuinely missing is the proposed cutoff datum's
   identification with the weighted `eLpNorm` and the resulting bound; the report
   should distinguish that missing bridge from the generic `PiLp` identity.

3. **Tree-wide gap check.**  I grepped the entire
   `formalization/NSFormalization/Section4` tree before accepting the residual claims:

   - `grep -rnE 'fourier_mul_convolution_eq|smulLeftCLM|scalarConvolution' .../Section4`
     finds only `smulLeftCLM` uses in `A05/RieszShift.lean:855-883` and
     `D01/OrderZero{Curl,Symbol}.lean:337-412`; there is no angular
     `angularRealization` product-to-convolution theorem.
   - `grep -rnE 'angularRealization.*(convolution|smulLeftCLM)|...' .../Section4`
     returns no lines.
   - `grep -rnE '(realSymmetry|realSubspace).*(convolution|cutoff)|...' .../Section4`
     returns no lines; the tree does contain generic symmetry facts such as
     `angularFourier_conj` (`B02/AnnularReal.lean:47-51`), but not the R2 cutoff
     preservation theorem.
   - `grep -rnE 'PiLp\.norm_(sq_)?eq_of_L2|cutoff.*(PiLp|norm|eLpNorm)|...' .../Section4`
     finds generic `PiLp.norm_sq_eq_of_L2` uses, including
     `D01/FiniteOrderNorm.lean:257-282`, but no cutoff-specific weighted datum
     assembly.
   - `grep -rnE 'cutoffMultiplierConst|cutoffMultiplier|ENNReal\.ofReal_le_ofReal' .../Section4`
     finds no cutoff multiplier theorem or constant; its hits are unrelated generic
     `ENNReal.ofReal_le_ofReal` applications.

4. **Negative and non-vacuity checks.**  The reviewer probe
   `research/T22/probes/rev397_mutation.lean` changes the engine's positive constant to
   `0`; the attempted proof fails with the substantive type mismatch:

```text
../research/T22/probes/rev397_mutation.lean:17:2: error: Type mismatch
  eLpNorm_besselWeight_scalarConvolution_le s K g hK hg
has type
  eLpNorm (fun ξ => besselW s ξ • scalarConvolution K g ξ) 2 volume ≤
    ENNReal.ofReal (peetreConst s * ∫ (ζ : Space), besselW |s| ζ * ‖K ζ‖) *
      eLpNorm (fun η => besselW s η • g η) 2 volume
but is expected to have type
  eLpNorm (fun ξ => besselW s ξ • scalarConvolution K g ξ) 2 volume ≤
    0 * eLpNorm (fun η => besselW s η • g η) 2 volume
```

   `research/T22/probes/rev397_nonvacuity.lean` proves a concrete unit-ball indicator
   input is nonzero (`rev397A_zero`, `rev397A_ne_zero`) and finite in `MemLp`, and
   applies the cutoff engine to a `ContDiffBump` at `s = 1/2`; it elaborates with zero
   output.

5. **Hygiene.**  No `sorry`, `admit`, `axiom`, or `native_decide` occurs in the lane's
   new Lean/module/probe files; `maxHeartbeats` does not occur there.  There are no
   modified `formalization` files relative to
   `origin/erenup/integration-section3`—only new `CutoffKernel.lean` and
   `CutoffMultiplier.lean`; `verification/` is untouched.  The lane's citations to
   the paper, Spec, WeightRatio, CutoffKernel, and YoungConvolution match the lines
   above.

# 4. Commands and results

All commands used `. scripts/lean-env.sh`; every `lake` command ran from `verification/`
with `LEAN_NUM_THREADS=6`.

```text
bash scripts/lean-install.sh
... toolchain 'leanprover/lean4:v4.34.0-rc2' is already installed ...
== OK
```

```text
cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T22.CutoffMultiplier
... dependency replay warnings ...
Build completed successfully (8817 jobs).
```

```text
cd verification && LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T22/CutoffMultiplier.lean
(0 output)
cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/T22/probes/cutoff_multiplier_closes.lean
(0 output)
cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/T22/probes/rev397_nonvacuity.lean
(0 output)
```

The lane axioms file produced exactly:

```text
'NSFormalization.Section3.T22.besselW_peetre' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T22.eLpNorm_besselWeight_scalarConvolution_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T22.cutoffMultiplierConst_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T22.eLpNorm_cutoff_multiplier_le' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The required negative probe is expected to fail as quoted in §3.  `make check` exits 0;
its exact final lines are:

```text
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.042s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
```

The full gates command was also run with the lane base:

```text
BASE_REF=origin/erenup/integration-section3 LEAN_NUM_THREADS=6 scripts/gates.sh NSFormalization.Section3.T22.CutoffMultiplier
...
Mutation suite passed. This is an infrastructure check, not a PDE proof.
== check_contracts
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
== gates OK
```

Standalone `python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3`
also ended with the exact `base_compatibility_checked: true` / architecture-scope lines
shown above.  `git diff --check` exited 0.  The module build is successful, but its replay
does print pre-existing dependency linter warnings; the direct module `lake env lean` is
silent.

