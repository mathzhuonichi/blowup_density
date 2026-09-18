ACCEPT-WITH-NOTES

## What the lane claims

The report claims that `torusPairingBound_advection` proves the nonlinear
pairing estimate with the explicit constant
`15 * 4^(m/2) * sqrt (∑ W⁻²)`, and that the classical specialization is
lane 335's `hpair` (`research/T11/REPORT_336.md:10-26`).  It also claims an unconditional
`PeriodicContinuationAPI.higherOrderBound`, plus carrier, reweight, physical,
and projected companion bounds (`research/T11/REPORT_336.md:28-42`).

The paper target is exactly the high-order nonlinear term in
`paper/sections/appendix-a-local-theory.tex:132-137`: the factors are
`‖u‖_{H²}`, `‖u‖_{H^m}`, and `‖∇u‖_{H^m}`.  The lane-335 consumer binder is
`formalization/NSFormalization/Section3/T11/EnergyIdentity.lean:897-907`, and
the lane's `torusPairingBound_classical` has that same binder and RHS at
`formalization/NSFormalization/Section3/T11/PairingBound.lean:1713-1723`.
The low-level advection theorem honestly exposes the order-`m+1` datum and the
coefficient-convolution hypothesis at `PairingBound.lean:1580-1593`; the smooth
slice theorem discharges that hypothesis using the Fourier convolution identity
at `PairingBound.lean:1696-1707` and `1644-1690`.

The carrier theorem has the stated `r-1` pairing and explicit constant at
`PairingBound.lean:1000-1024`, with the integer-order wrapper at
`1026-1034`.  The projected theorem correctly requires a solenoidal partner at
`PairingBound.lean:1199-1208`.  The claimed API field is copied verbatim in the
probe (`research/T11/probes/pairing_bound_closes.lean:11-13`) and is implemented
by `torusHigherOrderBound` at `PairingBound.lean:1734-1749`, matching the API
field `research/T11/probes/api_on_canonical.lean:112-121`.

The non-vacuity witness is substantive: the shear datum is nonzero and all
three RHS factors are strictly positive in
`research/T11/probes/pairing_bound_closes.lean:223-258`, and it also checks the
projected estimate.  The module has no executable forbidden admissions or
`maxHeartbeats` settings (`PairingBound.lean:1-1751`; the only `rg` hit for
`sorry|axiom` is explanatory prose at line 91).  Both local instances are
explicitly named (`PairingBound.lean:106-110`).

## What is in Lean

`formalization/NSFormalization/Section3/T11/PairingBound.lean` is new relative
to `origin/erenup/integration-section3`; the diff contains no existing Lean
module, contract, binding, or test changes.  The source has 31 public
declarations and two named local instances; the conformance file checks all 33
(`research/T11/axioms_pairing_bound.lean:1-136`) and its `#guard_msgs` assertions
require exactly `[propext, Classical.choice, Quot.sound]`.  The module and the
two normal probes typecheck, and the report's main statements are therefore
not merely restated in prose.

## Gaps and notes

1. **Documentation correction (one line).**  The report says “the tree only had
   `r = 3`” (`research/T11/REPORT_336.md:32`) and ATTEMPTS labels `∑ W⁻²` “not in the tree”
   (`research/T11/ATTEMPTS_PAIRING_BOUND.md:81-88`).  A direct `grep -rn` of the required
   Section 4 tree is empty, but the broader required tree already contains the
   equivalent H² inverse-weight definition and summability theorem:
   `formalization/NSFormalization/Paper1/PeriodicH2Embedding.lean:31-35` and
   `265-268`.  The new result is genuinely stronger because it proves every
   real exponent `r > 3/2` (`PairingBound.lean:173-220`), but the one-line claim
   should say that the **exported `PeriodicInverseWeightSummable` theorem** only
   had `r = 3`, while `PeriodicH2Embedding` separately supplies the `r = 2`
   case.

2. **Documentation correction (one line).**  REPORT_336 says the module has
   “30 private helpers” (`research/T11/REPORT_336.md:46-49`), but counting the private
   declarations in the source gives 59 (`PairingBound.lean:117-1585`, including
   the private carrier and advection lemmas).  Correct the count; it has no
   proof or API impact.

3. **Clarify the form-identification gap (one line).**  The report/ATTEMPTS
   says the advection and divergence forms are not identified
   (`research/T11/REPORT_336.md:74-76`; `research/T11/ATTEMPTS_PAIRING_BOUND.md:322-326`).  This is true
   for the missing *coefficient-carrier datum bridge*, but the tree already has
   the physical-field identity
   `formalization/NSFormalization/Section4/A01/ConvectionDivergence.lean:111-118`
   (and `Section3/T11/LocalTheory.lean:33-35` aliases the torus divergence
   field).  State explicitly that only the carrier-level bridge is absent.

4. The non-vacuity block is a named theorem rather than a Lean `example`
   (`research/T11/probes/pairing_bound_closes.lean:226`).  If the brief's word
   “example” is literal, rename it to `example` or add a one-line anonymous
   example invoking it; mathematically the current witness is adequate.

No substantive theorem fix is required for these notes.  The only unused
integer hypothesis is the intentionally preserved API-shaped `hm` in the
carrier wrapper (`PairingBound.lean:1027-1034`); it does not weaken or vacuously
prove the main classical statement.

## Commands and results

All commands were run read-only with `. scripts/lean-env.sh`,
`LEAN_NUM_THREADS=6`, and `lake` from `verification/`.

```text
bash -lc '. scripts/lean-env.sh && cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.PairingBound'
/home/ping/.profile: line 31: /data/ping/agent-os/ucoworker-cicd/cargo/env: No such file or directory
Build completed successfully (9995 jobs).
exit 0

bash -lc '. scripts/lean-env.sh && cd verification && LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T11/PairingBound.lean'
/home/ping/.profile: line 31: /data/ping/agent-os/ucoworker-cicd/cargo/env: No such file or directory
exit 0

bash -lc '. scripts/lean-env.sh && cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/T11/probes/pairing_bound_closes.lean'
/home/ping/.profile: line 31: /data/ping/agent-os/ucoworker-cicd/cargo/env: No such file or directory
exit 0

bash -lc '. scripts/lean-env.sh && cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/T11/axioms_pairing_bound.lean'
/home/ping/.profile: line 31: /data/ping/agent-os/ucoworker-cicd/cargo/env: No such file or directory
exit 0
```

The module/probe commands emit no Lean diagnostics; the build's replayed
warnings are from pre-existing dependencies, not this module.  `make check`
completed with the exact final lines:

```text
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.046s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
```

The full lane gates command
`BASE_REF=origin/erenup/integration-section3 LEAN_NUM_THREADS=6 scripts/gates.sh NSFormalization.Section3.T11.PairingBound`
also passed:

```text
== make test-mutations
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
== check_contracts
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
== gates OK
```

The explicit contract check with `--base-ref origin/erenup/integration-section3`
also ended with `"base_compatibility_checked": true` and exit 0.  `git diff
--check` returned `EXIT:0`; the changed-name audit was exactly the six new lane
artifacts plus the required append-only `research/T11/T11_SPLIT.md` row:

```text
formalization/NSFormalization/Section3/T11/PairingBound.lean
research/T11/ATTEMPTS_PAIRING_BOUND.md
research/T11/REPORT_336.md
research/T11/T11_SPLIT.md
research/T11/axioms_pairing_bound.lean
research/T11/probes/pairing_bound_closes.lean
```

For the required substantive negative check, the scratch probe
`research/T11/probes/rev336_mutated_constant.lean:9-20` changes the main RHS
constant from `torusPairingConstant m` to `0`.  Lean fails at line 20 with:

```text
error: Type mismatch
  torusPairingBound_classical
has type
  ∀ (ν : ℝ),
    0 < ν →
      ∀ a ∈ initialClassT,
        ∀ f ∈ forceClassT,
          ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T) (m : ℕ),
            3 ≤ m →
              ∀ t ∈ Set.Ioo 0 T,
                ∀ (Gm Nm : ↥(PeriodicSobolev ↑m)),
                  IsPeriodicDatum (↑m) (fun x => w.velocity (t, x)) Gm →
                    IsPeriodicDatum (↑m) (fun x => convectionFieldT w.velocity (t, x)) Nm →
                      |torusRealPairing Gm Nm| ≤
                        torusPairingConstant ↑m * torusSobolevNormAt 2 w.velocity t *
                            torusSobolevNormAt (↑m) w.velocity t *
                          torusGradientNormAt (↑m) w.velocity t
but is expected to have type
  ∀ (ν : ℝ),
    0 < ν →
      ∀ a ∈ initialClassT,
        ∀ f ∈ forceClassT,
          ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T) (m : ℕ),
            3 ≤ m →
              ∀ t ∈ Set.Ioo 0 T,
                ∀ (Gm Nm : ↥(PeriodicSobolev ↑m)),
                  IsPeriodicDatum (↑m) (fun x => w.velocity (t, x)) Gm →
                    IsPeriodicDatum (↑m) (fun x => convectionFieldT w.velocity (t, x)) Nm →
                      |torusRealPairing Gm Nm| ≤
                        0 * torusSobolevNormAt 2 w.velocity t * torusSobolevNormAt (↑m) w.velocity t *
                          torusGradientNormAt (↑m) w.velocity t
```

This is a real statement mutation, not argument deletion, and confirms the
claimed constant is load-bearing.
