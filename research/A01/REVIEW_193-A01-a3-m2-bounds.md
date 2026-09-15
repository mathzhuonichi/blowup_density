ACCEPT-WITH-NOTES

## 1. What the lane claims

The lane claims a base-order-radius construction of the all-order a-priori-bound
family, conditional on one named finite-order energy input `MildGronwall`.  The
worker report reproduces all eleven production signatures accurately: the
definitions are at `AprioriFamily.lean:147-170`, the prefix/base/lowering/cap
lemmas at `AprioriFamily.lean:16-138`, and the two family theorems at
`AprioriFamily.lean:177-256`.  I found no mismatch between those declarations
and `REPORT_193.md:18-158`.

The two notes are record/probe fixes, not defects in the proved family:

1. `probe193_wiring.lean:4-7`, `REPORT_193.md:172-174`, and
   `ATTEMPTS_A3_M2_193.md:110-114` call the lane-192 export
   `hsob_of_bounds`.  Fixed commit `3eaab5c` deleted that split export and
   exports `constructorInputs_of_bounds` at
   `3eaab5c:formalization/NSFormalization/Section4/A01/CylinderWiring.lean:137-153`.
   The exact final interface is replayed successfully in
   `probes/rev193_constructor_and_zero.lean:18-59`.
2. The gap discussion should cite the existing vendor mild-energy entry
   `EulerMildMajorantEnergy.mild_majorized_energy_subinterval`
   (`vendor/NavierStokesAndEuler/Euler/MildMajorantEnergy.lean:22-65`).  It is
   not a turnkey proof of this lane's `MildGronwall`, but it is materially more
   relevant than the report's classical-carrier diagnostic and should be the
   first lane-194 route attempted.

The mathematical target is otherwise faithful.  The paper says that one local
interval supports every higher Sobolev order
(`paper/sections/appendix-a-local-theory.tex:60-76`) and gives the actual
continuation inequality

`(d/dt) ‖u‖_{H^m} ≤ C_{m,ν}‖u‖_{H²}²‖u‖_{H^m} + ‖f‖_{H^m}`

at `paper/sections/appendix-a-local-theory.tex:127-147`.  Here `m=q+1`, exactly
as encoded by the initial, envelope, and force terms in
`AprioriFamily.lean:151-162`.  Thus the force term
`E * ‖sobolevPath F hF (q+1)‖` is an honest, explicitly stronger compact-time
supremum estimate for the paper's `L¹_t H^{q+1}` term.  It is not the draft's
sharper gained-derivative `L¹_t H^q` route.  It adds no hidden named premise:
`hF` supplies continuity in every finite order on the compact interval.  The
report states this distinction honestly at `REPORT_193.md:208-211`.

`MildGronwall` is a restriction of a standard property, not the conclusion in
disguise:

- `E,C` are quantified before `T` and `u` (`AprioriFamily.lean:147-154`).
- Its driver contains only the lowered path and fixed constants
  (`AprioriFamily.lean:159-162`), not `R₆`, `aprioriRadius`, or a bound on `u`.
- `Nat.succ_le_succ hq` is `7 ≤ q+1`; the codomain is visibly
  `SobolevSpace 1 7` in `lower_identification`
  (`AprioriFamily.lean:85-102`).  It is therefore lowering to the order-seven
  cylinder carrier used at base index six, whose norm controls physical `H²`.
- The factor `256` is exactly the square of the order-two comparison constant
  `16`: `OrderTwoCap.lean:191-207` proves the pointwise square bound and
  `OrderTwoCap.lean:209-246` integrates it to `256 * R² * T₀`.

There is no `.toReal` occurrence, `⊤` loophole, empty interval, or conclusion
hidden among the named inputs.  Every `Icc 0 T` is nonempty because `hT : 0 ≤ T`;
the singleton case `T=0` is handled separately in
`AprioriFamily.lean:37-51`.  `hR` itself forces `0 ≤ R₆`, and `hE`/`hC` are
used in the Grönwall proof (`AprioriFamily.lean:193,202-204,208,225-242`).

## 2. What is in Lean

### Base order and subwindows

The vendor theorem supplies `0<T≤S`, a path, the exact radius
`‖u₀‖+1`, and the Duhamel identity
(`vendor/NavierStokesAndEuler/Euler/QuadraticHeatLocal.lean:31-56`).
`exists_base_apriori` consumes precisely that output
(`AprioriFamily.lean:105-116`).  It does not assume an a-priori bound.

The time-prefix bookkeeping is correct.  `quadratic_mild_prefix` proves that
the restriction of a full fixed point is a fixed point for the shorter-horizon
map (`AprioriFamily.lean:16-34`); this agrees with the actual definition of
`quadraticDuhamel`, whose coefficient is evaluated through `timeInclusion`
(`vendor/NavierStokesAndEuler/Euler/QuadraticHeatLocal.lean:12-29`).  Whole-window
uniqueness is `MildUniqueness.lean:144-183`; the lane adds exactly the missing
singleton case at `AprioriFamily.lean:37-51`.  Hence every base-order competitor
on every `[0,T]⊆[0,S]` is the prefix of `u₆`
(`AprioriFamily.lean:53-82`).

### Higher orders and the final radius

The horizon-`T` lowering theorem `lower_forced_mild`
(`CommonHorizon.lean:103-151`) is applied to the restricted force at
`AprioriFamily.lean:99-102`; uniqueness then identifies the result with the
base prefix.  This is the required lane-186/lane-188 composition and does not
route through the all-order constructor.

`h2_cap_transfer` uses that identification and the base radius to obtain the
exact physical cap `256 * R₆^2 * T` (`AprioriFamily.lean:118-138`), matching
`kbnd_of_sup_bound_Icc_endpoint` (`AprioriRows.lean:150-190`).  In the main
assembly, the same constant is used directly in the scalar driver.  The proof
first bounds `k(s)` by `256*R₆²` (`AprioriFamily.lean:207-217`), integrates
and widens `t≤T≤S` to `256*R₆²*S` (`:218-224`), and bounds the constant
force integral by `S * E q * ‖F‖` (`:233-239`).  Consequently the result is
exactly

`E q * (‖u₀‖_{q+1} + S * ‖F‖_{q+1}) * exp (C q * 256 * R₆² * S)`

as defined at `AprioriFamily.lean:164-170`, neither looser nor tighter.

The quantifier order is correct: `HasAprioriBound` fixes `R` before every
`T,u` (`Horizon.lean:97-114`), and `hb_of_base` fixes `u₆,R₆,E,C,hMG` before
returning `∀ q, HasAprioriBound ...` (`AprioriFamily.lean:177-186`).

### Composition and non-vacuity

The worker's stale lane-192 probe still typechecks only because it postulates a
copied theorem parameter (`probe193_wiring.lean:19-43`).  The reviewer probe
copies the actual fixed-commit `constructorInputs_of_bounds` interface and
feeds it the exact `hb_of_base` family; it typechecks with zero output
(`probes/rev193_constructor_and_zero.lean:18-59`).

The audit's zero-data example proves its own `MildGronwall`; it does not assume
it (`axioms_a3_m2_193.lean:52-77`).  To check the lead's precise variant, the
reviewer probe separately proves the vendor base radius `1`
(`probes/rev193_constructor_and_zero.lean:113-120`), proves zero
`MildGronwall` internally (`:89-111`), and derives the all-order family with
`R₆=1` (`:122-131`).  This probe has zero output.

### Axioms and hygiene

The production module has eleven declarations and the audit prints those plus
three private zero helpers: fourteen reports total
(`axioms_a3_m2_193.lean:5-15,79-81`).  Every one is exactly
`[propext, Classical.choice, Quot.sound]`; the exact output is reproduced in
§4.  The source contains no `sorry`, `admit`, declaration `axiom`, or
`native_decide`.  Its only heartbeat override is per declaration, exactly
`400000`, with the elaboration comment immediately above it
(`AprioriFamily.lean:173-176`).

`git diff --name-only origin/erenup/integration...HEAD` shows one new production
module and records only; no pre-existing Lean module was modified.  The paper
and source citations checked above are correct.  The report's vendor lifespan
description is also accurate: the theorem chooses `ε/2` from the two Picard
budgets (`VolterraUniqueness.lean:68-92`), while the local solver fixes
`R=‖u₀‖+1` and applies those budgets (`QuadraticHeatLocal.lean:39-53`).

## 3. Gaps

The sole mathematical gap remains the nonzero proof of `MildGronwall`; scalar
Grönwall itself is discharged.  A whole-tree `rg` over
`formalization/NSFormalization/Section4` found no theorem with a
`quadraticDuhamel`/finite-Sobolev carrier and this envelope conclusion.  The
closest Section4 results are classical-carrier theorems:

- `A04.energyIdentityHigh` takes `ClassicalSolutionR`
  (`A04/EnergyIdentityHigh.lean:145-157`);
- `A04.highContinuationIntegral` also takes `ClassicalSolutionR`
  (`A04/HighContinuationIntegral.lean:85-101`);
- `A01.highOrder_bddAbove_of_kbnd` merely instantiates those classical results
  (`A01/GronwallInstance.lean:66-91`);
- lane 169 reaches only `m≤q-1`
  (`A01/DatumPathDeriv.lean:400-438`), not the required top order `q+1`.

Thus the report is correct that no *Section4 turnkey lemma* discharges the
predicate.  Its search narrative is incomplete, however, because the vendor
contains a proved full-order mild-energy route:
`regularized_word_hasDerivAt` handles top words without a top-order time
derivative premise (`Euler/RegularizedWordEquation.lean:54-70`),
`finite_cylinder_viscous_energy` is the cylinder energy identity
(`Euler/CylinderViscousEnergy.lean:24-86`), and
`mild_majorized_energy_subinterval` passes the regularization to a genuine mild
solution (`Euler/MildMajorantEnergy.lean:22-65`).  These do not already state
the lane's unweighted `H²`-driven envelope, so an adapter/nonlinear estimate is
still real work.

For lane 194, start from that vendor regularized mild-energy chain, specialize
to the constant Euclidean metric and the finite word family through order
`q+1`, and identify its scalar energy with a continuous majorant of the cylinder
norm.  For the nonlinear top-order term, reuse the registered tame estimate
`A03.outerProductTame` (`A03/OuterTameProduct.lean:165-179`) and its real
transport `A04.outerSobolevNormAt_le` (`A04/HighEnergy.lean:157-179`), then feed
the algebraic result through `A04.inner_energy_Rhigh`
(`A04/HighEnergy.lean:125-146`).  Lane 169/178's datum derivative route is too
low-order (and the all-order constructor would be circular), while the vendor
Picard ball bounds only produce the short base horizon and make a high-order
radius depend on itself; they are not the right energy entry.  The promising
entry is therefore the vendor's regularized mild-energy machinery, with A03/A04
supplying the Navier–Stokes tame top term.

The required substantive mutation changes `256` to `255` in the exponential
radius (`probes/rev193_mutation_fail.lean:14-35`).  It fails for the expected
reason, not because an argument was removed:

```text
../research/A01/probes/rev193_mutation_fail.lean:35:2: error: Type mismatch
  hb_of_base hν hS a F hF u₆ hR h₆ E C hE hC hMG
has type
  ∀ (q : ℕ) (hq : 6 ≤ q), HasAprioriBound hq hν a F hF (aprioriRadius a F hF R₆ E C q)
but is expected to have type
  ∀ (q : ℕ) (hq : 6 ≤ q), HasAprioriBound hq hν a F hF (mutatedRadius255 a F hF R₆ E C q)
```

## 4. Commands and results

All Lean shells sourced `scripts/lean-env.sh`; all Lake commands ran from
`verification/` with `LEAN_NUM_THREADS=6`.

`bash scripts/lean-install.sh` — exit 0.  Exact terminal lines:

```text
elan 4.2.4 (227caca13 2026-08-25)
info: toolchain 'leanprover/lean4:v4.34.0-rc2' is already installed
Lean (version 4.34.0-rc2, x86_64-unknown-linux-gnu, commit 6a10ac8c22beadecabdbb0919c2b50214762f91d, Release)
== lake exe cache get
Current branch: HEAD
Using cache from origin: (some leanprover-community/mathlib4)
No files to download
Already decompressed 8747 file(s)
== lake test
...
== OK
```

`lake build NSFormalization.Section4.A01.AprioriFamily` — exit 0.  Lake replayed
pre-existing dependency warnings; none points to `AprioriFamily.lean`.  Exact
ending:

```text
Build completed successfully (10022 jobs).
```

`lake env lean ../formalization/NSFormalization/Section4/A01/AprioriFamily.lean`
— exit 0, exact output:

```text
<0 bytes>
```

`lake env lean ../research/A01/axioms_a3_m2_193.lean` — exit 0, exact output:

```text
'NSFormalization.Section4.A01.quadratic_mild_prefix' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.quadratic_mild_unique_window' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.base_identification' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.hasAprioriBound_base' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.lower_identification' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.exists_base_apriori' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.h2_cap_transfer' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.MildGronwall' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.aprioriRadius' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.hb_of_base' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.hb_of_base_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private._stdin.0.NSFormalization.Section4.A01.zero_value' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private._stdin.0.NSFormalization.Section4.A01.zero_sob' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private._stdin.0.NSFormalization.Section4.A01.zero_mild' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`lake env lean ../research/A01/axioms_a3_m2.lean` — exit 0; its four lane-142
reports are also exactly the standard three axioms.

`lake env lean ../research/A01/probe193_wiring.lean` — exit 0, exact output:

```text
<0 bytes>
```

`lake env lean ../research/A01/probes/rev193_constructor_and_zero.lean` — exit
0, exact output:

```text
<0 bytes>
```

`lake env lean ../research/A01/probes/rev193_mutation_fail.lean` — exit 1 with
the exact expected error pasted in §3.

`make check` from the worktree root — exit 0.  The command emits the large
registered-contract closure JSON; its exact final checks were:

```text
  "base_compatibility_checked": false,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.039s

OK
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.
```

Hygiene command:

```text
$ rg -n --pcre2 '(^|\s)(sorry|admit|axiom|native_decide)\b' formalization/NSFormalization/Section4/A01/AprioriFamily.lean research/A01/axioms_a3_m2_193.lean research/A01/probe193_wiring.lean
<no output>
$ rg -n 'set_option maxHeartbeats' formalization/NSFormalization/Section4/A01/AprioriFamily.lean research/A01/axioms_a3_m2_193.lean research/A01/probe193_wiring.lean
formalization/NSFormalization/Section4/A01/AprioriFamily.lean:174:set_option maxHeartbeats 400000 in
```

`git diff --name-only origin/erenup/integration...HEAD` produced exactly:

```text
formalization/NSFormalization/Section4/A01/AprioriFamily.lean
research/A01/A3_SPLIT.md
research/A01/ATTEMPTS_A3_M2.md
research/A01/ATTEMPTS_A3_M2_193.md
research/A01/REPORT_193.md
research/A01/axioms_a3_m2_193.lean
research/A01/probe193_wiring.lean
```

`git diff --check origin/erenup/integration...HEAD` — exit 0, zero output.

Neither `scripts/gates.sh` nor
`python3 experiments/check_contracts.py --base-ref origin/erenup/integration`
was applicable: the exact diff above contains no `verification/` path, and the
brief makes both gates conditional on touching `verification/`.

Fixes before merge:

1. Replace the stale `hsob_of_bounds` composition claim/probe with the final
   `constructorInputs_of_bounds` interface, using
   `probes/rev193_constructor_and_zero.lean:18-59` as the checked replacement.
2. Add `Euler.MildMajorantEnergy.mild_majorized_energy_subinterval` and its
   regularized-word prerequisites to the recorded lane-194 search/route.
