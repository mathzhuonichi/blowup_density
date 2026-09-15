ACCEPT-WITH-NOTES

## 1. What the lane claims

Lane `166-R44-split`, branch `erenup/166-R44-split`, HEAD `ec56cb5`, claims a
six-row proof split for Proposition 4.4, three new conditional scalar/arithmetic
theorems, and reuse of two R43 theorems.  It does not claim to prove the final
nine-field R44 API.

The manuscript statement is exactly at
`paper/sections/04-whole-space.tex:136-144`: zero initial datum, the
inhomogeneous `L²(0,∞;H⁻¹/²)` force norm, strict lifespan past `S`, and a
radius `c ν^(3/2) exp (-C ν S)` with universal positive `c,C`
(`04-whole-space.tex:137-143`).  The proof defines `Y,Z,B` and gives the exact
weight identity at `:146-152`, eq:Rcritical2 at `:160-163`, Grönwall and first
exit at `:164-169`, and the embedding/continuation close at `:171-173`.
The reconciled final Lean API faithfully transcribes the statement:
`radiusFormula` is `research/R44/Spec.lean:224-225`, positivity is `:237`, and
the theorem field is `:266-270`.  In particular, `c,C,radius` precede all
`ν,S,f`, the norm stays in `ℝ≥0∞`, and the initial datum is literally
`fun _ => 0`.

The worker report's three claimed declarations all exist with the claimed
statements:

* `exists_rcritical2_constants` is at
  `formalization/NSFormalization/Section4/R44/Pieces.lean:40-46`.  It chooses
  `theta,c,C > 0`, proves both shrinkings, proves
  `C₃*c^2 < theta^2/4`, and fixes `C = C₂+1`; neither `ν` nor `S` occurs in
  the statement, so the choices are universal relative to the universal PDE
  constants.  This is exactly the claim at `research/R44/REPORT_166.md:7-10`.
* `radius_forces_gronwall_small` is at `Pieces.lean:76-84`.  Its premise uses
  real `rpow` `nu ^ (3/2 : ℝ)` and exponent `-(C₂+1)*nu*S`, and its conclusion
  is the claimed strict Grönwall smallness.  The square identity is proved at
  `:94-96` and the exponential estimate at `:97-107`, matching
  `REPORT_166.md:11-14`.
* `criticalSquaredNormBound_radius` is at `Pieces.lean:153-166`.  It assumes
  the conditional eq:Rcritical2-shaped inequality on `Ioo 0 T`, a prefix
  bound for `∫B²`, continuity/integrability data, and strict smallness, and
  concludes `Y t ≤ theta*nu/2` on `Icc 0 T`, exactly as claimed at
  `REPORT_166.md:15-19`.

The reused declarations also exist with the claimed exact shapes:
`R43.enorm_npow_two_eq_rpow_two` is
`formalization/NSFormalization/Section4/R43/Pieces.lean:62-63`, and
`R43.criticalL3_gate_enorm` is `:112-123`.  The new scalar proof genuinely
calls `A04.gronwall_deriv` (`Section4/A04/Gronwall.lean:172-180`) and
`Paper1.continuous_bootstrap` (`Paper1/ScalarEnergy.lean:85-88`) at
`R44/Pieces.lean:168-193`; it does not duplicate either proof.

No theorem is made vacuous by `⊤.toReal = 0`: the new module has no ENNReal
`.toReal` use at all.  Positivity guards are explicit in
`Pieces.lean:41-46,78-84,155-165`; `T=1` makes the reviewed interval nonempty in
the conformance example (`axioms_r44_pieces.lean:35-45`).  Every named
hypothesis of the three declarations is consumed in its proof
(`Pieces.lean:47-68,85-134,167-216`).  The global `Continuous Y` and
`IntervalIntegrable E'` hypotheses are genuine technical assumptions, not
vacuity devices, but their eventual PDE-level supply needs to be recorded more
precisely; see Part 3.

## 2. What is in Lean

The lane adds exactly one implementation module plus four research records;
`git diff --name-status origin/erenup/integration...HEAD` reports all five as
`A`, so no existing module or contract was modified.  The implementation is
218 lines and contains only the three public theorems above
(`Pieces.lean:40,76,153`).

The proof content is mathematically faithful to the cheap rows:

* Constant selection is before `nu,S`, and the two smallness gates are separate
  conjuncts (`Pieces.lean:43-46`).
* Radius algebra uses `nu > 0`, `S ≥ 0`, `C₂ ≥ 0`, and nonnegative `F`, so
  the rpow square and squaring of the strict radius bound are honest
  (`Pieces.lean:78-93`).
* The bootstrap retains the paper's `Ioo` energy window and `Icc` conclusion,
  starts at `Y 0 = 0`, and uses a true first-crossing argument
  (`Pieces.lean:158-171`).  The nonnegative dissipation is dropped only at
  `:189-192`; the prefix integral and exponential monotonicity are used at
  `:197-214`.

The conformance file prints all three new and both reused declarations
(`research/R44/axioms_r44_pieces.lean:15-17,49-50`).  Each reports exactly
`[propext, Classical.choice, Quot.sound]`.  Its concrete examples inhabit all
five theorem signatures (`:21-60`).  In addition, reviewer probe
`research/R44/probes/rev166_nonvacuity.lean:8-36` compiles with nonzero
`Y(t)=t/2` and nonzero `B(t)=1` on `[0,1]`, so the main scalar theorem is not
being exercised only on an empty interval or the all-zero functions.

Hygiene is clean.  A scan of the implementation, conformance file, and reviewer
probes finds no `sorry`, `admit`, `axiom`, `native_decide`, `set_option`, or
`maxHeartbeats`.  `git diff --check` is silent.  The changed-module dry run says
`Changed Lean modules: NSFormalization.Section4.R44.Pieces`, so the module is in
the repository's changed-Lean build closure.

The negative check is substantive.  Probe
`research/R44/probes/rev166_mutation_quarter_fail.lean:6-22` strengthens the
main conclusion from `Y ≤ theta*nu/2` to `Y ≤ theta*nu/4`, leaving every
hypothesis unchanged.  Lean rejects it at `:21` because the theorem produces
the former type, not the latter.  This is a changed constant in the conclusion,
not a dropped argument.

## 3. Gaps

The registration audit is correct.  In `verification/contracts.json`,
`D01.datum_lemmas_v2` V2 explicitly registers the R44 `s=-1/2,q=2,m=0`
finiteness case (`:115-122`); `A05.gradient_l6` V1 explicitly excludes the
critical half/three-halves embeddings (`:49-56`); C01 V1 supplies the absorption
vocabulary (`:181-188`) while C01 V3 still excludes eq:RH1, the Fourier
inequality, the H² assembly, and eq:Rcritical2 (`:280-287`); A04 V2 stops before
the continuation criterion (`:269-276`); and A02 V2's `exists_maximal` retains
the local-solution argument (`:159-166`, with the exact field at
`Contracts/V2/MaximalPartial.lean:139-145`).

Every claimed absence was checked by `grep -rn` over the whole
`formalization/NSFormalization/Section4` tree:

* G1 is accurately open.  The tree has Bessel-weight and lowering machinery
  (for example `D01/LerayLowering.lean:115-129`) but no declaration defining
  the R44 `J`, proving the exact `H^(3/2)` weight identity, or proving the
  negative-order `⟨f,Ju⟩` bound.  The exact missing mathematics agrees with
  the paper at `04-whole-space.tex:146-158` and the comparison at
  `research/R44/COMPARISON.md:156`.
* G2 is accurately open.  The only `Rcritical2`/`criticalSquaredNorm` hits in
  `Section4` are comments and the conditional scalar theorem in this lane
  (`R44/Pieces.lean:9,153-165`); there is no PDE derivation of
  `04-whole-space.tex:161-163`.
* G3 is accurately open if read as the norm-valued slice/integral identity.
  D01 already constructs a lowered datum path and proves its finite Bochner norm
  (`D01/HalfOrder.lean:120-173`), so this is useful input and must not be called
  wholly absent.  What the tree does not prove is continuity/integrability of
  the real function `B(t)=‖f(t)‖_{H⁻¹/²}` together with its squared prefix
  integral identity.  C01's existing result is only the order-zero `L²` slice
  (`C01/ForceSlices.lean:146-161`), exactly as the split says at
  `R44_SPLIT.md:110-112`.
* A05 V2 is not in the tree or registry.  The needed declarations remain draft
  fields `velocityCriticalL3`, `derivativeCriticalL3`, and
  `besselCriticalL3` at `research/A05/Spec.lean:366-408`; the registered scope
  expressly contains only gradient-L⁶ (`contracts.json:49-56`).
* C01 V4 is not in the tree or registry.  Its exact draft fields are
  `enstrophyIntegralBound`, `sobolevTwoFourier`, and
  `h2TimeIntegralZeroDatum` at `research/C01/Spec.lean:532-541,555-558,599-607`;
  whole-tree grep finds no corresponding theorem.
* R44 G4 endpoint gluing is not present.  Whole-tree searches for an H²/maximal
  endpoint limit or `squaredHTwoIntegral` maximal-lifespan bridge return no
  theorem.  The split correctly isolates the mismatch between fixed horizons
  and the maximal endpoint at `R44_SPLIT.md:163-167`.
* A04 `extendsBeyond` is not registered and is also **not proved in this
  checkout**.  The only exact declaration is the draft field at
  `research/A04/Spec.lean:613-617`; the registered A04 V2 scope says the
  criterion is out of scope (`contracts.json:269-276`), and whole-tree grep under
  `Section4/A04` returns only mentions in `Forcing.lean:11-12`.  The report's
  phrase “registration after its proof” at `REPORT_166.md:52` is therefore stale
  relative to this branch.
* The A02/A01 disclosure is correct.  The tree theorem itself is named
  `exists_maximal_of_localSolution` and takes the global `localSolution`
  argument at `Section4/A02/Maximal.lean:157-164`; no A01 theorem in this
  checkout supplies the final `LocalTheoryAPI.solution` contract field.

Four documentation fixes are required before merge; none changes a proved Lean
statement:

1. After `research/R44/R44_SPLIT.md:64`, add exactly: “To feed S2 this must be
   assembled as one `E' : ℝ → ℝ` with `IntervalIntegrable E' volume 0 T`;
   the pointwise existential alone does not discharge `Pieces.lean:162-163`.”
2. After `research/R44/R44_SPLIT.md:98`, add exactly: “Instantiation also owes
   either global `Continuous Y` or a continuous extension of the PDE norm path
   from `Icc 0 T`, because `Pieces.lean:158` inherits global continuity from
   `Paper1.continuous_bootstrap`.”  Replace `REPORT_166.md:29-30`'s “conditional
   only” sentence accordingly.
3. In `research/R44/R44_SPLIT.md:116`, replace `:148-160,170` by
   `:148-160,171`; in `:139`, replace `:170-171` by `:171`.  Paper line 170 is
   blank and the embedding/H¹/H² continuation step is line 171.
4. In `research/R44/REPORT_166.md:52`, replace `S registration after its proof`
   by `M+S proof and registration (no extendsBeyond theorem on this branch)`.

## 4. Commands and results

All Lean commands were run after sourcing `scripts/lean-env.sh`, one at a time,
from `verification/`, with `LEAN_NUM_THREADS=6`.

```text
$ LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.R44.Pieces
Build completed successfully (2686 jobs).
# exit 0

$ LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section4/R44/Pieces.lean
# exit 0; exact output: 0 bytes

$ LEAN_NUM_THREADS=6 lake env lean ../research/R44/axioms_r44_pieces.lean
'NSFormalization.Section4.R44.exists_rcritical2_constants' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.radius_forces_gronwall_small' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.criticalSquaredNormBound_radius' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.R43.enorm_npow_two_eq_rpow_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.criticalL3_gate_enorm' depends on axioms: [propext, Classical.choice, Quot.sound]
# exit 0; all examples also typechecked

$ LEAN_NUM_THREADS=6 lake env lean ../research/R44/probes/rev166_nonvacuity.lean
# exit 0; exact output: 0 bytes

$ LEAN_NUM_THREADS=6 lake env lean ../research/R44/probes/rev166_mutation_quarter_fail.lean
../research/R44/probes/rev166_mutation_quarter_fail.lean:21:2: error: Type mismatch
  criticalSquaredNormBound_radius hT hnu htheta hC₂ hC₃ hR hsmall hY hY0 hYnonneg hBsq hBbound hdE hE'int henergy
has type
  ∀ t ∈ Icc 0 T, Y t ≤ theta * nu / 2
but is expected to have type
  ∀ t ∈ Icc 0 T, Y t ≤ theta * nu / 4
# exit 1, expected

$ make check
python3 experiments/check_formalization_plan.py --check
Explicit axiom/admission tokens, all copied sources: 11
python3 experiments/check_contracts.py
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.045s

OK
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.
# exit 0

$ git diff --check origin/erenup/integration...HEAD
# exit 0; exact output: 0 bytes

$ python3 experiments/build_changed_lean.py --base-ref origin/erenup/integration --dry-run
Changed Lean modules: NSFormalization.Section4.R44.Pieces
# exit 0
```

`git diff --name-only origin/erenup/integration...HEAD -- verification` produced
zero output, so the conditional `scripts/gates.sh` and
`check_contracts.py --base-ref origin/erenup/integration` gates do not apply to
this lane.  No git state-changing command was run.  The only reviewer additions
are the two permitted `research/R44/probes/rev166_*.lean` files and this review.
