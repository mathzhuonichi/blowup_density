ACCEPT

## 1. What the lane claims

The worker claims three declarations under
`NSFormalization.Section4.A01`, with the common hypotheses displayed in
`research/A01/REPORT_179.md:9-22`:

1. `highOrder_bddAbove_of_kbnd_Ico_full`: for every integer `m ≥ 3`, the
   explicit bound
   `(sobolevNormAt m w.velocity 0 + (forceSobolevENormL1 m f).toReal) *
   exp (Cgron m ν * (256 * R^2 * T))` holds for every `t ∈ Ico 0 T`
   (`research/A01/REPORT_179.md:24-28`).
2. `highOrder_bddAbove_all_orders_Ico_full`: every order `m ≥ 3` is
   `BddAbove` on the subtype `Ico 0 T` (`research/A01/REPORT_179.md:30-32`).
3. `hOne_uniform_Ico_full`: there is a finite `K : ℝ≥0∞` bounding the
   order-one velocity norm on all of `Ico 0 T`
   (`research/A01/REPORT_179.md:34-36`).

These are the claims the brief asks for under its explicit interpretation of
the endpoint output as a bound uniform on the entire half-open horizon, not a
value assertion at `t = T`.  This interpretation agrees with the manuscript:
the continuation criterion is the finite integral on `[0,S)` followed by
smooth extension (`paper/sections/02-preliminaries.tex:105-114`), and the local
theory appendix says that Grönwall bounds every `H^m` norm uniformly up to `S`
before using the bounded `H¹` restart data
(`paper/sections/appendix-a-local-theory.tex:140-152`).  The whole-space proof
uses estimates through every finite `S` within or at the maximal lifespan
(`paper/sections/04-whole-space.tex:113-132`).

The statement claims are faithful.  The common hypotheses in the source are
exactly the reported ones (`formalization/NSFormalization/Section4/A01/GronwallEndpoint.lean:16-28`),
and the three source statements are at `:32-36`, `:44-46`, and `:57-59`.
The independent `#check @...` probe prints those same binders, quantifier order,
intervals, constants, and conclusions
(`research/A01/probes/rev179_statement_print.lean:3-5`).

No premise silently makes the result vacuous.  In particular, `hT : 0 < T`
keeps `Ico 0 T` inhabited (`GronwallEndpoint.lean:19`); `hR`, the closed
cylinder slice identification, angular invariance, and the smooth Sobolev path
are explicit named premises (`:18-26`).  The conformance example uses `T = 1`,
`q = 4`, `R = 0`, `A04.zeroSol`, and concrete zero cylinder paths, so all inputs
are jointly inhabitable and the time interval is nonempty
(`research/A01/axioms_gronwall_endpoint.lean:15-30`).

## 2. What is in Lean

The first theorem applies the existing half-open Grönwall theorem directly at
`T₀ := T` (`GronwallEndpoint.lean:37-41`).  This is permitted because the
upstream theorem requires `T₀ ≤ T`, not `T₀ < T`, and returns its result on
`Ico 0 T₀`
(`formalization/NSFormalization/Section4/A01/GronwallInstance.lean:68-78`).
Its cap is supplied by the closed-endpoint theorem, whose conclusion is
`∀ t ∈ Icc 0 T, ... ≤ 256 * R^2 * T`
(`formalization/NSFormalization/Section4/A01/AprioriRows.lean:150-160`).  Thus
the exponential contains the requested endpoint constant once, with no
interior-horizon degradation.

The all-orders result packages that explicit real number as an upper bound for
the range (`GronwallEndpoint.lean:44-52`).  The handoff lowers an order-three
datum using `lowerVectorL 3 1`, rewrites the actual order-one `sobolevENorm`,
and bounds it by `ENNReal.ofReal (‖L‖ * B)`
(`GronwallEndpoint.lean:57-79`).  It does not infer a real bound by applying
`.toReal` to a potentially infinite ENNReal, so the `⊤.toReal = 0` failure mode
does not occur.  Its conclusion is exactly the velocity premise of
`A04.restartBeyond`, including `K ≠ ⊤`
(`research/A04/Spec.lean:574-583`).

All three declarations compile and print exactly
`[propext, Classical.choice, Quot.sound]`
(`research/A01/axioms_gronwall_endpoint.lean:11-13`).  Searches of the two new
Lean files found no `sorry`, `admit`, `axiom`, `native_decide`, or
`maxHeartbeats`.  `git diff --name-only origin/erenup/integration...HEAD` lists
one new formalization module and four research records; no existing Lean
module and no `verification/` file was modified.  `git diff --check` exits 0.

## 3. Gaps

The result deliberately does not bound the total carrier's value at `T` and
does not prove a limit or an energy identity at `T`; the module states this at
`formalization/NSFormalization/Section4/A01/GronwallEndpoint.lean:4-5`, and the
worker records it at `research/A01/ATTEMPTS_GRONWALL_ENDPOINT.md:27-40`.

The substantive negative mutation changes the main interval from `Ico 0 T` to
`Icc 0 T` (`research/A01/probes/rev179_closed_endpoint_mutation.lean:31-37`).
The proof fails at `:39` for the expected mathematical reason:

```text
../research/A01/probes/rev179_closed_endpoint_mutation.lean:39:23: error: Application type mismatch: The argument
  ht.right
has type
  t ≤ T
but is expected to have type
  t < T
in the application
  ⟨ht.left, ht.right⟩
```

The report's remaining qualifications are honest: the theorem is conditional
on `‖u‖ ≤ R`, `hslice`, and `HasSmoothSobolevPath`, so it does not close the
`Kbnd(R)`/`HasAprioriBound` supply circle
(`research/A01/ATTEMPTS_GRONWALL_ENDPOINT.md:29-54`).  Force boundedness and
uniform restart helpers do exist separately—for example
`exists_boundedIntoHOne_of_memForceR` at
`formalization/NSFormalization/Section4/A04/Forcing.lean:149-162` and
`forced_uniform_restart_time` at
`formalization/NSFormalization/Section4/A01/Continuation.lean:242-263`—but this
lane does not assemble them with its velocity `K` into continuation.

As required, `grep -rn` was run over the whole
`formalization/NSFormalization/Section4` tree and also `Source/` and `Paper1/`.
For `restartBeyond|extendsBeyond`, every hit is a documentation reference:

```text
formalization/NSFormalization/Section4/A04/Forcing.lean:11:`.extendsBeyond`, `.lifespanInfiniteOfLocallyFinite` (the `L¹_t H^m` clause) and
formalization/NSFormalization/Section4/A04/Forcing.lean:12:`.restartBeyond` (the bounded-into-`H¹` clause) consume:
formalization/NSFormalization/Section4/A04/Forcing.lean:30:  `restartBeyond` also needs, is *not* free and is not claimed here — only the
formalization/NSFormalization/Section4/A04/Forcing.lean:158:§4 F1 states; matching it to the velocity's `K` — which `restartBeyond` also
formalization/NSFormalization/Section4/A01/GronwallEndpoint.lean:54:/-- The finite `ENNReal` velocity-bound input of A04's `restartBeyond`.
```

Therefore the worker's narrower “no implemented A04 `restartBeyond` /
`extendsBeyond` in this checkout” claim
(`research/A01/ATTEMPTS_GRONWALL_ENDPOINT.md:42-48`) is correct.

## 4. Commands and results

All Lean/Lake commands sourced `scripts/lean-env.sh`, used
`LEAN_NUM_THREADS=6`, and ran Lake only from `verification/`.

`lake build NSFormalization.Section4.A01.GronwallEndpoint`:

```text
exit_code=0
Build completed successfully (9982 jobs).
```

The command was not globally zero-output because Lake replayed warnings and one
info diagnostic from existing dependencies.  There was no diagnostic from
`GronwallEndpoint.lean`; the exact success line is above.

`lake env lean ../formalization/NSFormalization/Section4/A01/GronwallEndpoint.lean`:

```text
exit_code=0
output_bytes=0
```

`lake env lean ../research/A01/axioms_gronwall_endpoint.lean`:

```text
exit_code=0
'NSFormalization.Section4.A01.highOrder_bddAbove_of_kbnd_Ico_full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.highOrder_bddAbove_all_orders_Ico_full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.hOne_uniform_Ico_full' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`make check` from the worktree root exited 0.  Its architecture checks emitted
the repository's large JSON closure listing; the exact final output was:

```text
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.042s

OK
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.
```

`scripts/gates.sh NSFormalization.Section4.A01.GronwallEndpoint` exited 0.  Its
exact terminal section was:

```text
== make test-mutations
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
== check_contracts
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
== gates OK
```

Thus `check_contracts.py --base-ref origin/erenup/integration` also passed as
part of `scripts/gates.sh`, even though the diff check reported
`verification_touched=no` and the conditional standalone gate was not needed.

The negative probe command exited 1 with exactly the type mismatch pasted in
Part 3.  The statement-print probe exited 0 and printed all three declaration
types.  Final hygiene output:

```text
formalization/NSFormalization/Section4/A01/GronwallEndpoint.lean
research/A01/A3_SPLIT.md
research/A01/ATTEMPTS_GRONWALL_ENDPOINT.md
research/A01/REPORT_179.md
research/A01/axioms_gronwall_endpoint.lean
verification_touched=no
```

Fixes: none.
