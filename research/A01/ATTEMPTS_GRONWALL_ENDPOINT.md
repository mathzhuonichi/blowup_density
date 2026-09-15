# Lane 179 — Grönwall endpoint (P9b)

## Result and interpretation

Row (iii-b), interpreted as a uniform high-order bound on the full `Ico 0 T`, is
closed conditionally on the existing cylinder cap hypotheses. Use
`kbnd_of_sup_bound_Icc_endpoint` on `Icc 0 T`, restrict its conclusion to
`Ico 0 T`, and instantiate `highOrder_bddAbove_of_kbnd` directly at its
`T₀ := T` (the intermediate horizon called `T₁` in the brief). Its hypothesis
is `T₀ ≤ T`, not `T₀ < T`. No limiting argument or new energy identity at `T`
is needed. The constant is exactly

`B_m = (sobolevNormAt m w.velocity 0 + (A04.forceSobolevENormL1 m f).toReal)
       * exp (A04.Cgron m ν * (256 * R^2 * T))`.

The all-orders theorem packages `B_m` as an upper bound for the range indexed
by `Ico 0 T`. `MemL1Hm` is discharged by `memL1Hm_of_memForceR`.

The A04 handoff lowers the order-three datum with the existing continuous
linear map `L := D01.lowerVectorL 3 1 (by norm_num)`. It supplies
`K := ENNReal.ofReal (‖L‖ * B_3)`, proves `K ≠ ⊤`, and proves verbatim
`∀ t ∈ Ico 0 T, sobolevENorm 1 (fun x => w.velocity (t,x)) ≤ K`.
The finite, fixed operator norm suffices; no sharp monotonicity constant is
needed. `sobolevENorm_eq` identifies the represented slice with its datum's
enorm, so no use of `⊤.toReal = 0` can make the argument vacuous.

## What remains after this lane

`ClassicalSolutionR` has a total field as its Lean carrier, but its solution
regularity is only certified on `Ico 0 T`. We prove neither an endpoint value
bound nor an endpoint limit of that field. The input `hslice` still relates
the cylinder path to the field on `Icc 0 T`, exactly as the existing cap
requires; it is not obtained from `ClassicalSolutionR` here.

The old P9b description saying an energy identity limit at `T` is necessary
is superseded for the full-half-open-bound interpretation specified in this
lane. The paper's continuation conclusion is a separate obligation. Verified
with `sed -n`: `02-preliminaries.tex:108-114` states the squared-H²-integral
criterion and extension beyond `S`; `04-whole-space.tex:113-121` gives RH1,
RL2 and the finite-endpoint discussion.

A mandatory `grep -rn` over all of `Section4/{D01,A03,A04,A01,C01}`, `Source/`
and `Paper1/` found no implementation of `restartBeyond` or `extendsBeyond`
in this checkout (only documentation references). The owner's conditional
implementation described in HANDOFF is not consumed. The output above matches
the velocity-bound premise in `research/A04/Spec.lean`'s `restartBeyond`;
it does not assert extension or discharge that field's separate force bounds
with the same `K`, `SolvesBelow`, or the uniform A02 restart theorem.

In particular, A02 restart does not magically close `HasAprioriBound`:
`‖u‖ ≤ R` is assumed here, and `Kbnd = 256 R² T` and hence `B_m` depend on
that very `R`. A bound chosen from data/force before the cylinder solution,
and the remaining constructor/path/restart supply obligations, still need
an independent argument. No radius bootstrap has been proved by this lane.

## Proof attempts and resolved diagnostics

* Section variables used only in proofs required an explicit `include` list.
  Original diagnostic: ``Unknown identifier `hν` `` (likewise `ha`, `hf`, `hpath`).
* Opening both D01 and A04 made `forceSobolevENormL1` ambiguous; qualified
  the intended A04 name. Diagnostic: `Ambiguous term forceSobolevENormL1`.
* Datum lowering is under `D01.Leray` and requires `LerayLowering`:
  ``Unknown identifier `isSobolevDatum_lower` `` resolved by explicit import
  and `Leray.isSobolevDatum_lower`.
* Rewriting an order-three datum equality required normalizing the natural
  cast: ``Tactic `rewrite` failed: Did not find an occurrence of the pattern
  sobolevENorm ↑3 ...``. `norm_num only [Nat.cast_ofNat] at he` resolves it.
* `ENNReal.ofReal_norm` is not the lemma name (`Unknown constant`); the
  current unqualified `ofReal_norm` works without a deprecation warning.

No unresolved Lean errors; no increased heartbeat limits. The conformance
file prints all three new declarations and instantiates the entire assembled
handoff on `A04.zeroSol 1 1`, zero cylinder/ordinary paths, `q = 4`, `R = 0`.
See `REPORT_179.md` for exact statements and final gates.
