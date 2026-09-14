# A01 A3 — attempts, decisions, negative findings (lane 122)

Module: `formalization/NSFormalization/Section4/A01/Propagation.lean`.
Goal: the abstract, route-independent arithmetic core of A3 (the order-independent
horizon), reusing `A04.gronwall_integral_mul` verbatim.

## What was proved and how the interface was chosen

`gronwall_bddAbove_Ico` + `higherOrder_bddAbove` (+ the `k=(y m₀)²` corollary).
Built first try after the design below; `#print axioms` = standard three.
Commands:
* `cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A04.Gronwall`
  → `Build completed successfully (2680 jobs)`.
* `… lake build NSFormalization.Section4.A01.Propagation` → success (2681 jobs);
  first pass had one `linter.unusedVariables` warning (below), then clean.
* `lake env lean ../formalization/.../Propagation.lean` → silent, exit 0.
* `lake env lean ../research/A01/axioms_a3.lean` → standard three for all three
  decls, exit 0.
* `make check` → contract-policy tests + work-queue check pass.

## Decision 1 — why the `hstep` interface is `y t ≤ y 0 + ∫(Cgron·k·y + b)`

This is exactly the shape `A04.gronwall_integral_mul` (`Gronwall.lean:202`,
`#check`ed) consumes, **and** exactly the output of `A04.sqrt_le_primitive_linear`
(`Regularized.lean:134`, `#check`ed) after the Young step: `sqrt_le_primitive_linear`
concludes `√E t ≤ √E 0 + ∫(K·√E + b)`, and with `y := √E`, `K := Cgron·k` that is
the `hstep` here.  So the lane sits precisely at the seam between A04's ζ-device
and the horizon assembly — no re-statement of the differential inequality was
needed, and the two A04 lemmas plug in without an adapter.  Stating it over
abstract `y,k,b : ℝ → ℝ` (not `ClassicalSolutionR`) is what lets it reuse
`gronwall_integral_mul` verbatim and be route-independent.

## Decision 2 — uniform integral caps `Kbnd`,`Bbnd`, NOT `∫ 0..T₀`

First design used the improper `∫ s in 0..T₀, k` as the cap and tried to prove
`∫ 0..t k ≤ ∫ 0..T₀ k` from the nonneg tail.  **Abandoned**: that needs `k ≥ 0`
on the *closed* `Icc t T₀` (to apply `intervalIntegral.integral_nonneg` on the
tail `∫ t..T₀`), i.e. nonnegativity/continuity of `k` **at `T₀` itself**.  On the
A3 half-open horizon the low-order norm need not be controlled at `T₀` (that is
where existence stops), so assuming anything at `T₀` is wrong for the application.
Taking `Kbnd`,`Bbnd` as *hypotheses* (uniform caps valid on `Ico 0 T₀`) is both
weaker and exactly what the mild-space membership supplies (`Kbnd = ‖u‖²_{L²_tH²}`,
`Bbnd = ‖f‖_{L¹_tH^m}`), so it is the faithful abstraction.  It also removes the
`IntervalIntegrable k 0 T₀` hypotheses entirely.

## Decision 3 — the `0 ≤ y 0` hypothesis is load-bearing (negative finding)

The final monotone step needs to replace `(y 0 + ∫₀ᵗb)·exp(Cgron·∫₀ᵗk)` by
`(y 0 + Bbnd)·exp(Cgron·Kbnd)`.  Monotonicity in the `exp` factor is **false**
when the base is negative.  The fix is `0 ≤ y 0` (natural: `y_m 0 = ‖a‖_{H^m} ≥ 0`),
which with `b ≥ 0` makes the base `y 0 + ∫₀ᵗ b ≥ 0`; then `A·e₁ ≤ B·e₁ ≤ B·e₂` with
`B ≥ 0` (`mul_le_mul_of_nonneg_right` on the base, then `mul_le_mul_of_nonneg_left`
on the exponent).

**Statement-level refutation (lane-122 review F4, folded in).**  Per
`logs/LESSONS.md` (2026-09-14) an *arithmetic proof-step* counterexample
(`A=B=-1, e₁=1, e₂=2`) does **not** prove a hypothesis necessary.  The proper
witness — the whole lemma minus `hy0` is false — is
`research/A01/probes/hy0_necessary_probe.lean` `hy0_is_necessary : ¬ NoNonnegInitial`:
`T₀=2, Cgron=1, k=1, b=0, Kbnd=2, Bbnd=0`, `y = fun s => -Real.exp s` (the exact
solution of `y'=y`, `y 0 = -1`), for which `hstep` holds with **equality** and every
other hypothesis holds, yet at `t=0` the conclusion is `-1 ≤ -exp 2`, false
(`exp 2 ≥ 3`).  Compiles, standard 3 axioms.  So `hy0` is load-bearing at the
statement level, not just at a proof step.  (`hstep` was discharged by FTC via
`intervalIntegral.integral_eq_sub_of_hasDerivAt` on `-exp`, not `integral_exp` —
`Mathlib.Analysis.SpecialFunctions.Integrals` is **not** in the cached olean set on
this pin, so importing it fails with "object file … does not exist".)

## Decision 4 — `BddAbove (image)` for the "same T₀ for every order" packaging

`higherOrder_bddAbove` concludes `∀ m ≥ m₀, BddAbove ((fun t => y m t) '' Ico 0 T₀)`.
`BddAbove S = (upperBounds S).Nonempty`; discharged by `refine ⟨M, ?_⟩;
rintro x ⟨t, ht, rfl⟩; exact gronwall_bddAbove_Ico … t ht` with
`M := (y m 0 + B m)·exp(C m · Kbnd)`.  The "same T₀" is structural: `T₀` and `k`,
`Kbnd` are single shared variables, so the `∀ m` conclusion carries one interval.
Considered stating it as `∀ m, ∃ M, ∀ t ∈ Ico 0 T₀, y m t ≤ M` (avoids the
`upperBounds` API) — `BddAbove` chosen because it is the canonical Mathlib form a
later `IsCompact`/`sSup` argument (T1, B1) will want.

## Decision 5 — do NOT weaken `k`/`b` continuity to interval-integrability (F13)

`gronwall_bddAbove_Ico` inherits `ContinuousOn k/b` from
`A04.gronwall_integral_mul` → `gronwall_integral`, whose integrating-factor proof
differentiates `x ↦ ∫₀ˣ c` pointwise (FTC) and needs `s ↦ exp(-∫c)·b s` continuous
for `integral_mono_on`.  Weakening to `IntervalIntegrable` would force reproving
A04's `gronwall_integral` via absolute continuity — and buys nothing: the supply
side is *already* continuity.  `A04.intervalIntegrable_highContinuationIntegrand`
(`Continuity.lean:132`) is itself proved `apply ContinuousOn.intervalIntegrable`
from `continuousOn_sobolevNormAt_velocity`/`_force`.  No strengthening.

## The linter warning (fixed)

First build: `Propagation.lean:150 linter.unusedVariables: Variable name 't' is
not explicitly referenced` in the `k=(y m₀)²` corollary's `hknn := fun t _ =>
sq_nonneg _`.  The `t` binder is unused (the goal `0 ≤ (y m₀ t)^2` fixes the
`sq_nonneg` argument by unification).  Fixed by renaming to `fun _ _ => sq_nonneg _`.
No `set_option` / linter disable used (forbidden).

## What this lane did NOT do (scope), and why

* **A2 (eq:Rhigh)** is A04's `energyIdentityHigh`; A01 consumes it.  Its last
  missing input `hpr` (pressure drop) is being proved by lane 121 concurrently —
  not touched here.
* **A3-M1 (Young)** and **A3-M2 (compose ζ-device)** are S/M but gated by A2's
  `hpr` (they need the concrete `HasDerivAt E` / `½E' ≤ …`), so proving them now
  would only produce a lemma with an unusable hypothesis; deferred, stated in
  `A3_SPLIT.md`.
* **A3-M1 (Young)** and **A3-M2 (compose ζ-device)** — see above; gated on A04 `hpr`.
* **A2b-a (continuation)** is **not** an L and **not** blocked on C1c — corrected
  after the review (F5).  The OpenAI/local layer *does* have forced-path
  continuation: `EulerBoundedMildContinuation.exists_global_mild_of_bound`
  (`vendor/.../Euler/BoundedMildContinuation.lean:39`) composes with
  `ForcedCylinderLocal.coefficients` in one line —
  `research/A01/probes/a2b_continuation_probe.lean` (compiles, standard 3 axioms).
  HeliCorgi/`FormalPatched` is **not** needed; the revision-1 grep claim to the
  contrary was a false negative (omission of the one relevant file).  A3-L2
  collapses (`horizon := S`).
* **A3-L1·k (order-2 norm cap)** is blocked on a **new one-directional norm
  comparison** (not a C1b norm identity — 119 disclaims that) plus 119's
  **C1b-m-D** (missing D01 finite-order datum constructor).  `hy0 : 0 ≤ y_m 0`
  needs **no** bridge (`sobolevNormAt` is `.toReal`, `ENNReal.toReal_nonneg`).
* `research/A01/C1B_SPLIT.md` (lane 119) was genuinely absent at merge-base
  `6801945` (review-verified); 119 has since merged (`0415366`, PR #121), so its
  rows are cited via the lane-122 review, not from this worktree.
