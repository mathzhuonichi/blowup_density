# C1b — attempts, probes, decisions (lane 119)

Non-generated notebook for unit C1b (`research/A01/C1B_SPLIT.md`).  Records the
probes run, what typechecked on the first try, the one dead end, and the scoping
decisions.

## Decision: first S unit = C1b-0 (order-0 carrier bridge)

The briefing offered two candidate first units: (i) the order-0 identification
`EulerMeanSolenoidal.L2 ↔ MemLp 2` with the D01 order-0 datum, or (ii) the
`ordinaryLift`-adjoint norm identity at one order.  Chose **(i)** because D01
already ships the whole order-0 seed from a *bare* `MemLp` field
(`Section4/D01/OrderZeroDatum.lean`, `orderZeroDatum` / `isSobolevDatum_orderZeroDatum`
/ `exists_isSobolevDatum_zero_of_memLp`, discovered by
`grep -rn IsSobolevDatum formalization/NSFormalization/Section4/`), so (i) is a
short, certain bridge that unblocks the order-0 halves of rows c5/c6/c8; (ii)
would re-derive an isometry that `ordinaryLift : L2 →ₗᵢ LiftL2 1` already *is*.

## What typechecked, and the one fix

Probes (all under `research/A01/probes/`, run with
`cd verification && lake env lean ../research/A01/probes/<f>.lean`):

* `c1b_probe.lean` — order-0 bridge: `isSobolevDatum_orderZeroDatum (Lp.memLp U)
  : IsSobolevDatum 0 (⇑U) (orderZeroDatum (Lp.memLp U))`.  **Typechecked
  first try.**  Confirms `EulerMeanSolenoidal.L2 = Lp Space 2 volume` with the
  *same* `Space = EuclideanSpace ℝ (Fin 3)` as D01
  (`NavierStokes/ProblemStatement.lean:30`, `Euler/EulerProof.lean:5202`), so no
  `show`/coercion is needed to feed `Lp.memLp U` to `orderZeroDatum` (whose field
  is `{z : Space → Space}`).
* `c1b_probe2.lean` — `IsSobolevDatum.congr_field` (ae-transport, all orders) and
  the c5-0 transport `U = a.toLp → IsSobolevDatum 0 a.field …`.  **Both
  typechecked** (proof: `rw [h i ψ]; refine integral_congr_ae ?_; filter_upwards
  … with x hx; rw [hx]`).

**One failure, fixed.**  In the module, writing the c5-0 lemma with dot notation
`(isSobolevDatum_zero_ordinaryL2 U).congr_field …` failed to build:

```
error: Invalid field `congr_field`: The environment does not contain
`Function.congr_field`, so it is not possible to project the field `congr_field`
from an expression … of type ∀ (i : Fin 3) (ψ : …), …
```

Cause (**corrected by reviewer finding 12** — my first-written cause "the body is
a `∀`" was wrong).  The real cause is a **namespace mismatch**: `h.congr_field`
resolves `Foo.congr_field` where `Foo` is the head constant of `h`'s type.  Here
`h`'s type has head constant `NSFormalization.Section4.D01.IsSobolevDatum`, so
Lean looks for `…D01.IsSobolevDatum.congr_field` — but the helper was declared in
`NSFormalization.Section4.A01`.  That lookup fails, and *only then* does Lean
unfold the `def` to a pi type and print the `Function.congr_field` **fallback**
message.  The reviewer confirmed (`/tmp/rev119/dotfix.lean`) that the *same lemma*
declared inside `namespace NSFormalization.Section4.D01` (as
`…D01.IsSobolevDatum.congr_field'`) **does** support `h.congr_field'`, silently.
Fix used: call the lemma by full name —
`IsSobolevDatum.congr_field (isSobolevDatum_zero_ordinaryL2 U) …`.  Rebuilt clean
(`Build completed successfully (9873 jobs)`), `lake env lean` silent, axioms
standard three.

(Correct lesson-shaped one-liner, per reviewer: *a `Foo.bar` helper only supports
`h.bar` when it is declared in the namespace of `Foo`'s head constant; the
`Function.baz` message is the fallback, not the cause.*  Do **not** promote the
old "body is a `∀`" sentence to `logs/LESSONS.md`.  Cosmetic follow-up the
reviewer suggests for the next touch: move the helper to the `D01` namespace or
rename to `isSobolevDatum_congr_field`, since the current name advertises dot
notation it cannot deliver.)

## Convention question — settled by derivation, not left open

`COMPARISON.md` §4 lists "three Fourier conventions meet in C1b/C1c, and the
`(2π)` bookkeeping is where D01's first junk-value bug was" as the second risk.
For **C1b** this was settled without a probe by unfolding the definitions
(`Source/FourierConvention.lean:23` + Mathlib's `𝓕(∂ⱼf) = 2πi ζⱼ 𝓕f`): the
`(2π)^(-3/2)` prefactor and the `(2π)⁻¹` argument-rescaling of `angularFourier`
make `∂ⱼ ↔ i ξⱼ` with the `2π` **cancelling exactly**, which is corroborated in
tree by D01's `isSobolevDatum_partialDeriv` (`DerivativeDatum.lean:245`) carrying
multiplier `iξⱼ(1+‖ξ‖²)^{-1/2}` and **no** `2π`.  At order 0 the constant is
exactly `1` (`Paper3.sobolevRealization_zero`).  So C1b carries no loose
`(2π)^k`; the residual difficulty (rows C1b-m-E/C1b-m-D) is the homogeneous
derivative-tensor↔inhomogeneous Bessel-weight identification, which is analysis.
Full statement in `C1B_SPLIT.md` §0.

## Not attempted (correctly out of scope for an S unit), and why

* **C1b-m** (order `m ≥ 1`, intermediate time) — **L**, and **corrected by
  reviewer finding 9**.  My first draft called this "the shared dependency with
  B1/T1" (needing `U t` to be a `SmoothL2Field`).  That is wrong: it is the
  dependency of the *route I picked*, not of the unit.  A finite-order route needs
  **no** joint smoothness.  `u t : SobolevSpace 1 (q+1)` is a closed-graph array
  every edge of which is a genuine strong `L²` translation derivative
  (`word_hasDerivAt`, `CylinderSobolevSpace.lean:70`); each word is the `value` of
  a lower-order sub-array (`word_has_jet`/`ofJet`, `:91,78`) that inherits clause
  7's angle invariance, so `exists_ordinary_value` (`OrdinaryCylinderDescent.lean:29`,
  needs only `3 ≤ order`) descends each word to an ordinary `L²` field — giving
  `U t` strong `L²` derivatives up to order `q+1` at fixed `t>0`, with **no**
  `SmoothOrbit`, `SmoothL2Field`, B1 or T1.  The **real** blocker is a *missing
  D01 finite-order datum constructor* (`MemLp 2` + `L²` derivs up to order `m` ⟹
  order-`m` datum; the analogue of `orderZeroDatum` between it and
  `smoothAngularDatum`).  Split into C1b-m-E (Euler, M) and C1b-m-D (D01, M–L) in
  the table.  Deliberately not started under an S-unit budget.  (Separately, the
  `∀ m` of `ClassicalSolutionR.sobolev` on one `T` is gated by **A3**, not B1/T1;
  B1 is needed only for the `velocity t =ᵐ ⇑(U t)` hand-off, which
  `IsSobolevDatum.congr_field` already absorbs.)
* **C1b-c8-m** — continuity of the order-`m ≥ 1` datum path needs the vector
  order-`m` Plancherel isometry, which `OrderZeroDatum.lean`'s own docstring
  records as **not in tree** ("the norm identity is NOT proved here … a separate
  ~25–50-line item that belongs in `Paper3`").  Left as a gap row.
* **C1b-c8-0** — order-0 path continuity *is* provable (each factor of
  `orderZeroDatum` is a CLM/CLE), but requires re-expressing `componentLp` as a
  continuous-linear map of the `L²` argument (`Lp.compLp` of
  `ofRealCLM.comp (proj i)`); booked as ready→M, not squeezed into this lane.
