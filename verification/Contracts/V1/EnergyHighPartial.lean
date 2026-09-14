import Contracts.V1.Data
import Contracts.V1.TameProduct

/-! Stable specification for the **proved part** of A04 unit G1, the all-order
energy inequality eq:Rhigh on `R³`.

Task `collaboration/tasks/A04.md`, graph node `A04`
(`formalization/blueprint/DEPENDENCY_GRAPH.md:205-209`: `A04 ← A02, A03`;
consumers `A04 → R43, R44`).  This is the **first** registered A04 contract.
Version 1 fixes the single field of `research/A04/Spec.lean`'s `EnergyHighAPI`
that is discharged in the tree, `energyIdentityHigh`
(`Spec.lean:424-434`, proved as
`formalization/NSFormalization/Section4/A04/EnergyIdentityHigh.lean:145`), dropping
the differential/integrated continuation displays that are not yet proved (see
"Out of scope" below).  The mathematics is the order-`m` energy identity
`lem:Rhigh`, `paper/sections/appendix-a-local-theory.tex:132-137`:

```
½ (d/dt)‖u‖²_{H^m} + ν‖∇u‖²_{H^m}
   ≤ C_m ‖u‖_{H²} ‖u‖_{H^m} ‖∇u‖_{H^m} + ‖f‖_{H^m} ‖u‖_{H^m}   (m ≥ 3, t ∈ (0,T))
```

on the compact intervals of smooth existence the manuscript works on
(`:139`, "justified by Fourier approximation on compact intervals of smooth
existence").  The statement frozen here is the **tree form**, verified equivalent
to two independent blind restatements from the paper alone in the Rule-2 lane
`research/A04/BLIND_RHIGH.md` §2–§4 (verdict: Rule 2 closed for eq:Rhigh; the two
blind statements are `rfl`-equal to each other and, modulo the one hypothesis
below, to the tree form).

## What is fixed (the one proved field, with its manuscript source)

* `energyIdentityHigh` (`research/A04/Spec.lean:424-434`;
  `appendix-a-local-theory.tex:132-137`, `:129` "For every integer `m ≥ 3`"):
  the order-`m` differential energy inequality, stated with the two data fields
  `Chigh : ℕ → ℝ` / `Chigh_pos` as the Skolemization of the blind writers'
  `∃ C, (∀ m, 0 < C m) ∧ …` (`BLIND_RHIGH.md` §5.1).  The derivative is asserted,
  not assumed: `∃ d, HasDerivAt (fun r => ‖u(r)‖²_{H^m}) d t ∧ …`, matching the
  manuscript's `d/dt` (`:132`) which `:139` justifies rather than hypothesizes.

## The hypothesis `HasSmoothSobolevPath`, and why the field is CONDITIONAL

`energyIdentityHigh` carries the hypothesis `HasSmoothSobolevPath T w.velocity`:
every velocity slice has, at every integer order, a datum path that is `C^∞` in
time on `[0,T)` (`appendix-a-local-theory.tex:72-77`, "repeated time
differentiation gives `C^j_t H^k_x` regularity for all `j,k`").  This is exactly
A01's clause `sobolev_smooth` (`research/A01/Spec.lean:180`, split unit m1, size
`L`, status **gap**).  It is **NOT** derivable from `Data.ClassicalSolutionR.sobolev`,
which supplies only a `ContinuousOn` datum path (`BLIND_RHIGH.md` §3.3 gives the
`ContinuousOn ≠ ContDiffOn ℝ ∞` failure).  So this field is a *conditional*
statement: the manuscript asserts the time regularity at `:72-77`, but in the
formalization it is still owed by A01.  This is the single most important
disclosure of the contract.

## Out of scope, and asserted nowhere below

Not registered here, because not proved in the tree on this branch (they live in
`research/A04/Spec.lean` only as the draft's displays):

* `regularizedNormDerivative` / eq:highcontinuation before the limit
  (`Spec.lean:437-465`, `appendix-a-local-theory.tex:139-145`, the `ζ`-regularized
  `(‖u‖_{H^m})'` bound) — a V2 field (unit G2);
* `highContinuationIntegral` / the integrated Grönwall form
  (`Spec.lean:494-510`) and the continuation criterion eq:criterion — V2 (unit G2);
* `Cgron` (`Spec.lean`, `= (Chigh m)²/(4ν)`) and any identification of `Chigh`
  with another constant.

Also asserted nowhere: eq:mild, the mild-solution semantics, the first-crossing /
bootstrap arguments of Theorem 4.1, and the `t = 0` endpoint (the field speaks
only on the open interior `Ioo 0 T`).

## Conventions and the `.toReal` disclosure

* Every object quantified over is the canonical one of
  `verification/Contracts/V1/Data.lean`: `initialClassR` is `X_R`, `MemForceR` is
  `F_R`, `ClassicalSolutionR ν a f T` the classical solution on `[0,T)`,
  `IsSobolevDatum`/`sobolevENorm` the datum norm; `RealVectorSobolev` is Paper3's
  three-vector carrier; `gradientSobolevENorm` is the **registered**
  `Contracts.V1.TameProduct` object (`TameProduct.lean:192`), used unchanged.
* `‖∇u‖_{H^m}` is `gradientSobolevNormAt`, the gradient **tensor** Sobolev norm
  `(∑_j ‖∂_j u‖²_{H^m})^{1/2}` — it is **not** `‖u‖_{H^{m+1}}`, and the order shift
  `‖∇v‖_{H^s} ≤ ‖v‖_{H^{s+1}}` is out of scope (`TameProduct.lean:51-53`).
* The four norms are `ENNReal.toReal`, so a `⊤` value would read as `0`.  On the
  class quantified over this never happens: `Continuity.lean:64,73`
  (`sobolevENorm_velocity_ne_top`, `sobolevENorm_force_ne_top`) cover the three
  `sobolevNormAt` slots, and `Section4/A04/GradientFiniteness.lean`
  (`gradientSobolevENorm_velocity_ne_top`, lane 133, credit lane-128 reviewer)
  covers the gradient slot — so eq:Rhigh's dissipation `ν‖∇u‖²_{H^m}` is a genuine
  norm, not a `⊤ ↦ 0` artefact.
* `0 < ν`, `a ∈ initialClassR` and `3 ≤ m` are stated as the manuscript does; the
  proof has slack (`0 ≤ ν`, `2 ≤ m`, and `a ∈ initialClassR` unused), recorded in
  `research/A04/ATTEMPTS_CONTRACT.md`, not weakened in V1.

`Contracts.V1.Data` supplies `SpatialField`, `SpaceTimeField`, `ClassicalSolutionR`,
`initialClassR`, `MemForceR`, `IsSobolevDatum`, `sobolevENorm`; `RealVectorSobolev`
is Paper3's; `Contracts.V1.TameProduct` supplies `gradientSobolevENorm`.  Only the
three spec-local `def`s `sobolevNormAt`, `gradientSobolevNormAt`,
`HasSmoothSobolevPath` (`research/A04/Spec.lean:183,190,247`;
`Section4/A04/{Forcing.lean:74,LaplacianDatum.lean:86,DerivNorm.lean:87}`), which
have no `Data.lean`/`TameProduct.lean` declaration, are restated verbatim below;
`Bindings.EnergyHighPartial` records by `rfl` that each is the implementation's. -/

noncomputable section

namespace BlowupDensity.Contracts.V1.EnergyHighPartial

open Set MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open NSFormalization.Paper3 (RealVectorSobolev)
open scoped ContDiff ENNReal RealInnerProductSpace

/-! ## 1. Spec-local time-slice quantities (`research/A04/Spec.lean:183,190,247`) -/

/-- `research/A04/Spec.lean:183` `sobolevNormAt` (`Section4/A04/Forcing.lean:74`):
`‖u(t)‖_{H^s}` as a **real** number, the `.toReal` of `Data.sobolevENorm` on the
time-`t` slice.  `.toReal` reads a `⊤` norm as `0`; on the classes quantified over
in `energyIdentityHigh` the underlying `ℝ≥0∞` value is finite
(`Section4/A04/Continuity.lean:64,73`). -/
def sobolevNormAt (s : ℝ) (u : SpaceTimeField) (t : ℝ) : ℝ :=
  (sobolevENorm s (fun x : Space => u (t, x))).toReal

/-- `research/A04/Spec.lean:190` `gradientSobolevNormAt`
(`Section4/A04/LaplacianDatum.lean:86`): `‖∇u(t)‖_{H^s}` as a **real** number, the
`.toReal` of the registered `Contracts.V1.TameProduct.gradientSobolevENorm` (the
gradient tensor norm `(∑_j ‖∂_j u‖²_{H^s})^{1/2}`) on the time-`t` slice.  On a
classical-solution velocity slice this `ℝ≥0∞` value is finite
(`Section4/A04/GradientFiniteness.lean`). -/
def gradientSobolevNormAt (s : ℝ) (u : SpaceTimeField) (t : ℝ) : ℝ :=
  (TameProduct.gradientSobolevENorm s (fun x : Space => u (t, x))).toReal

/-- `research/A04/Spec.lean:247` `HasSmoothSobolevPath`
(`Section4/A04/DerivNorm.lean:87`), restated token-for-token: "for every integer
order the field has an order-`m` datum at every time of `[0,T)` and that datum
path is `C^∞` in time there".  This is A01's `sobolev_smooth` clause
(`appendix-a-local-theory.tex:72-77`), the differentiability input the energy
inequality needs; it is **not** implied by `Data.ClassicalSolutionR.sobolev`
(`ContinuousOn` only).  `Ico 0 T` is `UniqueDiffOn`, so the derivative at `t = 0`
is one-sided and no negative-time extension is differentiated. -/
def HasSmoothSobolevPath (T : ℝ) (u : SpaceTimeField) : Prop :=
  ∀ m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
    (∀ t ∈ Ico (0 : ℝ) T,
        IsSobolevDatum (m : ℝ) (fun x : Space => u (t, x)) (G t)) ∧
      ContDiffOn ℝ ∞ G (Ico (0 : ℝ) T)

/-! ## 2. The contract -/

/-- The **proved** field of the all-order energy inequality eq:Rhigh
(`paper/sections/appendix-a-local-theory.tex:132-137`) on `R³`, in exactly the form
`research/A04/Spec.lean`'s draft `EnergyHighAPI` states it, with the
`ζ`-regularized continuation displays and the criterion removed; see the module
docstring.

No field is a hypothesis about an unspecified proposition, and no field is `True`,
`∃ x, True` or any similar placeholder. -/
structure EnergyHighPartialAPI where
  /-- `appendix-a-local-theory.tex:132`, the constant `C_m` of eq:Rhigh, a family
  depending on the order `m` alone (not on `ν, a, f, T, w`).  Kept **opaque**: the
  contract asserts only its positivity, not `Chigh = tame.Ctame` nor any other
  identification (`research/A04/COMPARISON.md:66`, `BLIND_RHIGH.md` §5.3).  The
  Skolemization of the blind writers' `∃ C` (`BLIND_RHIGH.md` §5.1). -/
  Chigh : ℕ → ℝ
  /-- `appendix-a-local-theory.tex:132`, "`≤ C_m …`": the constant is strictly
  positive at every order, so the bound is a genuine estimate. -/
  Chigh_pos : ∀ m : ℕ, 0 < Chigh m

  /-- **`energyIdentityHigh`** (`research/A04/Spec.lean:424-434`;
  `appendix-a-local-theory.tex:132-137`, `:129` "For every integer `m ≥ 3`"): the
  order-`m` differential energy inequality on an interior time `t ∈ (0,T)` of a
  classical solution whose velocity has a `C^∞`-in-time Sobolev datum path.  The
  time derivative of `‖u(·)‖²_{H^m}` is **asserted** (`∃ d, HasDerivAt … ∧ …`),
  matching the manuscript's `d/dt`, which `:139` justifies by Fourier
  approximation on the compact intervals of smooth existence.

  The pressure term is absent: it vanishes by solenoidality
  (`ClassicalSolutionR.divergence`, `:137-138`).

  **Conditional on `HasSmoothSobolevPath`**, which is A01's unproved
  `sobolev_smooth` (`:72-77`; see the module docstring).  `a ∈ initialClassR` is
  carried for fidelity and unused; `0 < ν`, `3 ≤ m` are as the manuscript states
  them. -/
  energyIdentityHigh : ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ),
    0 < ν → a ∈ initialClassR → MemForceR f →
      ∀ w : ClassicalSolutionR ν a f T, HasSmoothSobolevPath T w.velocity →
        ∀ m : ℕ, 3 ≤ m → ∀ t ∈ Ioo (0 : ℝ) T,
          ∃ d : ℝ,
            HasDerivAt (fun r : ℝ => sobolevNormAt (m : ℝ) w.velocity r ^ 2) d t ∧
              (1 / 2) * d + ν * gradientSobolevNormAt (m : ℝ) w.velocity t ^ 2 ≤
                Chigh m * sobolevNormAt 2 w.velocity t *
                    sobolevNormAt (m : ℝ) w.velocity t *
                    gradientSobolevNormAt (m : ℝ) w.velocity t +
                  sobolevNormAt (m : ℝ) f t * sobolevNormAt (m : ℝ) w.velocity t

end BlowupDensity.Contracts.V1.EnergyHighPartial
