import Contracts.V1.EnergyHighPartial

/-! Version 2 of the **proved part of A04's continuation interface**: the
version-one record `EnergyHighPartialAPI` (`Contracts/V1/EnergyHighPartial.lean`),
extended by the constant `Cgron` and the two `ζ`-continuation fields
`regularizedNormDerivative` (unit **G2**, lane 135) and `highContinuationIntegral`
(unit **G2b**, lane 138) that were added to the tree after version one was frozen.

Task `collaboration/tasks/A04.md`, graph node `A04`
(`formalization/blueprint/DEPENDENCY_GRAPH.md:205-209`: `A04 ← A02, A03`; consumers
`A04 → R43, R44`).  `research/A04/Spec.lean` bundles the whole obligation as
`EnergyHighAPI`; version one registered the single field discharged in the tree at
the time, `energyIdentityHigh`, and listed `regularizedNormDerivative`,
`highContinuationIntegral` and the constant `Cgron` in its "Out of scope" section,
"not proved in the tree on this branch".  That is no longer true: lane 135
(`Section4/A04/HighContinuation.lean`) proved `regularizedNormDerivative` and defined
`Cgron`/`Cgron_pos`, and lane 138 (`Section4/A04/HighContinuationIntegral.lean`)
proved `highContinuationIntegral`; version two records them.

## Why a new version

`Contracts.V1.EnergyHighPartial`'s "Out of scope" list names
`regularizedNormDerivative`, `highContinuationIntegral`, `Cgron` and the criterion
`eq:criterion` among the excluded objects "because not proved in the tree on this
branch".  Two of the three are now proved (lanes 135, 138); `Contracts/V1/*` is
frozen by CI, so a version two is the only way to register them without editing the
frozen file.

## What changed, exactly

`EnergyHighPartialV2API` extends `Contracts.V1.EnergyHighPartial.EnergyHighPartialAPI`
unchanged and adds **four** fields:

* `Cgron : ℕ → ℝ → ℝ` and `Cgron_pos` (`research/A04/Spec.lean:354-356`;
  `appendix-a-local-theory.tex:142-145` the constant `C_{m,ν}`).  Kept **opaque**,
  exactly as version one keeps `Chigh` opaque: the contract asserts only
  `0 < Cgron m ν` at `0 < ν`, **not** `Cgron = (Chigh m)²/(4ν)` — the manuscript
  displays no formula.  The value the derivation gives, `(Chigh m)²/(4ν)`, appears
  only in the binding as the `rfl` bonus `energyHighPartialV2_Cgron_eq`.
* `regularizedNormDerivative` (`research/A04/Spec.lean:459-470`;
  `appendix-a-local-theory.tex:139-145`) — eq:highcontinuation **before** the `ζ↓0`
  limit, the fixed-`ζ` derivative bound on the regularized norm
  `(‖u‖²_{H^m}+ζ²)^{1/2}`.  Discharged by
  `NSFormalization.Section4.A04.regularizedNormDerivative` (lane 135, unit G2).
* `highContinuationIntegral` (`research/A04/Spec.lean:471-494`;
  `appendix-a-local-theory.tex:141-145`) — eq:highcontinuation **after** `ζ↓0`, in
  its integrated form on `[t₀,t] ⊆ [0,T)`.  Discharged by
  `NSFormalization.Section4.A04.highContinuationIntegral` (lane 138, unit G2b).

Each new field is stated **token-for-token** as its `research/A04/Spec.lean` draft
field, in the vocabulary of `Contracts.V1.Data` and the three spec-local notions
version one restated (`sobolevNormAt`, `gradientSobolevNormAt`,
`HasSmoothSobolevPath`), plus the single new restatement `MemL1Hm` below.  No
version-one field is removed, weakened, renamed or restated; `extends` makes that
structural.  `Bindings.energyHighPartial_of_v2` records the version-one projection
is the frozen version-one witness by `rfl`, and `Tests.checkedEnergyHighPartial`
keeps running against the untouched `Bindings.energyHighPartial`.

## The one object `Data.lean` does not define, restated verbatim

`Contracts.V1.Data` supplies `SpatialField`, `SpaceTimeField`, `ClassicalSolutionR`,
`initialClassR`, `MemForceR`, `forceSobolevENormL1`; version one supplies
`sobolevNormAt`, `gradientSobolevNormAt`, `HasSmoothSobolevPath` (all inherited by
importing `Contracts.V1.EnergyHighPartial`, and drift-guarded there by three `rfl`
bridges).  Mathlib supplies `IntervalIntegrable`, the interval-integral notation
`∫ s in t₀..t, ·`, `MeasureTheory.volume`, `Real.sqrt`, `HasDerivAt`, `Set.Ioo`.

The one notion neither `Data.lean` nor version one defines is **`MemL1Hm`**
(`research/A04/Spec.lean:268`, `Section4/A04/Forcing.lean:110`): finiteness of the
`L¹_t H^m` forcing norm at every integer order.  It is restated **verbatim** below,
and `Bindings.energyHighPartialV2_memL1Hm_eq` records by `rfl` that it is the
implementation's `NSFormalization.Section4.A04.MemL1Hm` — the **fourth** `rfl` bridge
of this contract family.

## Scope disclosures (beyond version one's)

1. **`Cgron` is opaque.**  The contract asserts only positivity at `0 < ν`; it does
   **not** assert `Cgron = (Chigh m)²/(4ν)` nor any other identification.  The
   manuscript displays no formula for `C_{m,ν}`; the value lives only in the binding
   as a `rfl` bonus.
2. **`ν = 0` is junk, so `0 < ν` cannot be weakened.**  At `ν = 0` Lean's division
   makes `Cgron m 0 = 0` (`research/A04/REVIEW_G2B.md` §5.3.2, 135-review
   `p7_dup.lean`), so a `0 ≤ ν` field would assert the strictly **stronger and false**
   bound with a vanishing coefficient.  Both `0 < ν` weakenings are refused
   (`REVIEW_G2B.md` §2(d), `p_nu0.lean`).
3. **`highContinuationIntegral` is the `ζ↓0` (integrated) statement, not a
   differential one.**  After the limit the left side is `‖u‖_{H^m}`, which need not
   be differentiable where `u` vanishes in `H^m`; the manuscript's `(‖u‖_{H^m})'` is
   shorthand for the inequality that survives the limit, and that inequality is this
   integrated one — the only form Grönwall consumes.
4. **The `IntervalIntegrable` conjunct is asserted, not assumed.**  Mathlib's
   `∫ s in t₀..t, ·` is `0` on a non-integrable integrand, so the inequality would be
   false rather than vacuous unless integrability is settled; it is settled here by
   **asserting** it as the first conjunct, proved from continuity on a compact interval
   (unit **N1**, `Section4/A04/Continuity.lean:132`).  The integral is therefore a
   genuine Lebesgue integral, not a `⊤ ↦ 0` artefact.
5. **The `.toReal` `⊤ ↦ 0` disclosure covers only the velocity and force slots
   here.**  `sobolevNormAt` is `ENNReal.toReal`; the two slots appearing in these
   fields (velocity `sobolevNormAt _ w.velocity`, force `sobolevNormAt _ f`) are
   finite on the class quantified over by `Section4/A04/Continuity.lean:64,73`
   (`sobolevENorm_velocity_ne_top`, `sobolevENorm_force_ne_top`).  Unlike version
   one's `energyIdentityHigh`, **no gradient norm appears** in these fields, so
   version one's `gradientSobolevENorm_velocity_ne_top` sentence is deliberately not
   repeated.
6. **Endpoints `0 ≤ t₀ ≤ t < T`, with `t₀ = 0` included.**  `highContinuationIntegral`
   runs on the closed-left interval (`t₀ = 0` is in range); the endpoint is covered by
   **continuity** on `Icc t₀ t ⊆ Ico 0 T`, not by `HasSmoothSobolevPath`, which is
   used only at interior times (`Ioo t₀ t ⊆ Ioo 0 T`).  `0 ≤ t₀` is load-bearing (a
   negative time has no datum and the norm reads junk `0`); `t < T` is strict (the
   solution need not exist at `T`).  `regularizedNormDerivative` speaks at interior
   times `t ∈ Ioo 0 T` only.
7. **Still conditional on `HasSmoothSobolevPath`.**  Like version one's
   `energyIdentityHigh`, both new differential-side fields carry
   `HasSmoothSobolevPath T w.velocity`, which is A01's unproved `sobolev_smooth`
   clause (unit m1, `research/A01/Spec.lean:180`, size `L`, status **gap**;
   `appendix-a-local-theory.tex:72-77`).  This is the single most important
   disclosure and version two does not weaken it.
8. **`MemL1Hm f` is redundant, kept for fidelity.**  `highContinuationIntegral`
   carries `MemL1Hm f`, but the proof does not consume it and it is **derivable** from
   `MemForceR f` by `NSFormalization.Section4.A04.memL1Hm_of_memForceR` (unit **F1a**,
   `Section4/A04/Forcing.lean:140`).  It is stated so the contract displays the
   manuscript's own `L¹_t H^m` hypothesis (`appendix-a-local-theory.tex:144-145`)
   rather than the ambient class (`REVIEW_G2B.md` finding 5).
9. **`a ∈ initialClassR` is slack** (inherited disclosure).  The proof routes it
   through `energyIdentityHigh`, whose V1 scope already records it as unused; version
   two adds no new redundancy.
10. **Out of scope, asserted nowhere below.**  The continuation criterion
    `eq:criterion` itself; the Grönwall consequence
    (`research/A04/Spec.lean` `higherOrderBound`, `appendix-a-local-theory.tex:146-147`);
    the uniform restart; `eq:mild`, the mild-solution semantics, and the
    first-crossing / bootstrap arguments of Theorem 4.1.

**Parallel, not sequential.**  `regularizedNormDerivative` and
`highContinuationIntegral` are two **parallel** explicit manuscript statements
(`Spec.lean` lists them as sibling fields); `highContinuationIntegral` does **not**
route through `regularizedNormDerivative` — it consumes `deriv_normSq_absorbed`
(unit G1 + Young) and `sqrt_le_primitive_linear` (unit Z1's `δ↓0`) directly.  So
`regularizedNormDerivative` currently has **zero** proof consumers in the tree
(`REVIEW_G2B.md` findings 2, 4); it is registered because it is a manuscript-explicit
step (Rule 2: cover what the paper states, not only what a downstream unit uses), and
its registration cost is zero (proved, standard three axioms).  A future version
three would add `eq:criterion` and the Grönwall consequence.

No new field is a hypothesis about an unspecified proposition, and none is `True`,
`∃ x, True` or any similar placeholder. -/

noncomputable section

namespace BlowupDensity.Contracts.V2.EnergyHighPartial

open Set MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.EnergyHighPartial (sobolevNormAt gradientSobolevNormAt
  HasSmoothSobolevPath)
open scoped ENNReal

/-! ## 1. The one object neither `Data.lean` nor version one defines -/

/-- `research/A04/Spec.lean:268` `MemL1Hm` (`Section4/A04/Forcing.lean:110`), restated
token-for-token: the `L¹_t H^m` forcing norm is finite at every integer order,
`‖f‖_{L¹_tH^m_x} < ∞`.  `forceSobolevENormL1` is `Contracts.V1.Data`'s
(`Data.lean:231`).  This is the manuscript's forcing hypothesis
(`appendix-a-local-theory.tex:144-145`) the continuation proof integrates; it is
derivable from `MemForceR` (unit F1a), and kept as a separate hypothesis for
fidelity.  `Bindings.energyHighPartialV2_memL1Hm_eq` records `= A04.MemL1Hm` by
`rfl`. -/
def MemL1Hm (f : SpaceTimeField) : Prop :=
  ∀ m : ℕ, forceSobolevENormL1 (m : ℝ) f ≠ ⊤

/-! ## 2. The contract -/

/-- **The proved part of A04's continuation interface, version 2.**  Version one's
`EnergyHighPartialAPI` (the constant `Chigh`/`Chigh_pos` and the all-order energy
inequality eq:Rhigh, `paper/sections/appendix-a-local-theory.tex:132-137`), together
with the continuation constant `Cgron` and the two `ζ`-continuation fields of lanes
135 and 138 (`Section4/A04/{HighContinuation,HighContinuationIntegral}.lean`).

Every field of `Contracts.V1.EnergyHighPartial.EnergyHighPartialAPI` is inherited
verbatim through `toEnergyHighPartialAPI`; see `Contracts/V1/EnergyHighPartial.lean`
for their docstrings and manuscript citations.

`EnergyHighPartialV2API` carries data fields (`Chigh`, `Cgron`), so it is a `Type`
and the binding is a `def`, as in version one.

No new field is a hypothesis about an unspecified proposition, and none is `True`,
`∃ x, True` or any similar placeholder. -/
structure EnergyHighPartialV2API extends
    BlowupDensity.Contracts.V1.EnergyHighPartial.EnergyHighPartialAPI where
  /-- `appendix-a-local-theory.tex:142-145`, the continuation constant `C_{m,ν}` of
  eq:highcontinuation.  Its two arguments are the manuscript's two subscripts: the
  order (inherited from `Chigh`) and the viscosity (entering when Young's inequality
  absorbs `C_m‖u‖_{H²}‖u‖_{H^m}‖∇u‖_{H^m}` into `ν‖∇u‖²_{H^m}` at `:139-140`).

  Kept **opaque**, exactly as version one keeps `Chigh` opaque: the contract asserts
  only positivity, **not** `Cgron = (Chigh m)²/(4ν)` (the manuscript displays no
  formula) nor any other identification.  The derived value appears only as the
  binding-level `rfl` bonus `energyHighPartialV2_Cgron_eq`.  `research/A04/Spec.lean:354`. -/
  Cgron : ℕ → ℝ → ℝ
  /-- `research/A04/Spec.lean:356`; positivity at every positive viscosity, which is
  what makes eq:highcontinuation a bound and not a vanishing statement.  At `ν = 0`
  the implementation's `Cgron m 0 = 0` (division junk), so `0 < ν` here cannot be
  weakened to `0 ≤ ν`. -/
  Cgron_pos : ∀ (m : ℕ) (ν : ℝ), 0 < ν → 0 < Cgron m ν

  /-- **`regularizedNormDerivative`** — eq:highcontinuation **before** the limit
  (`research/A04/Spec.lean:459-470`; `appendix-a-local-theory.tex:139-145`): at each
  fixed `ζ > 0`, the regularized norm `r ↦ (‖u(r)‖²_{H^m}+ζ²)^{1/2}` is differentiable
  at every interior time `t ∈ (0,T)` of a smooth-Sobolev-path classical solution, with

  `(d/dt)(‖u‖²_{H^m}+ζ²)^{1/2}
     ≤ C_{m,ν}‖u‖²_{H²}(‖u‖²_{H^m}+ζ²)^{1/2} + ‖f‖_{H^m}`.

  This is the fixed-`ζ` form, weaker than eq:highcontinuation and becoming it in the
  limit — the honest intermediate the manuscript's sentence describes.  Discharged by
  `NSFormalization.Section4.A04.regularizedNormDerivative` (lane 135, unit G2).

  **Conditional on `HasSmoothSobolevPath`** (A01's unproved `sobolev_smooth`).
  Currently has zero proof consumers in the tree (`highContinuationIntegral` bypasses
  it); registered as a manuscript-explicit step (see the module docstring). -/
  regularizedNormDerivative :
    ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ),
      0 < ν → a ∈ initialClassR → MemForceR f →
        ∀ w : ClassicalSolutionR ν a f T, HasSmoothSobolevPath T w.velocity →
          ∀ m : ℕ, 3 ≤ m → ∀ t ∈ Ioo (0 : ℝ) T, ∀ ζ : ℝ, 0 < ζ →
            ∃ d : ℝ,
              HasDerivAt
                  (fun r : ℝ =>
                    Real.sqrt (sobolevNormAt (m : ℝ) w.velocity r ^ 2 + ζ ^ 2)) d t ∧
                d ≤ Cgron m ν * sobolevNormAt 2 w.velocity t ^ 2 *
                      Real.sqrt (sobolevNormAt (m : ℝ) w.velocity t ^ 2 + ζ ^ 2) +
                    sobolevNormAt (m : ℝ) f t

  /-- **`highContinuationIntegral`** — eq:highcontinuation **after** `ζ↓0`
  (`research/A04/Spec.lean:471-494`; `appendix-a-local-theory.tex:141-145`), in its
  integrated form on `[t₀,t] ⊆ [0,T)`:

  `‖u(t)‖_{H^m} ≤ ‖u(t₀)‖_{H^m}
     + ∫_{t₀}^{t}(C_{m,ν}‖u(s)‖²_{H²}‖u(s)‖_{H^m} + ‖f(s)‖_{H^m}) ds`.

  The first conjunct **asserts** integrability of the integrand (proved from
  continuity on the compact interval, unit N1), so the integral is a genuine Lebesgue
  integral, not a `⊤ ↦ 0` artefact.  Endpoints `0 ≤ t₀ ≤ t < T` with `t₀ = 0`
  included, the left endpoint covered by continuity rather than by
  `HasSmoothSobolevPath`.  Carries the `L¹_t H^m` forcing hypothesis `MemL1Hm f`
  (redundant, derivable from `MemForceR`, unit F1a; kept for fidelity).  Discharged by
  `NSFormalization.Section4.A04.highContinuationIntegral` (lane 138, unit G2b).

  **Conditional on `HasSmoothSobolevPath`** (A01's unproved `sobolev_smooth`). -/
  highContinuationIntegral :
    ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ),
      0 < ν → a ∈ initialClassR → MemForceR f → MemL1Hm f →
        ∀ w : ClassicalSolutionR ν a f T, HasSmoothSobolevPath T w.velocity →
          ∀ m : ℕ, 3 ≤ m → ∀ t₀ t : ℝ, 0 ≤ t₀ → t₀ ≤ t → t < T →
            IntervalIntegrable
                (fun s : ℝ =>
                  Cgron m ν * sobolevNormAt 2 w.velocity s ^ 2 *
                      sobolevNormAt (m : ℝ) w.velocity s +
                    sobolevNormAt (m : ℝ) f s)
                volume t₀ t ∧
              sobolevNormAt (m : ℝ) w.velocity t ≤
                sobolevNormAt (m : ℝ) w.velocity t₀ +
                  ∫ s in t₀..t,
                    (Cgron m ν * sobolevNormAt 2 w.velocity s ^ 2 *
                        sobolevNormAt (m : ℝ) w.velocity s +
                      sobolevNormAt (m : ℝ) f s)

end BlowupDensity.Contracts.V2.EnergyHighPartial
