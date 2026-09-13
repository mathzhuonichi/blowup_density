import Contracts.V1.Data
import Contracts.V1.GradientL6

/-! Stable specification for the **proved part** of the ordinary-energy and
`H¹`-absorption *a priori* interface on `R³`.

Task `collaboration/tasks/C01.md`, graph node `C01`
(`formalization/blueprint/DEPENDENCY_GRAPH.md:275-281`: `C01 ← A02, A05`;
consumers `C01 → R43`, `C01 → R44`).  Version 1 fixes the fields of
`research/C01/Spec.lean`'s `EnergyAbsorptionAPI` that are **discharged in the
tree** by `formalization/NSFormalization/Section4/C01/{VelocityJets,ForceSlices,
Trilinear}.lean`, dropping the differential/integrated PDE displays and the
assembly that are not yet proved (see "Out of scope" below).  The mathematics is
the two *a priori* estimates that `prop:Rcritical1`
(`paper/sections/04-whole-space.tex:82`) and `prop:Rcritical2` (`:136`) quote by
name — eq:RL2 (`:118`) and eq:RH1 (`:113`) — restricted to their proved
ingredients.

## What is fixed (the five proved fields, with the paper they come from)

* `velocityJets` (`research/C01/Spec.lean:295-300`;
  `paper/sections/02-preliminaries.tex:12` eq:Rinitial, `:29-30`): every velocity
  slice `u(t,·)`, `t ∈ [0,T)`, of a classical whole-space solution is an
  `H^∞(R³;R³)` field in both the datum form `Data.MemHInfty` and the jet form
  `SmoothSquareIntegrableJets`.  The datum ⟹ jet direction (D01 unit L2) is
  closed here for velocity slices; this is the bridge on which the registered
  `A05.gradient_l6` runs.
* `forceTimeRegularity` (`Spec.lean:326-329`; `02-preliminaries.tex:17-19`
  eq:Rclasses, slicewise form of `04-whole-space.tex:119` eq:RL2, leaned on at
  `:171`): from `MemForceR f`, every future force slice is square integrable and
  `t ↦ ‖f(t)‖₂` is continuous on `[0,∞)`.
* `trilinearHolder` (`Spec.lean:410-414`; `04-whole-space.tex:107-109`): the
  three-factor Hölder inequality `|⟨(z·∇)z, Δz⟩| ≤ ‖z‖₃‖∇z‖₆‖Δz‖₂`, in `ℝ≥0∞`.
* `trilinearAbsorbed` (`Spec.lean:435-439`; `04-whole-space.tex:109-112`): its
  absorption form `|⟨(z·∇)z, Δz⟩| ≤ C₁‖z‖₃‖Δz‖₂²`, obtained from the previous by
  the registered gradient-`L⁶` clause `A05.gradient_l6` with `C₁` its constant.
* `laplacianSqENorm` (`Spec.lean:471-473`): the `ℝ≥0∞ ↔ ℝ` conversion
  `‖Δz‖₂² (as eLpNorm)² = ENNReal.ofReal (∫|Δz|²)` for the Laplacian term.

The single constant `C₁` (`Spec.lean:260`) and its positivity `C₁_pos`
(`Spec.lean:262`) are carried verbatim, because `trilinearAbsorbed` refers to
`C₁`; both are discharged by the registered `A05.gradient_l6` (its `Csix`,
`Csix_pos`).  `C₁` is read through `‖u‖₃` rather than through `y = ‖Λ^{1/2}u‖₂`,
which is the factor Hölder produces and the one
`research/section4/STATEMENTS.md:604` quotes ("`H¹` absorption once
`C₁‖u‖₃ ≤ ν/4`"); converting `‖u‖₃` to `Cy`/`CY` is A05's `velocityCriticalL3`,
not C01's.

## Out of scope, and asserted nowhere below

Not registered here, because not proved in the tree on this branch (they live in
`Section4/C01/Evolution.lean` only as the specification draft's displays, without
discharging theorems, and the other API constants `CRH1`, `CH2`, `Cassembly`
carry them):

* the ordinary energy fields `energyIdentity`, `energyDifferentialBound`,
  `l2Bound` (`Spec.lean:344-387`, eq:RL2 and its differential form);
* the enstrophy fields `enstrophyIdentity`, `enstrophyDifferentialBound`,
  `enstrophyIntegralBound` (`Spec.lean:487-541`, eq:RH1 and its integrated form);
* the Fourier inequality `sobolevTwoFourier` (`Spec.lean:555-558`,
  `04-whole-space.tex:123`) and the assembly `h2TimeIntegral`,
  `h2TimeIntegralZeroDatum` (`Spec.lean:576-607`, `:127-130`);
* the constants `CRH1`, `CH2`, `Cassembly` and their positivity, mentioned only
  by those excluded fields, and the whole registered API `gradientL6 :
  GradientL6API` carried by `Spec.lean` (its standalone objects `gradientTensor`,
  `laplacian`, `SmoothSquareIntegrableJets` are all this record uses, so the
  bundled record is not needed here).

Also asserted nowhere: eq:Rcritical1/eq:Rcritical2 (the critical `Ḣ^{1/2}`/`H^{1/2}`
estimates), the Grönwall and first-crossing arguments of the two propositions,
the continuity bootstrap, the continuation criterion eq:criterion (A04), and
every torus / `Λ` / `J` / Leray-projection quantity — exactly as `Spec.lean`'s
"Out of scope" section records for the full draft.

## Conventions

* Every object quantified over is the canonical one of
  `verification/Contracts/V1/Data.lean`: `initialClassR` is `X_R`, `MemForceR` is
  `F_R`, `ClassicalSolutionR ν a f T` the classical solution on `[0,T)`,
  `MemHInfty` is `H^∞`.  `gradientTensor`, `laplacian`, `SmoothSquareIntegrableJets`
  are the **registered** `Contracts.V1.GradientL6` objects
  (`verification/Contracts/V1/GradientL6.lean:89,94,106`), used unchanged so that
  the registered clause `GradientL6API.gradientLSix` applies verbatim.
* Time is the first spacetime coordinate; the squared `L²` quantities are real
  Bochner integrals (`velocityJets` supplies the integrability that keeps them
  from being Mathlib's junk `0`), while the critical `L³` norm and the `L²`/`L⁶`
  `eLpNorm`s stay `ℝ≥0∞` and are never routed through `.toReal`.

`Contracts.V1.Data` supplies `SpatialField`, `SpaceTimeField`, `ClassicalSolutionR`,
`initialClassR`, `MemForceR`, `MemHInfty` directly; `Contracts.V1.GradientL6`
supplies `lift`, `gradientTensor`, `laplacian`, `SmoothSquareIntegrableJets`.
Only the six spec-local time-slice `def`s `slice`, `l2Sq`, `l2Norm`,
`laplacianSq`, `criticalL3`, `advectionWork` (`research/C01/Spec.lean:167,172,177,
191,212,202`) — which have no `Data.lean` declaration — are restated verbatim
below; `Bindings.EnergyAbsorptionPartial` records by `rfl` that each is the
implementation's. -/

noncomputable section

namespace BlowupDensity.Contracts.V1.EnergyAbsorptionPartial

open Set MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1
  (lift gradientTensor laplacian SmoothSquareIntegrableJets)
open BlowupDensity.Contracts.V1.Data
open scoped ContDiff ENNReal

/-! ## 1. Spec-local time-slice quantities (`research/C01/Spec.lean:167-212`) -/

/-- `research/C01/Spec.lean:167`: the spatial slice `z(t) = z(t,·)` of a
spacetime field.  Time is the first spacetime coordinate. -/
def slice (z : SpaceTimeField) (t : ℝ) : SpatialField := fun x => z (t, x)

/-- `research/C01/Spec.lean:172`: `04-whole-space.tex:119` eq:RL2, the squared
`L²(R³)` norm `∫|z|²` of a spatial field, real-valued. -/
def l2Sq (z : SpatialField) : ℝ := ∫ x : Space, ‖z x‖ ^ 2

/-- `research/C01/Spec.lean:177`: `04-whole-space.tex:119` eq:RL2, `‖z‖₂` itself,
the square root of `l2Sq`. -/
def l2Norm (z : SpatialField) : ℝ := Real.sqrt (l2Sq z)

/-- `research/C01/Spec.lean:191`: `04-whole-space.tex:109,115`, `‖Δz‖₂²` as a real
Bochner integral of the squared pointwise norm of the componentwise Euclidean
Laplacian.  `laplacian` is the registered `Contracts/V1/GradientL6.lean:94`
object. -/
def laplacianSq (z : SpatialField) : ℝ := ∫ x : Space, ‖laplacian z x‖ ^ 2

/-- `research/C01/Spec.lean:212`: `04-whole-space.tex:109,171`, `‖z‖₃`, the
critical Lebesgue norm in which the absorption hypothesis is stated.  Kept in
`ℝ≥0∞` and never differentiated. -/
def criticalL3 (z : SpatialField) : ℝ≥0∞ := eLpNorm z 3 volume

/-- `research/C01/Spec.lean:202`: `04-whole-space.tex:108`, `⟨(z·∇)z, Δz⟩`, the
nonlinear work against the Laplacian.  `advection` is the pinned upstream
`(z·∇)z` on the time-independent lift, matching `laplacian` and
`gradientTensor`. -/
def advectionWork (z : SpatialField) : ℝ :=
  ∫ x : Space, (inner ℝ (advection (lift z) 0 x) (laplacian z x) : ℝ)

/-! ## 2. The contract -/

/-- The **proved** fields of the ordinary-energy and `H¹`-absorption *a priori*
interface on `R³` (`paper/sections/04-whole-space.tex:96-131`, reused at `:171`),
in exactly the form `research/C01/Spec.lean`'s `EnergyAbsorptionAPI` states them,
with the differential/integrated PDE displays, the Fourier inequality, the
assembly and the constants only they use removed; see the module docstring.

No field is a hypothesis about an unspecified proposition, and no field is
`True`, `∃ x, True` or any similar placeholder. -/
structure EnergyAbsorptionPartialAPI where
  /-- `04-whole-space.tex:110`, the constant of `‖u‖₃‖∇u‖₆‖Δu‖₂ ≤ C₁y‖Δu‖₂²`, read
  through `‖u‖₃` (`research/section4/STATEMENTS.md:604`).  Universal: independent
  of `ν`, of the datum and of the solution.  The proof takes `C₁` to be the
  constant of the registered `A05.gradient_l6`. -/
  C₁ : ℝ
  /-- Positivity of `C₁`; it is a divisor in the threshold `ν/(4C₁)`. -/
  C₁_pos : 0 < C₁

  /-- **`velocityJets`** (`research/C01/Spec.lean:295-300`;
  `paper/sections/02-preliminaries.tex:12` eq:Rinitial, `:29-30` "a classical
  velocity belongs to `C([0,S];H^m)` for every integer `m ≥ 0`"): every velocity
  slice `u(t,·)`, `t ∈ [0,T)`, is an `H^∞(R³;R³)` field in both the datum form
  `Data.MemHInfty` and the jet form `Contracts.V1.SmoothSquareIntegrableJets`, on
  which the registered `A05.gradient_l6` runs. -/
  velocityJets :
    ∀ (ν : ℝ), 0 < ν → ∀ a : SpatialField, a ∈ initialClassR →
      ∀ f : SpaceTimeField, MemForceR f →
        ∀ (T : ℝ) (w : ClassicalSolutionR ν a f T), ∀ t ∈ Ico (0 : ℝ) T,
          MemHInfty (slice w.velocity t) ∧
            SmoothSquareIntegrableJets (slice w.velocity t)

  /-- **`forceTimeRegularity`** (`research/C01/Spec.lean:326-329`;
  `02-preliminaries.tex:17-19` eq:Rclasses, slicewise form of
  `04-whole-space.tex:119` eq:RL2): from `MemForceR f`, every future spatial slice
  is square integrable and `t ↦ ‖f(t)‖₂` is continuous on the closed half line
  `[0,∞)`.  Interval integrability of `s ↦ ‖f(s)‖₂` and `s ↦ ‖f(s)‖₂²` on each
  `[0,t]` is a consequence of the continuity conjunct and is not restated. -/
  forceTimeRegularity :
    ∀ f : SpaceTimeField, MemForceR f →
      (∀ t : ℝ, 0 ≤ t → MemLp (slice f t) 2 volume) ∧
        ContinuousOn (fun s => l2Norm (slice f s)) (Ici (0 : ℝ))

  /-- **`trilinearHolder`** (`research/C01/Spec.lean:410-414`;
  `04-whole-space.tex:107-109`): the three-factor Hölder inequality
  `|⟨(z·∇)z, Δz⟩| ≤ ‖z‖₃‖∇z‖₆‖Δz‖₂`, exponents `1/3 + 1/6 + 1/2 = 1`.  Stated in
  `ℝ≥0∞` because the `L³` and `L⁶` factors are `eLpNorm`s that are never
  differentiated; the hypothesis is the jet form (`velocityJets` hands it out for
  velocity slices). -/
  trilinearHolder :
    ∀ z : SpatialField, SmoothSquareIntegrableJets z →
      ENNReal.ofReal |advectionWork z| ≤
        criticalL3 z * eLpNorm (gradientTensor z) 6 volume *
          eLpNorm (laplacian z) 2 volume

  /-- **`trilinearAbsorbed`** (`research/C01/Spec.lean:435-439`;
  `04-whole-space.tex:109-112`): the absorption form
  `|⟨(z·∇)z, Δz⟩| ≤ C₁‖z‖₃‖Δz‖₂²`, obtained from `trilinearHolder` by the
  registered `A05.gradient_l6`'s `‖∇v‖₆ ≤ C‖Δv‖₂`.  The right-hand side is `‖Δz‖₂²`
  as an `ℝ≥0∞` square; `laplacianSqENorm` converts it to the real
  `laplacianSq`. -/
  trilinearAbsorbed :
    ∀ z : SpatialField, SmoothSquareIntegrableJets z →
      ENNReal.ofReal |advectionWork z| ≤
        ENNReal.ofReal C₁ * criticalL3 z *
          eLpNorm (laplacian z) 2 volume ^ (2 : ℝ)

  /-- **`laplacianSqENorm`** (`research/C01/Spec.lean:471-473`): the one
  conversion between the contract's two number systems on the Laplacian term,
  `eLpNorm (Δz) 2 volume ^ 2 = ENNReal.ofReal (∫|Δz|²)`.  An equality, not a
  bound, and `.toReal`-free: the left side is `⊤` exactly when `Δz ∉ L²`, and on
  the jet class it never is.  Both sides are objects of the same field
  `laplacian z`, so this is bookkeeping, not analysis. -/
  laplacianSqENorm :
    ∀ z : SpatialField, SmoothSquareIntegrableJets z →
      eLpNorm (laplacian z) 2 volume ^ (2 : ℝ) = ENNReal.ofReal (laplacianSq z)

end BlowupDensity.Contracts.V1.EnergyAbsorptionPartial
