import NSFormalization.Paper3.AngularFourierDilation
import NSFormalization.Paper3.RealVectorPositiveDensity
import NSFormalization.Paper3.PositiveTemporalDensity
import NSFormalization.Source.RealSobolev
import NavierStokes.R3.ProblemStatement

/-!
# The D01 solution class, restated for `Section4.A02`

This module is the **single** A02-local restatement of the Section-4 solution
class of `verification/Contracts/V1/Data.lean`:  `ClassicalSolutionR`
(`:624-648`), `maximalLifespanR` (`:657`), `RegularThrough` (`:664`),
`PressureGaugeEquivOn` (`:589`), `initialClassR` (`:509`), `MemForceR` (`:544`)
and `IsSobolevDatum` (`:160`), together with the supporting `IsSobolevPath`,
`MemHInfty`, `IsSolenoidal` and the field/time-domain abbreviations.  Every one of the
A02 units imports it — `Restrict.lean` (U4), `Order.lean` (U6) and `Energy.lean`
(U1a) — so there is exactly one copy in the `A02` namespace (lane 040 deleted the
byte-identical inline copy that lane 032 had left in `Restrict.lean` §0).

The `NSFormalization` package is a *dependency* of the `Contracts` library and
cannot import it, so the objects below are restated **verbatim**, token for token
with `Contracts/V1/Data.lean` (the abbreviation `SpatialField` and friends
included).  Every field type is therefore definitionally the contract's, so a
`verification/Bindings` module can move a `ClassicalSolutionR` across the two
copies field by field and discharge each contract statement by `exact`.  A `rfl`
bridge is not available for the structure itself: two separately declared
structures are distinct inductive types.

## Canonical copy, and the relation to the D01 copies

`Section4/D01/{SmoothDatum,ForceClass}.lean` carry their own restatements of
`IsSobolevDatum`, `IsSobolevPath`, `MemForceR`, `futureTimes` and
`forceTimeMeasure`.  They are **definitionally equal** to the ones here — lane
040 verified `example : A02.IsSobolevDatum = D01.IsSobolevDatum := rfl` and the
same for `IsSobolevPath`, `MemForceR`, `futureTimes`, `forceTimeMeasure` — so a
`Bindings` or downstream module discharges either from the other by `exact` with
no transport.  They are **not token-identical**, however: the D01 copies unfold
`SpatialField`/`SpaceTimeField` to `Space → Space`/`VelocityField`, whereas the
copies here keep the abbreviations, matching `Contracts/V1/Data.lean` on the
nose.  This module is therefore kept as the canonical copy for the A02 chain and
does **not** import the D01 ones: (i) the token-for-token agreement with the
contract is what the `Bindings` `rfl` bridges rely on, and (ii) importing
`D01.SmoothDatum`/`D01.ForceClass` would drag their ~35-module analytic closure
into the otherwise lightweight `Restrict`/`Order` (which need only `Paper3` and
`NavierStokes.R3.ProblemStatement`).  No `rfl` bridge lemma is stated here for
the same import-hygiene reason; the equalities are recorded in
`research/A02/ATTEMPTS_SIMP.md`.  `Energy.lean` alone imports D01 (unit U1a is
analytic), and there the A02↔D01 datum defeq is used directly.
-/

noncomputable section

namespace NSFormalization.Section4.A02

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Paper3
open NSFormalization.Source.RealSobolev (FourierData)
open scoped ContDiff ENNReal SchwartzMap

/-! ## 0. The D01 objects, restated verbatim from `Contracts/V1/Data.lean` -/

/-- `Data.lean:99`. -/
abbrev SpatialField := Space → Space

/-- `Data.lean:104`. -/
abbrev SpaceTimeField := VelocityField

/-- `Data.lean:108`. -/
abbrev SpaceTimeScalar := PressureField

/-- `Data.lean:113`. -/
abbrev futureTimes : Set ℝ := Ici (0 : ℝ)

/-- `Data.lean:118`. -/
abbrev forceTimeMeasure : Measure ℝ := positiveTimeMeasure

/-- `Data.lean:160`, restated verbatim. -/
def IsSobolevDatum (s : ℝ) (z : SpatialField) (A : RealVectorSobolev s) : Prop :=
  ∀ (i : Fin 3) (ψ : SchwartzMap Space ℂ),
    angularRealization s ((A i : FourierData)) ψ = ∫ x : Space, ψ x * ((z x i : ℝ) : ℂ)

/-- `Data.lean:174`. -/
def IsSobolevPath (s : ℝ) (f : SpaceTimeField) (G : ℝ → RealVectorSobolev s) : Prop :=
  ∀ t : ℝ, 0 ≤ t → IsSobolevDatum s (fun x => f (t, x)) (G t)

/-- `Data.lean:495`, the datum form of `H^∞`. -/
def MemHInfty (a : SpatialField) : Prop :=
  ContDiff ℝ ∞ a ∧
    ∀ m : ℕ, ∃ A : RealVectorSobolev (m : ℝ), IsSobolevDatum (m : ℝ) a A

/-- `Data.lean:504`. -/
def IsSolenoidal (a : SpatialField) : Prop :=
  ∀ x : Space, spatialDivergence (fun z : SpaceTime => a z.2) 0 x = 0

/-- `Data.lean:509`, the initial class `X_R = H^∞ ∩ L²_σ`. -/
def initialClassR : Set SpatialField := {a | MemHInfty a ∧ IsSolenoidal a}

/-- `Data.lean:544`, the force class `F_R`. -/
def MemForceR (f : SpaceTimeField) : Prop :=
  ContDiffOn ℝ ∞ f futureDomain ∧
    ∀ m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
      IsSobolevPath (m : ℝ) f G ∧
      ContDiffOn ℝ ∞ G futureTimes ∧
      MemLp G 1 forceTimeMeasure ∧
      MemLp G 2 forceTimeMeasure

/-- `Data.lean:589`: two pressures differ by a function of time alone on `I`. -/
def PressureGaugeEquivOn (I : Set ℝ) (p q : SpaceTimeScalar) : Prop :=
  ∃ c : ℝ → ℝ, ∀ t ∈ I, ∀ x : Space, q (t, x) = p (t, x) + c t

/-- `Data.lean:624-648`: a classical whole-space solution of eq:NS on `[0,T)`
at viscosity `ν`, with initial velocity `a` and force `f`. -/
structure ClassicalSolutionR (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ) where
  /-- The velocity field. -/
  velocity : SpaceTimeField
  /-- The pressure field, fixed only up to a function of time. -/
  pressure : SpaceTimeScalar
  /-- The horizon is a genuine interval. -/
  horizon_pos : 0 < T
  /-- Smoothness on `[0,T) × R³`, one-sided at `t = 0`. -/
  velocity_smooth : ContDiffOn ℝ ∞ velocity (Ico (0 : ℝ) T ×ˢ (univ : Set Space))
  /-- Smoothness of the pressure on `[0,T) × R³`. -/
  pressure_smooth : ContDiffOn ℝ ∞ pressure (Ico (0 : ℝ) T ×ˢ (univ : Set Space))
  /-- `u(·,0) = a`. -/
  initial : ∀ x : Space, velocity (0, x) = a x
  /-- `∇·u = 0` on `[0,T)`. -/
  divergence : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space, spatialDivergence velocity t x = 0
  /-- eq:NS at viscosity `ν`, at interior times. -/
  momentum : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : Space,
    NavierStokesR3.ProblemStatement.navierStokesResidual ν velocity pressure t x = f (t, x)
  /-- `u ∈ C([0,S];H^m)` for every integer `m ≥ 0` on each compact subinterval. -/
  sobolev : ∀ m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
    ContinuousOn G (Ico (0 : ℝ) T) ∧
      ∀ t ∈ Ico (0 : ℝ) T, IsSobolevDatum (m : ℝ) (fun x => velocity (t, x)) (G t)
  /-- `∇p ∈ L²`; excludes a nonzero constant pressure gradient. -/
  pressure_gradient : ∀ t ∈ Ico (0 : ℝ) T,
    MemLp (fun x : Space => pressureGradient pressure t x) 2 volume

/-- `Data.lean:657`: `T^ν_{max,R}(a,f)`, the supremum of the horizons carrying a
classical solution.  The empty supremum is `0`. -/
def maximalLifespanR (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) : ℝ≥0∞ :=
  ⨆ S : ℝ, ⨆ _ : Nonempty (ClassicalSolutionR ν a f S), ENNReal.ofReal S

/-- `Data.lean:664`: "regular through `T`". -/
def RegularThrough (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ Nonempty (ClassicalSolutionR ν a f (T + δ))

end NSFormalization.Section4.A02
