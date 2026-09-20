import Contracts.V1.HomogeneousNorm
import NSFormalization.Paper1.PeriodicSobolevHilbert
import NSFormalization.Paper1.TorusCube
import NavierStokes.PeriodicLocalization

/-!
# T13 draft A: uniform localization of fractional norms

Statement-only, double-blind draft of `lem:localization`.  The physical torus
is represented by unit-periodic functions on `Space = ℝ³`.  The Gagliardo
torus integral is written on the fixed cube `[0,1]³`, rather than directly on
`UnitAddTorus`, because the periodized kernel in `03-torus.tex:53-67` is a
function of the concrete representative `x - y`.  Its Fourier coefficients
still use `Paper1.periodicFourierCoeff`, hence `torusLift` and normalized Haar
measure.

The whole-space homogeneous norm is the registered datum-infimum
`Contracts.V1.HomogeneousNorm.dotHomogeneousENorm`.  The two periodic norms and
their `lp (Fin 3 → ℤ) 2` data are local verbatim specification definitions,
flagged **needs registration (T10)** below.  The kernel, difference integrals,
chart/support predicates, and spatial periodization are likewise absent from
the registered vocabulary and are flagged **needs registration (T13)**.

All nonnegative integrals and norms take values in `ℝ≥0∞`.  This avoids a
`.toReal` finiteness side condition and is the canonical extended-nonnegative
version of the ordinary nonnegative integrals in the paper.
-/

noncomputable section

namespace BlowupDensity.Research.T13.DraftA

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NavierStokes.PeriodicIntegration
open NavierStokes.PeriodicLocalization
open NSFormalization.Paper1
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.HomogeneousNorm
open scoped BigOperators ContDiff ENNReal NNReal Topology

/-! ## Physical chart, support, and periodization -/

/-- **Needs registration (T13).**  The open representative of the chosen unit
fundamental cube.  Its closed-measure representative is `cube = [0,1]³`.
See `03-torus.tex:23,53` and `03-torus.tex:79-80`. -/
def openFundamentalCube : Set Space :=
  {x | ∀ i : Fin 3, 0 < x i ∧ x i < 1}

/-- **Needs registration (T13).**  "Coordinate ball" in
`03-torus.tex:22-23`: an honest Euclidean metric ball in the chosen chart.
The separate closure hypothesis below says that it lies strictly inside the
fundamental cube. -/
def IsCoordinateBall (B : Set Space) : Prop :=
  ∃ (x₀ : Space) (r : ℝ), 0 < r ∧ B = Metric.ball x₀ r

/-- **Needs registration (T13).**  The exact spatial lattice periodization of
a whole-space vector field, using the locally finite sum already implemented
for spacetime fields.  This renders `z_ᵀ` from `z_ℝ` in
`03-torus.tex:23` without an existential surrogate. -/
def spatialPeriodization (z : SpatialField) : SpatialField :=
  fun x => periodize (fun tx : SpaceTime => z tx.2) (0, x)

/-- **Needs registration (T13).**  The relation "`z_ᵀ` is the
periodization of `z_ℝ`" from `03-torus.tex:23`. -/
def IsSpatialPeriodization (zR zT : SpatialField) : Prop :=
  zT = spatialPeriodization zR

/-! ## Fractional kernels and difference integrals -/

/-- **Needs registration (T13).**  The extended nonnegative version of
`|h|^{-3-2s}` used in `03-torus.tex:35,43-48`.  At the single singular point
it takes the natural `⊤` value; this does not affect the Lebesgue integral. -/
def fractionalRadialKernel (s : ℝ) (h : Space) : ℝ≥0∞ :=
  (ENNReal.ofReal ‖h‖) ^ (-(3 + 2 * s))

/-- **Needs registration (T13).**  The explicitly normalized constant
`c_s = ∫_ℝ³ |exp(i h₁)-1|² |h|^{-3-2s} dh` from
`03-torus.tex:34-39`.  Positivity and finiteness for `0 < s < 1` are proof
obligations, not extra specification fields. -/
def cFrac (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ h : Space,
    ENNReal.ofReal (‖Complex.exp (Complex.I * (h 0 : ℂ)) - 1‖ ^ 2) *
      fractionalRadialKernel s h

/-- **Needs registration (T13).**  The periodic kernel
`K_s(h) = ∑_{n∈ℤ³}|h+n|^{-3-2s}` from `03-torus.tex:53-57`.
The lattice is embedded into physical `Space` by the registered periodic
localization map. -/
def KFrac (s : ℝ) (h : Space) : ℝ≥0∞ :=
  ∑' n : Lattice, fractionalRadialKernel s (h + lattice n)

/-- **Needs registration (T13).**  The nonzero-lattice tail occurring in
`03-torus.tex:81-94`, displayed there as
`∑_{n≠0}|x-y+n|^{-3-2s}`. -/
def latticeTailSum (s : ℝ) (x y : Space) : ℝ≥0∞ :=
  ∑' n : {n : Lattice // n ≠ 0},
    fractionalRadialKernel s (x - y + lattice n.1)

/-- **Needs registration (T13).**  The whole-space Gagliardo integral
`I_ℝ` from `03-torus.tex:40-49`, for a real three-vector field.  The
Euclidean norm squared is the paper's component-summed vector convention. -/
def IReal (s : ℝ) (z : SpatialField) : ℝ≥0∞ :=
  ∫⁻ h : Space, ∫⁻ x : Space,
    ENNReal.ofReal (‖z (x + h) - z x‖ ^ 2) * fractionalRadialKernel s h

/-- **Needs registration (T13).**  The torus Gagliardo integral `I_ᵀ`
from `03-torus.tex:53-67`, taken over the concrete fundamental cube so that
`K_s(x-y)` is literal. -/
def ITorus (s : ℝ) (z : SpatialField) : ℝ≥0∞ :=
  ∫⁻ x : Coords, (∫⁻ y : Coords,
    ENNReal.ofReal (‖z (toSpace x) - z (toSpace y)‖ ^ 2) *
      KFrac s (toSpace x - toSpace y) ∂cubeMeasure) ∂cubeMeasure

/-! ## Coefficient-side periodic Sobolev data -/

/-- **Needs registration (T10).**  Three componentwise copies of
`ℓ²(Fin 3 → ℤ; ℂ)`, with the outer Euclidean `PiLp 2` norm, as required
by the representation decision in `SECTION3_PLAN.md` §1. -/
abbrev PeriodicVectorDatum :=
  PiLp 2 (fun _ : Fin 3 => lp (fun _ : PeriodicFrequency => ℂ) 2)

/-- **Needs registration (T10).**  The angular frequency magnitude
`|2πk|`; see `03-torus.tex:64-72`. -/
def periodicAngularFrequency (k : PeriodicFrequency) : ℝ :=
  ‖(2 * Real.pi) • lattice k‖

/-- **Needs registration (T10).**  The coefficient datum with weight
`(1+4π²|k|²)^{s/2}` fixed by the Section 3 representation decision and
used for `H^s(ᵀ)` in `03-torus.tex:73-76`. -/
def IsPeriodicSobolevDatum (s : ℝ) (z : SpatialField)
    (A : PeriodicVectorDatum) : Prop :=
  ∀ (i : Fin 3) (k : PeriodicFrequency),
    A i k =
      (1 + periodicAngularFrequency k ^ 2) ^ (s / 2) •
        periodicFourierCoeff (fun x => ((z x i : ℝ) : ℂ)) k

/-- **Needs registration (T10).**  The coefficient-side periodic `H^s`
extended norm.  The infimum is `⊤` if the weighted coefficient datum does
not belong to `ℓ²`, matching the fail-safe registered whole-space design.
See `03-torus.tex:73-76`. -/
def periodicSobolevENorm (s : ℝ) (z : SpatialField) : ℝ≥0∞ :=
  ⨅ A : {A : PeriodicVectorDatum // IsPeriodicSobolevDatum s z A}, ‖A.1‖ₑ

/-- **Needs registration (T10).**  The coefficient datum with homogeneous
weight `|2πk|^s`, retaining the paper's `2π` factor exactly.  At positive
orders the zero coefficient is killed, so this realizes
`z - ŷ(0)` as in `03-torus.tex:64-72`. -/
def IsPeriodicHomogeneousDatum (s : ℝ) (z : SpatialField)
    (A : PeriodicVectorDatum) : Prop :=
  ∀ (i : Fin 3) (k : PeriodicFrequency),
    A i k =
      periodicAngularFrequency k ^ s •
        periodicFourierCoeff (fun x => ((z x i : ℝ) : ℂ)) k

/-- **Needs registration (T10).**  The coefficient-side periodic
`Ḋ^s(ᵀ)` extended norm used in the `I_ᵀ` identity of
`03-torus.tex:64-72`. -/
def periodicHomogeneousENorm (s : ℝ) (z : SpatialField) : ℝ≥0∞ :=
  ⨅ A : {A : PeriodicVectorDatum // IsPeriodicHomogeneousDatum s z A}, ‖A.1‖ₑ

/-! ## Endpoint quantities -/

/-- **Needs registration (T13).**  Squared whole-space `L²` norm used for
the order-zero rider in `03-torus.tex:29,96-98`. -/
def wholeL2Sq (z : SpatialField) : ℝ≥0∞ :=
  ∫⁻ x : Space, ENNReal.ofReal (‖z x‖ ^ 2)

/-- **Needs registration (T13).**  Squared single-copy torus `L²` norm used
for the order-zero rider in `03-torus.tex:29,96-98`. -/
def torusL2Sq (z : SpatialField) : ℝ≥0∞ :=
  ∫⁻ x : Coords, ENNReal.ofReal (‖z (toSpace x)‖ ^ 2) ∂cubeMeasure

/-- **Needs registration (T13).**  Sum of squared whole-space `L²` gradient
norms in the order-one rider of `03-torus.tex:29,96-98`. -/
def wholeGradientL2Sq (z : SpatialField) : ℝ≥0∞ :=
  ∑ i : Fin 3, ∫⁻ x : Space,
    ENNReal.ofReal (‖spatialPartial i z x‖ ^ 2)

/-- **Needs registration (T13).**  Sum of squared single-copy torus `L²`
gradient norms in the order-one rider of `03-torus.tex:29,96-98`. -/
def torusGradientL2Sq (z : SpatialField) : ℝ≥0∞ :=
  ∑ i : Fin 3, ∫⁻ x : Coords,
    ENNReal.ofReal (‖spatialPartial i z (toSpace x)‖ ^ 2) ∂cubeMeasure

/-! ## The four-clause localization contract -/

/-- Statement-only API for `lem:localization` and the two Fourier/Gagliardo
identifications used in its proof (`03-torus.tex:22-98`).  There are exactly
four fields: the two identities, the uniform localization estimate, and the
endpoint rider.  All clauses are vector-valued and use the same scalar `c_s`;
the scalar theorem is recovered by a one-component embedding. -/
structure LocalizationAPI : Prop where
  /-- `03-torus.tex:40-51`: for every compactly supported smooth real vector
  field and `0 < s < 1`, `I_ℝ = c_s ‖·‖²_{Ḋ^s(ℝ³)}` in the registered
  homogeneous-datum vocabulary. -/
  real_gagliardo_identity :
    ∀ (s : ℝ) (z : SpatialField), 0 < s → s < 1 →
      ContDiff ℝ ∞ z → HasCompactSupport z →
      IReal s z = cFrac s * dotHomogeneousENorm s z ^ (2 : ℝ)

  /-- `03-torus.tex:53-72`: for every smooth unit-periodic real vector field
  and `0 < s < 1`, `I_ᵀ = c_s ‖·‖²_{Ḋ^s(ᵀ)}` with the zero mode
  suppressed by the homogeneous coefficient weight. -/
  torus_gagliardo_identity :
    ∀ (s : ℝ) (z : SpatialField), 0 < s → s < 1 →
      ContDiff ℝ ∞ z → UnitPeriods z →
      ITorus s z = cFrac s * periodicHomogeneousENorm s z ^ (2 : ℝ)

  /-- `03-torus.tex:22-29,79-96`, equation `eq:localization`.  Quantifier
  order makes `C = C_{s,B}` depend only on the fixed exponent and coordinate
  ball, before the field or its (possibly shrinking) support is chosen.  The
  Euclidean `L²` term is the registered `H⁰` datum norm. -/
  uniform_localization :
    ∀ (B : Set Space), IsCoordinateBall B → closure B ⊆ openFundamentalCube →
      ∀ (s : ℝ), 0 < s → s < 1 →
        ∃ C : ℝ≥0, ∀ (zR zT : SpatialField),
          ContDiff ℝ ∞ zR → tsupport zR ⊆ B →
          IsSpatialPeriodization zR zT →
          periodicSobolevENorm s zT ≤
            (C : ℝ≥0∞) * (sobolevENorm 0 zR + dotHomogeneousENorm s zR)

  /-- `03-torus.tex:29,96-98`: periodization preserves the `L²` norm at
  order zero and the `L²` gradient norm at order one.  Squared quantities
  avoid inserting square roots and state the same equalities exactly. -/
  endpoint_identities :
    ∀ (B : Set Space), IsCoordinateBall B → closure B ⊆ openFundamentalCube →
      ∀ (zR zT : SpatialField),
        ContDiff ℝ ∞ zR → tsupport zR ⊆ B →
        IsSpatialPeriodization zR zT →
        wholeL2Sq zR = torusL2Sq zT ∧
          wholeGradientL2Sq zR = torusGradientL2Sq zT

end BlowupDensity.Research.T13.DraftA
