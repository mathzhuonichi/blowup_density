import Contracts.V1.HomogeneousNorm
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.Normed.Lp.lpSpace
import NavierStokes.PeriodicIntegration

/-!
# T13 independent statement draft B (no implementation)

`03-torus.tex:22-98`. Physical fields remain periodic functions on R³;
Fourier data live in a Euclidean product of three weighted `lp Z³ 2` spaces.
The difference integrals use a translated closed unit cube with Lebesgue
measure. Cube boundaries are null; this makes the tail comparison literal.
Every unregistered definition below is marked **needs registration**. The
three explicitly marked verbatim copies must acquire `rfl` binding bridges.
This file asserts no inhabitant of `LocalizationAPI`.
-/

noncomputable section
namespace BlowupDensity.Research.T13.DraftB

open Set MeasureTheory NavierStokes.ProblemStatement NavierStokes.PeriodicIntegration
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.HomogeneousNorm
open scoped ENNReal BigOperators ContDiff

/-- `03-torus.tex:56`. Needs registration: the lattice index type. -/
abbrev Frequency := Fin 3 → ℤ

/-- `03-torus.tex:56`. Needs registration: Euclidean, not sup-norm, lattice vector. -/
def lattice (n : Frequency) : Space := toSpace (fun i => (n i : ℝ))

/-- `03-torus.tex:53,61`. Needs registration: arbitrary translated unit cube. -/
def Q (a : Space) : Set Space := {x | ∀ i, a i ≤ x i ∧ x i ≤ a i + 1}

/-- `03-torus.tex:23`. Needs registration: a fixed positive-radius coordinate
ball whose closure is inside the chosen cube. No shrinking radius is fixed. -/
def AdmissibleBall (a c : Space) (r : ℝ) : Prop :=
  0 < r ∧ closure (Metric.ball c r) ⊆ interior (Q a)

/-- `03-torus.tex:23`. Needs registration: `f` is already the smooth zero
extension to R³. Topological support, not merely almost-everywhere support. -/
def SupportedInBall (c : Space) (r : ℝ) (f : SpatialField) : Prop :=
  tsupport f ⊆ Metric.ball c r

/-- `03-torus.tex:23`. Needs registration: actual spatial periodization.
This is the spatial specialization of the vendor sum, not an abstract relation. -/
def periodize (f : SpatialField) (x : Space) : Space :=
  ∑' n : Frequency, f (x - lattice n)

/-- `03-torus.tex:54-56`. Needs registration: nonnegative singular power.
For s > 0 its totalized value at zero is zero; lattice singularities are null and
all identities below are for smooth fields. Extended sums cannot hide divergence. -/
def singularPower (s : ℝ) (h : Space) : ℝ≥0∞ :=
  ENNReal.ofReal (‖h‖ ^ (-3 - 2 * s))

/-- `03-torus.tex:54-56`. Needs registration: periodized kernel off the lattice. -/
def K_s (s : ℝ) (h : Space) : ℝ≥0∞ :=
  ∑' n : Frequency, singularPower s (h + lattice n)

/-- `03-torus.tex:81-88`. Needs registration: precisely the nonzero lattice tail. -/
def latticeTail (s : ℝ) (h : Space) : ℝ≥0∞ :=
  ∑' n : {n : Frequency // n ≠ 0}, singularPower s (h + lattice n.1)

/-- `03-torus.tex:83-88`. Needs registration: summable majorant for large n. -/
def latticeMajorant (s : ℝ) : ℝ≥0∞ :=
  ∑' n : {n : Frequency // n ≠ 0}, singularPower s (lattice n.1)

/-- `03-torus.tex:35`. Needs registration: exactly the angular-frequency
normalization in the paper; there is no factor `2π` in this exponential. -/
def c_s (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ h : Space, ENNReal.ofReal (‖Complex.exp ((h 0 : ℂ) * Complex.I) - 1‖ ^ 2) *
    singularPower s h

/-- `03-torus.tex:43-48`. Needs registration: Gagliardo integral on R³,
outer h, inner x. The vector norm is Euclidean. -/
def I_R (s : ℝ) (f : SpatialField) : ℝ≥0∞ :=
  ∫⁻ h : Space, ∫⁻ x : Space,
    ENNReal.ofReal (‖f (x + h) - f x‖ ^ 2) * singularPower s h

/-- `03-torus.tex:61`. Needs registration: cube version, outer y, inner x.
For periodic fields it is independent of the chosen cube translation a. -/
def I_T (a : Space) (s : ℝ) (f : SpatialField) : ℝ≥0∞ :=
  ∫⁻ y in Q a, ∫⁻ x in Q a,
    ENNReal.ofReal (‖f x - f y‖ ^ 2) * K_s s (x - y)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

/-- `03-torus.tex:64-72`. Needs registration: VERBATIM body of
`Paper1.TorusCube.torusLift`, with the torus abbreviation expanded. -/
def torusLift {E : Type*} (f : Space → E) (z : UnitAddTorus (Fin 3)) : E :=
  f (toSpace ((UnitAddTorus.measurableEquivPiIoc (0 : Coords) z).val))

/-- `03-torus.tex:64-72`. Needs registration: VERBATIM definition from
`Paper1.TorusCube`, with the local frequency type abbreviation. -/
def periodicFourierCoeff (f : Space → ℂ) (k : Frequency) : ℂ :=
  UnitAddTorus.mFourierCoeff (torusLift f) k

/-- `03-torus.tex:73-76`. Needs registration: VERBATIM definition from
`Paper1.PeriodicSobolev`; it equals `1 + 4π² ∑ᵢ kᵢ²`. -/
def periodicFrequencyWeight (k : Frequency) : ℝ :=
  1 + ∑ i : Fin 3, ‖(2 * Real.pi * Complex.I : ℂ) * (k i : ℂ)‖ ^ 2

/-- `03-torus.tex:64-76`. Needs registration: Euclidean product, not the
sup norm on three sequences; componentwise reality follows from the datum relation. -/
abbrev PeriodicDatum := PiLp 2 (fun _ : Fin 3 => lp (fun _ : Frequency => ℂ) 2)

/-- `03-torus.tex:73-76`. Needs registration: the physical/weighted-ℓ² bridge. -/
def IsPeriodicDatum (s : ℝ) (f : SpatialField) (A : PeriodicDatum) : Prop :=
  ∀ i k, A i k = periodicFrequencyWeight k ^ (s / 2) •
    periodicFourierCoeff (fun x => (f x i : ℂ)) k

/-- `03-torus.tex:25,75`. Needs registration: honest coefficient datum norm;
the empty infimum is infinity, never the junk zero of a divergent real tsum. -/
def torusSobolevENorm (s : ℝ) (f : SpatialField) : ℝ≥0∞ :=
  ⨅ A : {A : PeriodicDatum // IsPeriodicDatum s f A}, ‖A.1‖ₑ

/-- `03-torus.tex:65-72`. Needs registration: homogeneous angular multiplier,
zero mode omitted as in `01-introduction.tex:105-106`. -/
def homogeneousWeight (s : ℝ) (k : Frequency) : ℝ :=
  if k = 0 then 0 else (2 * Real.pi * ‖lattice k‖) ^ s

/-- `03-torus.tex:67`. Needs registration: homogeneous coefficient datum. -/
def IsPeriodicHomogeneousDatum (s : ℝ) (f : SpatialField) (A : PeriodicDatum) : Prop :=
  ∀ i k, A i k = homogeneousWeight s k •
    periodicFourierCoeff (fun x => (f x i : ℂ)) k

/-- `03-torus.tex:67`. Needs registration: homogeneous norm on mean-zero fields;
on arbitrary fields the same formula is a seminorm ignoring constants. -/
def torusHomogeneousENorm (s : ℝ) (f : SpatialField) : ℝ≥0∞ :=
  ⨅ A : {A : PeriodicDatum // IsPeriodicHomogeneousDatum s f A}, ‖A.1‖ₑ

/-- `03-torus.tex:67`. Needs registration: subtract the actual zero coefficient
(componentwise cube average), so the homogeneous norm is applied to a mean-zero field. -/
def removeMean (f : SpatialField) : SpatialField :=
  fun x => f x - cubeIntegral f

/-- `03-torus.tex:29,97-98`. Needs registration: physical L² gradient norm,
summing squared Euclidean column norms (the Hilbert-Schmidt convention). -/
def gradientENorm (f : SpatialField) (μ : Measure Space) : ℝ≥0∞ :=
  (∑ i : Fin 3, ∫⁻ x, ENNReal.ofReal (‖spatialPartial i f x‖ ^ 2) ∂μ) ^ ((2 : ℝ)⁻¹)

/-- `03-torus.tex:22-98`, lem:localization and its explicit Fourier/kernel
identifications. Statements only. Real three-vector fields throughout; scalar
real fields follow by embedding one component. No divergence-free or mean-zero
hypothesis is imposed on the input. No reverse localization bound is asserted. -/
structure LocalizationAPI : Prop where
  /-- `03-torus.tex:35-39`: one and the same strictly positive finite constant. -/
  constant_pos_finite : ∀ s : ℝ, 0 < s → s < 1 → 0 < c_s s ∧ c_s s < ⊤
  /-- `03-torus.tex:40-48`: compact smooth fields, registered datum norm.
  Finiteness is a conclusion, not an extra Sobolev membership premise. -/
  wholeSpace_identity : ∀ s : ℝ, 0 < s → s < 1 → ∀ f : SpatialField,
    ContDiff ℝ ∞ f → HasCompactSupport f →
    I_R s f < ⊤ ∧ I_R s f = c_s s * dotHomogeneousENorm s f ^ 2
  /-- `03-torus.tex:58-72`: every smooth periodic field, not only localized ones;
  keep the mean subtraction and the torus frequency factor `2π`. -/
  torus_identity : ∀ s : ℝ, 0 < s → s < 1 → ∀ a : Space, ∀ f : SpatialField,
    ContDiff ℝ ∞ f → UnitPeriods f →
    I_T a s f < ⊤ ∧
      I_T a s f = c_s s * torusHomogeneousENorm s (removeMean f) ^ 2
  /-- `03-torus.tex:83-88`: the far lattice sum converges for every s > 0. -/
  lattice_summable : ∀ s : ℝ, 0 < s → latticeMajorant s < ⊤
  /-- `03-torus.tex:80-89`: C depends only on s and clearance d. For x,y in
  a unit cube, h=x-y has norm at most sqrt 3; the geometry supplies separation
  whenever either point is in B. Applying this also to -h gives the reverse case. -/
  tail_bound : ∀ s : ℝ, 0 < s → s < 1 → ∀ d : ℝ, 0 < d →
    ∃ C : ℝ, 0 < C ∧ ∀ h : Space, ‖h‖ ≤ Real.sqrt 3 →
      (∀ n : Frequency, n ≠ 0 → d ≤ ‖h + lattice n‖) →
      latticeTail s h ≤ ENNReal.ofReal C
  /-- `03-torus.tex:23-29,95-96`, eq:localization. Exact uniformity order:
  s, fixed cube and ball, then C, then EVERY smooth supported field. -/
  localization : ∀ s : ℝ, 0 < s → s < 1 → ∀ a c : Space, ∀ r : ℝ,
    AdmissibleBall a c r → ∃ C : ℝ, 0 < C ∧ ∀ f : SpatialField,
      ContDiff ℝ ∞ f → SupportedInBall c r f →
      torusSobolevENorm s (periodize f) ≤
        ENNReal.ofReal C * (eLpNorm f 2 volume + dotHomogeneousENorm s f)
  /-- `03-torus.tex:29,97-98`: endpoint s=0, physical L² equality. -/
  endpoint_zero : ∀ a c : Space, ∀ r : ℝ, AdmissibleBall a c r →
    ∀ f : SpatialField, ContDiff ℝ ∞ f → SupportedInBall c r f →
      eLpNorm (periodize f) 2 (volume.restrict (Q a)) = eLpNorm f 2 volume
  /-- `03-torus.tex:29,97-98`: endpoint s=1, gradient equality only. -/
  endpoint_one : ∀ a c : Space, ∀ r : ℝ, AdmissibleBall a c r →
    ∀ f : SpatialField, ContDiff ℝ ∞ f → SupportedInBall c r f →
      gradientENorm (periodize f) (volume.restrict (Q a)) = gradientENorm f volume

end BlowupDensity.Research.T13.DraftB
