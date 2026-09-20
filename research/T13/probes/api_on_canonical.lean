import NSFormalization.Section3.T13.Localization
import NSFormalization.Section3.T10.PeriodicData
import Contracts.V1.Data
import Contracts.V1.HomogeneousNorm

noncomputable section

namespace NSFormalization.Section3.T13

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField)
open NSFormalization.Section4.D01 (dotHomogeneousENorm)
open NSFormalization.Section3.T10
open scoped ContDiff ENNReal BigOperators Topology

/-! The registered whole-space field and norm vocabulary is reused definitionally. -/

example :
    NSFormalization.Section4.A02.SpatialField =
      BlowupDensity.Contracts.V1.Data.SpatialField := rfl

example (s : ℝ) (f : SpatialField) :
    dotHomogeneousENorm s f =
      BlowupDensity.Contracts.V1.HomogeneousNorm.dotHomogeneousENorm s f := rfl

/-! ## Reconciled six-field API -/

/-- Statement-only API for `lem:localization` and the Fourier/Gagliardo
identifications used by its proof (`03-torus.tex:22-98`).  The range is always
`0 < s < 1`; the two endpoints are stated separately. -/
structure LocalizationAPI : Prop where
  /-- `03-torus.tex:35-39`: the defined constant `c_s` is strictly positive
  and finite for `0 < s < 1`.

  Non-vacuity: this constrains the concrete integral `cFrac s`, rather than
  allowing an arbitrary positive constant to be chosen. -/
  constant_pos_finite :
    ∀ (s : ℝ), 0 < s → s < 1 → 0 < cFrac s ∧ cFrac s < ⊤

  /-- `03-torus.tex:40-51`: the whole-space Gagliardo integral of every smooth
  compactly supported real vector field equals `c_s` times the square of the
  registered `dotHomogeneousENorm`.

  Non-vacuity: compact smooth fields exist (in particular the zero field), and
  the conclusion both proves finiteness and fixes the exact norm value. -/
  wholeSpace_identity :
    ∀ (s : ℝ), 0 < s → s < 1 → ∀ f : SpatialField,
      ContDiff ℝ ∞ f → HasCompactSupport f →
        IReal s f < ⊤ ∧
          IReal s f = cFrac s * dotHomogeneousENorm s f ^ (2 : ℕ)

  /-- `03-torus.tex:53-72`: the periodic Gagliardo integral of every smooth
  periodic vector field equals the same `c_s` times T10's homogeneous norm of
  its explicitly mean-zero part; the T10 weight retains the exact `2π` factor.

  Non-vacuity: the zero field is smooth and periodic, while the identity also
  applies to nonconstant trigonometric modes and asserts a finite integral. -/
  torus_identity :
    ∀ (s : ℝ), 0 < s → s < 1 → ∀ f : SpatialField,
      ContDiff ℝ ∞ f → IsPeriodicSpatial f →
        ITorus s f < ⊤ ∧
          ITorus s f = cFrac s *
            periodicHomogeneousENorm s (meanZeroPartT f) ^ (2 : ℕ)

  /-- `03-torus.tex:22-28,73-96`, equation `eq:localization`: for every fixed
  positive-radius ball strictly inside the fixed cube, one positive finite real
  constant is chosen before every smooth zero extension supported in that ball.
  The torus and whole-space terms use T10's `periodicSobolevENorm`, the
  registered `eLpNorm f 2 volume`, and the registered homogeneous norm.

  Non-vacuity: positive-radius balls with closure inside `(0,1)³` exist, and
  the quantifier order makes one `C_{s,B}` control every smaller support. -/
  localization :
    ∀ (s : ℝ), 0 < s → s < 1 → ∀ (c : Space) (r : ℝ),
      0 < r → closure (Metric.ball c r) ⊆ interior fundamentalCube →
        ∃ C : ℝ, 0 < C ∧ ∀ f : SpatialField,
          (ContDiff ℝ ∞ f ∧ SupportedInBall c r f) →
            periodicSobolevENorm s (periodize f) ≤
              ENNReal.ofReal C * (eLpNorm f 2 volume + dotHomogeneousENorm s f)

  /-- `03-torus.tex:29,96-98`: at `s=0`, integration over the single copy of
  the support gives equality of the physical `L²` norms.

  Non-vacuity: the equality compares the concrete periodization on the fixed
  cube with the whole-space field, under the same nonempty ball condition as
  the fractional statement. -/
  endpoint_zero :
    ∀ (c : Space) (r : ℝ),
      0 < r → closure (Metric.ball c r) ⊆ interior fundamentalCube →
        ∀ f : SpatialField, (ContDiff ℝ ∞ f ∧ SupportedInBall c r f) →
          eLpNorm (periodize f) 2 (volume.restrict fundamentalCube) =
            eLpNorm f 2 volume

  /-- `03-torus.tex:29,96-98`: at `s=1`, integration over the single copy of
  the support gives equality of the corresponding physical `L²` gradient
  norms, without identifying them with the full inhomogeneous `H¹` norm.

  Non-vacuity: this is an equality of explicit Hilbert--Schmidt gradient norms
  for every supported smooth field, not a restatement of `endpoint_zero`. -/
  endpoint_one :
    ∀ (c : Space) (r : ℝ),
      0 < r → closure (Metric.ball c r) ⊆ interior fundamentalCube →
        ∀ f : SpatialField, (ContDiff ℝ ∞ f ∧ SupportedInBall c r f) →
          gradientENorm (periodize f) (volume.restrict fundamentalCube) =
            gradientENorm f volume

end NSFormalization.Section3.T13
