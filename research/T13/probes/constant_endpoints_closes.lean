import NSFormalization.Section3.T13.ConstantEndpoints
import NSFormalization.Section3.T10.PeriodicData
import Contracts.V1.Data
import Contracts.V1.HomogeneousNorm
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Lane 344 closure probe

`research/` is not a Lean module root, so this probe restates
`research/T13/probes/api_on_canonical.lean`'s `LocalizationAPI` **verbatim**
(copied character for character from that file) and then shows that the three
fields proved by lane 344 close against it:

* `constant_pos_finite`
* `endpoint_zero`
* `endpoint_one`

`localizationAPI_of_remaining_fields` is the mechanical check: it builds the
full six-field record from the three proved theorems plus the three fields that
are *not* in lane 344's scope, supplied verbatim as hypotheses.  Those three
hypotheses are not a peeling input of the shipped module
`NSFormalization.Section3.T13.ConstantEndpoints`, which assumes nothing; they
are the targets of the sibling proof lanes 345/346 and appear here only so that
the three proved fields are type-checked against the real record fields.

The last section is the non-vacuity witness: an explicit smooth, nonzero field
supported in an explicit admissible ball, on which both endpoint identities are
instantiated.
-/

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

/-! ## The three fields proved by lane 344, each closed verbatim -/

example :
    ∀ (s : ℝ), 0 < s → s < 1 → 0 < cFrac s ∧ cFrac s < ⊤ :=
  constant_pos_finite

example :
    ∀ (c : Space) (r : ℝ),
      0 < r → closure (Metric.ball c r) ⊆ interior fundamentalCube →
        ∀ f : SpatialField, (ContDiff ℝ ∞ f ∧ SupportedInBall c r f) →
          eLpNorm (periodize f) 2 (volume.restrict fundamentalCube) =
            eLpNorm f 2 volume :=
  endpoint_zero

example :
    ∀ (c : Space) (r : ℝ),
      0 < r → closure (Metric.ball c r) ⊆ interior fundamentalCube →
        ∀ f : SpatialField, (ContDiff ℝ ∞ f ∧ SupportedInBall c r f) →
          gradientENorm (periodize f) (volume.restrict fundamentalCube) =
            gradientENorm f volume :=
  endpoint_one

/-- Mechanical field-by-field check against the record: the three lane-344
theorems fill exactly their three `LocalizationAPI` slots.  The other three
fields are hypotheses here (lanes 345/346), never in the shipped module. -/
theorem localizationAPI_of_remaining_fields
    (hWholeSpace :
      ∀ (s : ℝ), 0 < s → s < 1 → ∀ f : SpatialField,
        ContDiff ℝ ∞ f → HasCompactSupport f →
          IReal s f < ⊤ ∧
            IReal s f = cFrac s * dotHomogeneousENorm s f ^ (2 : ℕ))
    (hTorus :
      ∀ (s : ℝ), 0 < s → s < 1 → ∀ f : SpatialField,
        ContDiff ℝ ∞ f → IsPeriodicSpatial f →
          ITorus s f < ⊤ ∧
            ITorus s f = cFrac s *
              periodicHomogeneousENorm s (meanZeroPartT f) ^ (2 : ℕ))
    (hLocalization :
      ∀ (s : ℝ), 0 < s → s < 1 → ∀ (c : Space) (r : ℝ),
        0 < r → closure (Metric.ball c r) ⊆ interior fundamentalCube →
          ∃ C : ℝ, 0 < C ∧ ∀ f : SpatialField,
            (ContDiff ℝ ∞ f ∧ SupportedInBall c r f) →
              periodicSobolevENorm s (periodize f) ≤
                ENNReal.ofReal C * (eLpNorm f 2 volume + dotHomogeneousENorm s f)) :
    LocalizationAPI where
  constant_pos_finite := constant_pos_finite
  wholeSpace_identity := hWholeSpace
  torus_identity := hTorus
  localization := hLocalization
  endpoint_zero := endpoint_zero
  endpoint_one := endpoint_one

/-! ## Non-vacuity

`cFrac` is the concrete `ℝ≥0∞`-valued integral of the paper, not an abstract
constant; and the endpoint hypotheses are satisfied by an explicit smooth
nonzero field supported in an explicit admissible ball. -/

example (s : ℝ) :
    cFrac s =
      ∫⁻ h : Space,
        ENNReal.ofReal (‖Complex.exp (Complex.I * (h 0 : ℂ)) - 1‖ ^ 2) *
          fractionalRadialKernel s h := rfl

example : 0 < cFrac (1/2 : ℝ) ∧ cFrac (1/2 : ℝ) < ⊤ :=
  constant_pos_finite (1/2) (by norm_num) (by norm_num)

/-- Centre of the fundamental cube. -/
def probeCenter : Space := (EuclideanSpace.equiv (Fin 3) ℝ).symm (fun _ => (1/2 : ℝ))

/-- A genuine smooth bump supported in `closedBall probeCenter (1/4)`. -/
def probeBump : ContDiffBump probeCenter := ⟨1/8, 1/4, by norm_num, by norm_num⟩

/-- A nonzero smooth vector field supported in `ball probeCenter (3/8)`. -/
def probeField : SpatialField := fun x => (probeBump x) • coordinateVector 0

theorem probe_ball_admissible :
    closure (Metric.ball probeCenter (3/8 : ℝ)) ⊆ interior fundamentalCube := by
  refine (Metric.closure_ball_subset_closedBall).trans ?_
  rw [interior_fundamentalCube]
  intro x hx i
  have hd : ‖x - probeCenter‖ ≤ 3/8 := by
    rw [← dist_eq_norm]; exact hx
  have h1 : |x i - probeCenter i| ≤ 3/8 := by
    have h := abs_spaceCoord_le_norm (x - probeCenter) i
    have h2 : (x - probeCenter) i = x i - probeCenter i := rfl
    rw [h2] at h
    linarith
  have hc : probeCenter i = 1/2 := rfl
  rw [hc, abs_le] at h1
  exact ⟨by linarith [h1.1], by linarith [h1.2]⟩

theorem probeField_contDiff : ContDiff ℝ ∞ probeField :=
  probeBump.contDiff.smul contDiff_const

theorem probeField_supported : SupportedInBall probeCenter (3/8 : ℝ) probeField := by
  have hsub : Function.support probeField ⊆ Function.support (⇑probeBump) := by
    intro x hx
    simp only [Function.mem_support] at hx ⊢
    intro hg
    exact hx (by simp [probeField, hg])
  have h1 : tsupport probeField ⊆ tsupport (⇑probeBump) := closure_mono hsub
  rw [probeBump.tsupport_eq] at h1
  refine h1.trans ?_
  intro y hy
  rw [Metric.mem_closedBall] at hy
  rw [Metric.mem_ball]
  have hr : probeBump.rOut = 1/4 := rfl
  rw [hr] at hy
  linarith

/-- The witness field is not the zero field, so neither endpoint identity is
vacuous. -/
theorem probeField_ne_zero : probeField probeCenter ≠ 0 := by
  have h1 : probeBump probeCenter = 1 :=
    probeBump.one_of_mem_closedBall (Metric.mem_closedBall_self probeBump.rIn_pos.le)
  have h2 : probeField probeCenter = coordinateVector 0 := by
    simp [probeField, h1]
  rw [h2]
  intro hcon
  have hz : (coordinateVector (0 : Fin 3)) 0 = 0 := by rw [hcon]; rfl
  rw [coordinateVector] at hz
  simp at hz

example :
    eLpNorm (periodize probeField) 2 (volume.restrict fundamentalCube) =
      eLpNorm probeField 2 volume :=
  endpoint_zero probeCenter (3/8) (by norm_num) probe_ball_admissible probeField
    ⟨probeField_contDiff, probeField_supported⟩

example :
    gradientENorm (periodize probeField) (volume.restrict fundamentalCube) =
      gradientENorm probeField volume :=
  endpoint_one probeCenter (3/8) (by norm_num) probe_ball_admissible probeField
    ⟨probeField_contDiff, probeField_supported⟩

end NSFormalization.Section3.T13
