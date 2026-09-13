import NSFormalization.Paper1.PeriodicSingleModeLocal
import NSFormalization.Paper1.PeriodicDensityDichotomy

/-!
# Single-mode slice of the periodic density branch

The explicit transverse heat mode is an admissible manuscript initial datum and
has a positive unforced flow horizon.  This adapter feeds that concrete witness
into the already proved subcritical singular-force insertion branch.  It makes
no claim of local existence for arbitrary admissible periodic data.
-/
noncomputable section
namespace NSFormalization.Paper1.PeriodicSingleModeDensity

open Set MeasureTheory
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Source
open NSFormalization.Paper1.PeriodicForceSpace
open NSFormalization.Paper1.PeriodicLifespan
open NSFormalization.Paper1.PeriodicDensityFiber
open NSFormalization.Paper1.PeriodicDensityDichotomy
open NSFormalization.Paper1.PeriodicInitialData
open NSFormalization.Paper1.PeriodicSingleModeLocal
open scoped ContDiff ENNReal

/-- The initial datum of the explicit unit-period transverse heat mode. -/
def singleModeInitial (A : ℝ) : Space → Space :=
  fun x => (A * Real.sin ((2 * Real.pi) * x 1)) • coordinateVector 0

/-- The explicit mode belongs to the corrected manuscript initial-data class.
This is extracted from its actual unforced flow witness, so smoothness,
periodicity, and divergence-freeness are all witnessed at time zero. -/
theorem singleModeInitial_admissible (ν A : ℝ) :
    IsAdmissibleInitialData (singleModeInitial A) := by
  have hW := (singleModeHeatFlow ν A).some
  change IsAdmissibleInitialData (fun x =>
    (A * Real.sin ((2 * Real.pi) * x 1)) • coordinateVector 0)
  exact hW.initial_admissible

/-- The explicit mode supplies the local unforced-flow premise required by the
fixed-profile density branch. -/
theorem singleMode_unforced_local (ν A : ℝ) :
    ∃ R : ℝ, Nonempty (Flow ν (singleModeInitial A) (0 : VelocityField) R) := by
  refine ⟨1, ?_⟩
  change Nonempty (Flow ν
    (fun x => (A * Real.sin ((2 * Real.pi) * x 1)) • coordinateVector 0)
    (0 : VelocityField) 1)
  exact singleModeHeatFlow ν A

/- The explicit witness gives a quantitative fixed-slice certificate.  This is
not an assertion of local existence for arbitrary admissible data: the only
initial datum here is the displayed single Fourier mode, and the lower bound
comes from its concrete unit-horizon Flow. -/
theorem singleMode_fixed_slice_certificate (ν A : ℝ) :
    IsAdmissibleInitialData (singleModeInitial A) ∧
      ∃ R : ℝ, 0 < R ∧
        Nonempty (Flow ν (singleModeInitial A) (0 : VelocityField) R) ∧
        ENNReal.ofReal R ≤ lifespan ν (singleModeInitial A) (0 : VelocityField) := by
  refine ⟨singleModeInitial_admissible ν A, 1, by norm_num, ?_, ?_⟩
  · change Nonempty (Flow ν
      (fun x => (A * Real.sin ((2 * Real.pi) * x 1)) • coordinateVector 0)
      (0 : VelocityField) 1)
    exact singleModeHeatFlow ν A
  · change ENNReal.ofReal (1 : ℝ) ≤
      lifespan ν
        (fun x => (A * Real.sin ((2 * Real.pi) * x 1)) • coordinateVector 0)
        (0 : VelocityField)
    exact horizon_le_lifespan (singleModeHeatFlow ν A).some

/-- For every test force and subcritical Sobolev index, the single-mode initial
data admits arbitrarily close inserted forces whose actual flow has positive
lifespan bounded by the prescribed deadline.  The force is returned together
with the actual positive-horizon flow witness; this is the concrete
single-mode slice of the existing density branch. -/
theorem singleMode_density_branch
    {ν T s A : ℝ} (hν : 0 < ν) (hT : 0 < T) (hs : s < 1 / 2)
    {g : VelocityField} (hg : IsTestForce g) {ρ : ℝ≥0∞} (hρ : 0 < ρ) :
    ∃ G : VelocityField, IsTestForce G ∧ forceDistance s G g < ρ ∧
      (∃ R : ℝ, Nonempty (Flow ν (singleModeInitial A) G R)) ∧
      0 < lifespan ν (singleModeInitial A) G ∧
      lifespan ν (singleModeInitial A) G ≤ ENNReal.ofReal T := by
  obtain ⟨R, hR⟩ := singleMode_unforced_local ν A
  change ∃ G : VelocityField, IsTestForce G ∧ forceDistance s G g < ρ ∧
      (∃ R : ℝ, Nonempty (Flow ν
        (fun x => (A * Real.sin ((2 * Real.pi) * x 1)) • coordinateVector 0) G R)) ∧
      0 < lifespan ν
        (fun x => (A * Real.sin ((2 * Real.pi) * x 1)) • coordinateVector 0) G ∧
      lifespan ν (fun x => (A * Real.sin ((2 * Real.pi) * x 1)) • coordinateVector 0) G ≤
        ENNReal.ofReal T
  exact exists_nearby_singular_force_of_unforced_localFlow hν hT hs hR.some hg hρ

/-- The admissibility certificate and the density branch can be obtained
simultaneously for the explicit mode. -/
theorem singleMode_admissible_density_branch
    {ν T s A : ℝ} (hν : 0 < ν) (hT : 0 < T) (hs : s < 1 / 2)
    {g : VelocityField} (hg : IsTestForce g) {ρ : ℝ≥0∞} (hρ : 0 < ρ) :
    IsAdmissibleInitialData (singleModeInitial A) ∧
      (∃ G : VelocityField, IsTestForce G ∧ forceDistance s G g < ρ ∧
        (∃ R : ℝ, Nonempty (Flow ν (singleModeInitial A) G R)) ∧
        0 < lifespan ν (singleModeInitial A) G ∧
        lifespan ν (singleModeInitial A) G ≤ ENNReal.ofReal T) := by
  exact ⟨singleModeInitial_admissible ν A,
    singleMode_density_branch hν hT hs hg hρ⟩

end NSFormalization.Paper1.PeriodicSingleModeDensity
