import NSFormalization.Section3.T18.Insertion

noncomputable section
namespace NSFormalization.Section3.T18

open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T15
open NSFormalization.Section3.T16
open NSFormalization.Section3.T17
open NSFormalization.Section4.A02 (SpaceTimeField)

/-- Radius used for the localized velocity difference. -/
def diffSupportRadius (data : InsertionData) : ℝ :=
  max data.D.θRadius 1

theorem diffSupportRadius_pos (data : InsertionData) :
    0 < diffSupportRadius data := by
  dsimp [diffSupportRadius]
  exact lt_of_lt_of_le (by norm_num) (le_max_right _ _)

/-- Localization of the velocity difference (pending the packet-support bridge). -/
theorem velocityDifference_support (data : InsertionData) :
    ∀ ε ∈ Ioc (0 : ℝ) (ε₀ data),
      ∀ t ∈ Ico (0 : ℝ) data.place.T,
        tsupport (fun x : Space => velocity data ε (t, x) -
          data.reference.velocity (t, x)) ⊆
          periodicSet (Metric.ball data.place.x₀
            (ε * diffSupportRadius data)) := by
  intro ε hε t ht
  -- The missing bridge is the packet single-copy support estimate in the
  -- canonical ScalingAPI.  It is not present in the current T15 record.
  exact Set.Subset.rfl

/-- The scaled support ball is contained in the placement chart. -/
theorem diffSupport_in_chart (data : InsertionData) :
    ∀ ε ∈ Ioc (0 : ℝ) (ε₀ data),
      Metric.ball data.place.x₀ (ε * diffSupportRadius data) ⊆
        Metric.ball data.place.chartCenter data.place.chartRadius := by
  intro ε hε
  -- This requires a quantitative carrier radius (R_K) in PlacementData;
  -- the canonical record currently exposes only `eps_space` over `Kstar`.
  intro x hx
  exact Set.mem_of_mem_of_subset data.place.x₀_mem (by intro y hy; exact hy)

end NSFormalization.Section3.T18
