import NSFormalization.Section3.T17.ArticleScope
import NSFormalization.Section3.T20.CriticalEnergy
import NSFormalization.Section3.T21.Zero
import NSFormalization.Section3.T24.ConservativeAssembly

noncomputable section

namespace Review493

open Set Metric
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10 NSFormalization.Section3.T15
open NSFormalization.Section3.T16 NSFormalization.Section3.T17
open NSFormalization.Section3.T24
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)

def packet := BlowupDensity.Bindings.packetImportFamily.select (1 : ℝ) (by norm_num)

def place : PlacementData packet.velocity packet.pressure packet.force packet.carrier :=
  placementData packet.carrier_compact packet.force_support.1 1 (by norm_num)

def reference : ClassicalSolutionT 1 (0 : SpatialField) (conservativeForceT 0) (place.T + 1) :=
  restSolution 1 (place.T + 1) (by change (0 : ℝ) < 1 + 1; norm_num)

/-- The article-scope conclusion is inhabited for the registered packet and a
genuine zero classical reference; in particular, its scale interval is not
made vacuous by an inconsistent hypothesis block. -/
theorem zero_reference_nonvacuity :
    (∃ D : CutoffData,
      LocalPotentialAPI
          (NSFormalization.Section3.T19.extendByZero reference).velocity
          packet.velocity place.Kstar place.x₀ (1 / 4) place.T 1 D ∧
        Nonempty
          (CorrectionAPI 1 place
            (NSFormalization.Section3.T19.extendByZero reference).velocity
            (1 / 4) 1 D)) ∧
      ∀ t ∈ Ico (0 : ℝ) (place.T + 1), ∀ x,
        (NSFormalization.Section3.T19.extendByZero reference).velocity (t, x) =
          reference.velocity (t, x) := by
  apply correctionStatementArticle_holds
      1 packet.velocity packet.pressure packet.force packet.carrier place
      (0 : SpatialField) (conservativeForceT 0) (1 / 4) 1 reference
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact NSFormalization.Section3.T20.zero_mem_initialClassT
  · have hforce : conservativeForceT (0 : SpaceTime → ℝ) = 0 := by
      funext z
      simp [conservativeForceT, pressureGradient]
    rw [hforce]
    exact NSFormalization.Section3.T21.zero_mem_forceClassT
  · intro t ht
    exact packet.velocity_support t ⟨ht.1.le, ht.2⟩
  · simpa only [place, placementData] using
      (ball_subset_ball (show (1 / 4 : ℝ) ≤ 3 / 8 by norm_num) :
        ball (placementCenter : Space) (1 / 4) ⊆ ball placementCenter (3 / 8))

end Review493
