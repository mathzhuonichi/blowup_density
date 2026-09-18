import NSFormalization.Section3.T22.ZeroExtRegularity

noncomputable section

namespace NSFormalization.Section3.T22

open Set MeasureTheory Metric
open NavierStokes.ProblemStatement (Space)
open NSFormalization.Section4.A02 (SpatialField)
open NSFormalization.Section4.D01 (IsSobolevDatum)
open scoped ContDiff Topology

def probeΩ : Set Space := ball (0 : Space) 1

def probeK : Set Space := closedBall (0 : Space) (1 / 2 : ℝ)

def probeBump : ContDiffBump (0 : Space) :=
  ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

def probeχ : Space → ℝ := probeBump

def probez : SpatialField := fun x =>
  probeχ x • EuclideanSpace.basisFun (Fin 3) ℝ 0

theorem probeBump_nonzero : probeχ 0 ≠ 0 := by
  have hone : probeχ 0 = 1 := by
    apply probeBump.one_of_mem_closedBall
    simp [probeBump]
  rw [hone]
  norm_num

theorem probe_zeroExtension_nonzero : zeroExtension probeΩ probez 0 ≠ 0 := by
  have hmem : (0 : Space) ∈ probeΩ := by simp [probeΩ]
  rw [zeroExtension, indicator_of_mem hmem]
  exact smul_ne_zero probeBump_nonzero ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.ne_zero 0)

theorem probeΩ_open : IsOpen probeΩ := by
  exact isOpen_ball

theorem probeK_compact : IsCompact probeK := by
  exact isCompact_closedBall _ _

theorem probeK_subset_probeΩ : probeK ⊆ probeΩ := by
  intro x hx
  have hxnorm : ‖x‖ ≤ (1 / 2 : ℝ) := by
    simpa [probeK, mem_closedBall, dist_zero_right] using hx
  have hxlt : ‖x‖ < (1 : ℝ) := lt_of_le_of_lt hxnorm (by norm_num)
  simpa [probeΩ, mem_ball, dist_zero_right] using hxlt

theorem probez_smooth : ContDiff ℝ ∞ probez := by
  exact probeBump.contDiff.smul contDiff_const

theorem probez_support :
    tsupport (zeroExtension probeΩ probez) ⊆ probeK := by
  rw [tsupport]
  apply closure_minimal
  · intro x hx
    by_contra hxK
    apply hx
    by_cases hxΩ : x ∈ probeΩ
    · rw [zeroExtension, indicator_of_mem hxΩ]
      change probeχ x • EuclideanSpace.basisFun (Fin 3) ℝ 0 = 0
      have hxnorm : (1 / 2 : ℝ) < ‖x‖ := by
        have hnot : ¬ ‖x‖ ≤ (1 / 2 : ℝ) := by
          simpa [probeK, mem_closedBall, dist_zero_right] using hxK
        exact lt_of_not_ge hnot
      have hdist : probeBump.rOut ≤ dist x (0 : Space) := by
        simpa [probeBump, dist_zero_right] using (le_of_lt hxnorm)
      rw [show probeχ x = probeBump x by rfl, probeBump.zero_of_le_dist hdist]
      simp
    · simp [zeroExtension, hxΩ]
  · exact isClosed_closedBall

theorem probe_contDiff_zeroExtension :
    ContDiff ℝ ∞ (zeroExtension probeΩ probez) := by
  apply contDiff_zeroExtension probeΩ_open probez_smooth.contDiffOn
    probeK_compact probeK_subset_probeΩ probez_support

theorem probe_hasCompactSupport_zeroExtension :
    HasCompactSupport (zeroExtension probeΩ probez) := by
  exact hasCompactSupport_zeroExtension probeΩ_open probez_smooth.contDiffOn
    probeK_compact probeK_subset_probeΩ probez_support

theorem probe_smoothJets_zeroExtension :
    NSFormalization.Section4.D01.SmoothSquareIntegrableJets
      (zeroExtension probeΩ probez) := by
  exact smoothJets_zeroExtension probeΩ_open probez_smooth.contDiffOn
    probeK_compact probeK_subset_probeΩ probez_support

theorem probe_memLp_zeroExtension :
    MemLp (zeroExtension probeΩ probez) 2 volume := by
  exact memLp_zeroExtension probeΩ_open probez_smooth.contDiffOn
    probeK_compact probeK_subset_probeΩ probez_support

theorem probe_exists_datum_zeroExtension (s : ℝ) :
    ∃ A, IsSobolevDatum s (zeroExtension probeΩ probez) A := by
  exact exists_datum_zeroExtension probeΩ_open probez_smooth.contDiffOn
    probeK_compact probeK_subset_probeΩ probez_support s

end NSFormalization.Section3.T22
