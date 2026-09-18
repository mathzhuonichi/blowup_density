import NSFormalization.Section3.T22.ZeroExtensionComparison

/-!
# Probe for T22 U-Z1

The first example is the exact canonical-field type match.  The concrete
instance uses `Ω = ball 0 1`, `K = closedBall 0 (1/2)`, and a nonzero smooth
vector bump supported in `K`.
-/

noncomputable section

namespace T22ProbeUZ1

open Set MeasureTheory Metric
open NavierStokes.ProblemStatement
open NSFormalization.Paper3 (RealVectorSobolev)
open NSFormalization.Section3.T22
open NSFormalization.Section4.D01
open NSFormalization.Section4.A02 (SpatialField)
open scoped ContDiff ENNReal Topology

example : BoundedDomainNormAPI →
    (∀ (Ω K : Set Space), IsOpen Ω → IsCompact K → K ⊆ Ω →
      ∀ s : ℝ, ∃ C : ℝ, 0 < C ∧ ∀ z : SpatialField,
        ContDiffOn ℝ ∞ z Ω → tsupport (zeroExtension Ω z) ⊆ K →
        domainSobolevENorm Ω s (restrictField Ω z) ≤
            sobolevENorm s (zeroExtension Ω z) ∧
          sobolevENorm s (zeroExtension Ω z) ≤
            ENNReal.ofReal C * domainSobolevENorm Ω s (restrictField Ω z)) :=
  BoundedDomainNormAPI.zeroExtensionComparison

example : ∀ (Ω K : Set Space), IsOpen Ω → IsCompact K → K ⊆ Ω →
    ∀ s : ℝ, ∃ C : ℝ, 0 < C ∧ ∀ z : SpatialField,
      ContDiffOn ℝ ∞ z Ω → tsupport (zeroExtension Ω z) ⊆ K →
      domainSobolevENorm Ω s (restrictField Ω z) ≤
          sobolevENorm s (zeroExtension Ω z) ∧
        sobolevENorm s (zeroExtension Ω z) ≤
          ENNReal.ofReal C * domainSobolevENorm Ω s (restrictField Ω z) :=
  zeroExtensionComparison

def probeΩ : Set Space := ball (0 : Space) 1
def probeK : Set Space := closedBall (0 : Space) (1 / 2 : ℝ)

theorem probeΩ_open : IsOpen probeΩ := isOpen_ball

theorem probeK_compact : IsCompact probeK := isCompact_closedBall _ _

theorem probeK_subset_probeΩ : probeK ⊆ probeΩ := by
  intro x hx
  have hxnorm : ‖x‖ ≤ (1 / 2 : ℝ) := by
    simpa [probeK, mem_closedBall, dist_zero_right] using hx
  have hxlt : ‖x‖ < (1 : ℝ) := lt_of_le_of_lt hxnorm (by norm_num)
  simpa [probeΩ, mem_ball, dist_zero_right] using hxlt

def probeBump : ContDiffBump (0 : Space) :=
  ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

def probez : SpatialField := fun x =>
  probeBump x • coordinateVector 0

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
      change probeBump x • coordinateVector 0 = 0
      have hxnorm : (1 / 2 : ℝ) < ‖x‖ := by
        have hnot : ¬ ‖x‖ ≤ (1 / 2 : ℝ) := by
          simpa [probeK, mem_closedBall, dist_zero_right] using hxK
        exact lt_of_not_ge hnot
      have hdist : probeBump.rOut ≤ dist x (0 : Space) := by
        simpa [probeBump, dist_zero_right] using (le_of_lt hxnorm)
      rw [probeBump.zero_of_le_dist hdist]
      simp
    · simp [zeroExtension, hxΩ]
  · exact isClosed_closedBall

theorem probez_nonzero : probez 0 ≠ 0 := by
  rw [probez]
  have hzero : (0 : Space) ∈ closedBall (0 : Space) probeBump.rIn := by
    simp [probeBump]
  rw [probeBump.one_of_mem_closedBall hzero, one_smul]
  intro h
  have hi := congrArg (fun x : Space => x 0) h
  simp [coordinateVector] at hi

theorem concrete_nonzero_instance (s : ℝ) :
    ∃ C : ℝ, 0 < C ∧
      domainSobolevENorm probeΩ s (restrictField probeΩ probez) ≤
        sobolevENorm s (zeroExtension probeΩ probez) ∧
      sobolevENorm s (zeroExtension probeΩ probez) ≤
        ENNReal.ofReal C * domainSobolevENorm probeΩ s (restrictField probeΩ probez) ∧
      probez 0 ≠ 0 := by
  obtain ⟨C, hC, hbound⟩ :=
    zeroExtensionComparison probeΩ probeK probeΩ_open probeK_compact
      probeK_subset_probeΩ s
  obtain ⟨hleft, hright⟩ := hbound probez probez_smooth.contDiffOn probez_support
  exact ⟨C, hC, hleft, hright, probez_nonzero⟩

end T22ProbeUZ1
