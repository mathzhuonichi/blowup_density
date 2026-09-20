import NSFormalization.Section3.T23.DomainComparison
import NSFormalization.Section3.T22.Assembly

/-!
# Reviewer probe for lane 484

The first example witnesses that the API's `eps_pos` field makes the scale
interval nonempty.  The second example is used as a negative mutation: it
reverses the first comparison inequality while leaving all hypotheses and the
second inequality unchanged.
-/

noncomputable section

namespace NSFormalization.Section3.T23.Rev484

open Set MeasureTheory
open NavierStokes.ProblemStatement (Space)
open NSFormalization.Section4.A02 (SpaceTimeField)
open NSFormalization.Section3.T22
open scoped ContDiff ENNReal

example {ε₀ : ℝ} (hε₀ : 0 < ε₀) : (Ioc (0 : ℝ) ε₀).Nonempty := by
  exact ⟨ε₀, hε₀, le_rfl⟩

theorem zero_mem_forceClassOmega (Ω : Set Space) :
    (0 : SpaceTimeField) ∈ forceClassOmega Ω := by
  constructor
  · intro T'
    refine ⟨univ, isOpen_univ, subset_univ _, ?_⟩
    exact contDiff_const.contDiffOn
  · refine ⟨∅, isCompact_empty, empty_subset _, ?_⟩
    simp [tsupport]

def reviewTimeBump : ContDiffBump (1 : ℝ) :=
  ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

def reviewForce : SpaceTimeField :=
  fun z ↦ reviewTimeBump z.1 • nonvacuityField z.2

theorem reviewForce_contDiff : ContDiff ℝ ∞ reviewForce := by
  exact (reviewTimeBump.contDiff.comp contDiff_fst).smul
    (nonvacuityField_contDiff.comp contDiff_snd)

theorem reviewForce_mem : reviewForce ∈ forceClassOmega nonvacuityΩ := by
  constructor
  · intro T'
    exact ⟨univ, isOpen_univ, subset_univ _, reviewForce_contDiff.contDiffOn⟩
  · refine ⟨Metric.closedBall (1 : ℝ) reviewTimeBump.rOut,
        isCompact_closedBall _ _, ?_, ?_⟩
    · intro t ht
      rw [Metric.mem_closedBall, Real.dist_eq] at ht
      have hlo := neg_le_of_abs_le ht
      change (0 : ℝ) < t
      dsimp [reviewTimeBump] at hlo
      linarith
    · apply closure_minimal _ (Metric.isClosed_closedBall.prod isClosed_univ)
      intro z hz
      have htime : reviewTimeBump z.1 ≠ 0 := by
        intro hzero
        apply hz
        simp [reviewForce, hzero]
      have htime' := subset_tsupport (reviewTimeBump : ℝ → ℝ)
        (Function.mem_support.mpr htime)
      rw [reviewTimeBump.tsupport_eq] at htime'
      exact ⟨htime', mem_univ _⟩

theorem reviewForce_ne_zero : reviewForce (1, (0 : Space)) ≠ 0 := by
  have ht : (1 : ℝ) ∈ Metric.closedBall (1 : ℝ) reviewTimeBump.rIn := by
    simp [reviewTimeBump]
  rw [reviewForce, reviewTimeBump.one_of_mem_closedBall ht, one_smul]
  exact nonvacuityField_ne_zero

/-! A concrete, nonempty-scale instance of the main theorem's hypotheses:
the fixed closed half-ball lies inside the open unit ball and the force
difference is the nonzero smooth, positive-time-compact `reviewForce`. -/
example :
    ∀ s : ℝ, ∃ C : ℝ, 0 < C ∧ ∀ ε ∈ Ioc (0 : ℝ) 1,
      domainForceSobolevENorm nonvacuityΩ s
          (fun z ↦ reviewForce z - (0 : SpaceTimeField) z) ≤
        zeroExtForceSobolevENorm nonvacuityΩ s
          (fun z ↦ reviewForce z - (0 : SpaceTimeField) z) ∧
      zeroExtForceSobolevENorm nonvacuityΩ s
          (fun z ↦ reviewForce z - (0 : SpaceTimeField) z) ≤
        ENNReal.ofReal C * domainForceSobolevENorm nonvacuityΩ s
          (fun z ↦ reviewForce z - (0 : SpaceTimeField) z) := by
  apply domain_zeroExt_comparison (Ω := nonvacuityΩ) boundedDomainNorm
      nonvacuityΩ_open (by norm_num : (0 : ℝ) < 1 / 2)
  · rw [closure_ball (0 : Space) (by norm_num : (1 / 2 : ℝ) ≠ 0)]
    exact nonvacuityK_subset_Ω
  · intro ε hε
    have heq :
        (fun z ↦ reviewForce z - (0 : SpaceTimeField) z) = reviewForce := by
      funext z
      simp
    rw [heq]
    exact reviewForce_mem
  · intro ε hε t x hx
    rw [closure_ball (0 : Space) (by norm_num : (1 / 2 : ℝ) ≠ 0)]
    have hfield : nonvacuityField x ≠ 0 := by
      intro hzero
      apply hx
      simp [reviewForce, hzero]
    have hbump : nonvacuityBump x ≠ 0 := by
      intro hzero
      apply hfield
      simp [nonvacuityField, hzero]
    have hx' := subset_tsupport (nonvacuityBump : Space → ℝ)
      (Function.mem_support.mpr hbump)
    rw [nonvacuityBump.tsupport_eq] at hx'
    simpa [nonvacuityBump] using hx'

variable {Ω : Set Space} {ε₀ : ℝ}
  {force : ℝ → SpaceTimeField} {g : SpaceTimeField}
  {c : Space} {R : ℝ}

set_option linter.unusedVariables false in
example (norms : BoundedDomainNormAPI)
    (hΩ : IsOpen Ω) (hR : 0 < R)
    (hball : closure (Metric.ball c R) ⊆ Ω)
    (hforce : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      (fun z ↦ force ε z - g z) ∈ forceClassOmega Ω)
    (hsupport : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      ∀ t : ℝ, ∀ x : Space, force ε (t, x) - g (t, x) ≠ 0 →
        x ∈ closure (Metric.ball c R)) : True := by
  fail_if_success
    have _hmutated :
        ∀ s : ℝ, ∃ C : ℝ, 0 < C ∧ ∀ ε ∈ Ioc (0 : ℝ) ε₀,
          zeroExtForceSobolevENorm Ω s (fun z ↦ force ε z - g z) ≤
              domainForceSobolevENorm Ω s (fun z ↦ force ε z - g z) ∧
          zeroExtForceSobolevENorm Ω s (fun z ↦ force ε z - g z) ≤
              ENNReal.ofReal C *
                domainForceSobolevENorm Ω s (fun z ↦ force ε z - g z) :=
      domain_zeroExt_comparison norms hΩ hR hball hforce hsupport
  exact True.intro

end NSFormalization.Section3.T23.Rev484
