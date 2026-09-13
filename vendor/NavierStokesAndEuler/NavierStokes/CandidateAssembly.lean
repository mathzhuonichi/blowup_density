import NavierStokes.TimeLocalization
import NavierStokes.ResidualRegularity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Conditional outer assembly of the candidate fields

Given presingular fields and a smooth future force agreeing with their residual
only on `(3/4, 1)`, activate the fields and join their early residual to the
supplied force at `7/8`. The theorem proves all `CandidateProperties` for these
explicit outputs. It does not construct the input fields or the future force.
-/

namespace NavierStokes.CandidateAssembly

noncomputable section

open ProblemStatement TimeLocalization ResidualRegularity SmoothCutoffs Set Filter
open scoped ContDiff Topology

/-- The early force is the actual residual of the activated fields; after the
join it is the supplied future force. The two agree on an open overlap under
the late-agreement hypothesis used below. -/
def assembledForce (u : VelocityField) (p : PressureField) (F : VelocityField) :
    VelocityField := fun z =>
  if z.1 < (7 / 8 : ℝ) then
    navierStokesResidual (activatedVelocity u) (activatedPressure p) z.1 z.2
  else F z

theorem assembledForce_eq_early (u : VelocityField) (p : PressureField) (F : VelocityField)
    {t : ℝ} (ht : t < 7 / 8) (x : Space) :
    assembledForce u p F (t, x) =
      navierStokesResidual (activatedVelocity u) (activatedPressure p) t x := by
  simp only [assembledForce, ht, ite_eq_left]

theorem assembledForce_eq_after_join (u : VelocityField) (p : PressureField)
    (F : VelocityField) {t : ℝ} (ht : 7 / 8 ≤ t) (x : Space) :
    assembledForce u p F (t, x) = F (t, x) := by
  simp only [assembledForce, not_lt.mpr ht, ite_false]

/-- Late matching makes the piecewise force equal to `F` on the entire open
overlap, not merely at the join point. -/
theorem assembledForce_eq_late (u : VelocityField) (p : PressureField) (F : VelocityField)
    (hmatch : ∀ t ∈ Ioo (3 / 4 : ℝ) 1, ∀ x : Space,
      F (t, x) = navierStokesResidual u p t x)
    {t : ℝ} (ht : 3 / 4 < t) (x : Space) :
    assembledForce u p F (t, x) = F (t, x) := by
  by_cases hj : t < 7 / 8
  · rw [assembledForce_eq_early u p F hj x, activated_residual_eq_late u p ht x]
    exact (hmatch t ⟨ht, lt_trans hj (by norm_num)⟩ x).symm
  · exact assembledForce_eq_after_join u p F (le_of_not_gt hj) x

/-- Throughout the PDE interval, the constructed force is exactly the residual
of the activated fields. No early agreement condition on `F` is needed. -/
theorem assembledForce_eq_residual (u : VelocityField) (p : PressureField)
    (F : VelocityField)
    (hmatch : ∀ t ∈ Ioo (3 / 4 : ℝ) 1, ∀ x : Space,
      F (t, x) = navierStokesResidual u p t x)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (x : Space) :
    assembledForce u p F (t, x) =
      navierStokesResidual (activatedVelocity u) (activatedPressure p) t x := by
  by_cases hj : t < 7 / 8
  · exact assembledForce_eq_early u p F hj x
  · have hlate : 3 / 4 < t := by linarith
    calc
      _ = F (t, x) := assembledForce_eq_after_join u p F (le_of_not_gt hj) x
      _ = navierStokesResidual u p t x := hmatch t ⟨hlate, ht.2⟩ x
      _ = _ := (activated_residual_eq_late u p hlate x).symm

theorem assembledForce_eventuallyEq_early (u : VelocityField) (p : PressureField)
    (F : VelocityField) {z : SpaceTime} (hz : z.1 < 7 / 8) :
    assembledForce u p F =ᶠ[𝓝 z]
      (fun w => navierStokesResidual (activatedVelocity u) (activatedPressure p) w.1 w.2) := by
  have hU : {w : SpaceTime | w.1 < (7 / 8 : ℝ)} ∈ 𝓝 z :=
    (isOpen_lt continuous_fst continuous_const).mem_nhds hz
  filter_upwards [hU] with w hw
  exact assembledForce_eq_early u p F hw w.2

theorem assembledForce_eventuallyEq_late (u : VelocityField) (p : PressureField)
    (F : VelocityField)
    (hmatch : ∀ t ∈ Ioo (3 / 4 : ℝ) 1, ∀ x : Space,
      F (t, x) = navierStokesResidual u p t x)
    {z : SpaceTime} (hz : 3 / 4 < z.1) :
    assembledForce u p F =ᶠ[𝓝 z] F := by
  have hU : {w : SpaceTime | (3 / 4 : ℝ) < w.1} ∈ 𝓝 z :=
    (isOpen_lt continuous_const continuous_fst).mem_nhds hz
  filter_upwards [hU] with w hw
  exact assembledForce_eq_late u p F hmatch hw w.2

theorem activatedVelocity_eventually_zero (u : VelocityField) (x : Space) :
    activatedVelocity u =ᶠ[𝓝 (0, x)] (fun _ => 0) := by
  have hs : (fun z : SpaceTime => timeSwitch z.1) =ᶠ[𝓝 (0, x)] (fun _ => 0) :=
    timeSwitch_eventually_zero.comp_tendsto continuous_fst.continuousAt
  filter_upwards [hs] with z hz
  simp only [activatedVelocity, hz, zero_smul]

theorem activatedPressure_eventually_zero (p : PressureField) (x : Space) :
    activatedPressure p =ᶠ[𝓝 (0, x)] (fun _ => 0) := by
  have hs : (fun z : SpaceTime => timeSwitch z.1) =ᶠ[𝓝 (0, x)] (fun _ => 0) :=
    timeSwitch_eventually_zero.comp_tendsto continuous_fst.continuousAt
  filter_upwards [hs] with z hz
  simp only [activatedPressure, hz, zero_mul]

/-- The force has a zero germ at time zero even if the original fields have
arbitrary extensions to negative time. -/
theorem assembledForce_eventually_zero (u : VelocityField) (p : PressureField)
    (F : VelocityField) (x : Space) :
    assembledForce u p F =ᶠ[𝓝 (0, x)] (fun _ => 0) := by
  exact (assembledForce_eventuallyEq_early u p F (z := (0, x)) (by norm_num)).trans
    (residual_eventually_zero (activatedVelocity_eventually_zero u x)
      (activatedPressure_eventually_zero p x))

theorem assembledForce_zero_initial (u : VelocityField) (p : PressureField)
    (F : VelocityField) (x : Space) : assembledForce u p F (0, x) = 0 :=
  (assembledForce_eventually_zero u p F x).self_of_nhds

/-- Joint smoothness of the assembled force, including the relative boundary
at time zero and the join at `7/8`, follows from local exact equalities. -/
theorem assembledForce_smooth (u : VelocityField) (p : PressureField) (F : VelocityField)
    (hu : ContDiffOn ℝ ∞ u preSingularDomain)
    (hp : ContDiffOn ℝ ∞ p preSingularDomain)
    (hF : ContDiffOn ℝ ∞ F futureDomain)
    (hmatch : ∀ t ∈ Ioo (3 / 4 : ℝ) 1, ∀ x : Space,
      F (t, x) = navierStokesResidual u p t x) :
    ContDiffOn ℝ ∞ (assembledForce u p F) futureDomain := by
  intro z hz
  rcases z with ⟨t, x⟩
  by_cases hzero : t = 0
  · subst t
    have hconst : ContDiffAt ℝ ∞ (fun _ : SpaceTime => (0 : Space)) (0, x) :=
      contDiffAt_const
    exact (hconst.congr_of_eventuallyEq
      (assembledForce_eventually_zero u p F x)).contDiffWithinAt
  · have hpos : 0 < t := lt_of_le_of_ne hz.1 (Ne.symm hzero)
    by_cases hj : t < 7 / 8
    · have ht1 : t < 1 := lt_trans hj (by norm_num)
      have hres := contDiffOn_residual_interior
        (activatedVelocity_smooth u hu) (activatedPressure_smooth p hp)
      have hat : ContDiffAt ℝ ∞
          (fun w => navierStokesResidual (activatedVelocity u) (activatedPressure p) w.1 w.2)
          (t, x) :=
        hres.contDiffAt (prod_mem_nhds (Ioo_mem_nhds hpos ht1) Filter.univ_mem)
      exact (hat.congr_of_eventuallyEq
        (assembledForce_eventuallyEq_early u p F (z := (t, x)) hj)).contDiffWithinAt
    · have hlate : 3 / 4 < t := by linarith
      have heq := assembledForce_eventuallyEq_late u p F hmatch (z := (t, x)) hlate
      exact (hF (t, x) hz).congr_of_eventuallyEq
        (heq.filter_mono nhdsWithin_le_nhds) heq.self_of_nhds

theorem assembledForce_periodic (u : VelocityField) (p : PressureField)
    (F : VelocityField)
    (huper : UnitSpatialPeriodsOn (Ico (0 : ℝ) 1) u)
    (hpper : UnitSpatialPeriodsOn (Ico (0 : ℝ) 1) p)
    (hFper : UnitSpatialPeriodsOn (Ici (0 : ℝ)) F) :
    UnitSpatialPeriodsOn (Ici (0 : ℝ)) (assembledForce u p F) := by
  intro t ht x i
  by_cases hzero : t = 0
  · subst t
    rw [assembledForce_zero_initial, assembledForce_zero_initial]
  · have hpos : 0 < t := lt_of_le_of_ne ht (Ne.symm hzero)
    by_cases hj : t < 7 / 8
    · rw [assembledForce_eq_early u p F hj, assembledForce_eq_early u p F hj]
      exact residual_periods_interior
        (activatedVelocity_periodic u _ huper) (activatedPressure_periodic p _ hpper)
        t ⟨hpos, lt_trans hj (by norm_num)⟩ x i
    · rw [assembledForce_eq_after_join u p F (le_of_not_gt hj),
        assembledForce_eq_after_join u p F (le_of_not_gt hj)]
      exact hFper t ht x i

/-- The new early segment does not affect compact future time support. -/
theorem assembledForce_time_support (u : VelocityField) (p : PressureField)
    (F : VelocityField) (hF : CompactFutureTimeSupport F) :
    CompactFutureTimeSupport (assembledForce u p F) := by
  obtain ⟨T, hT, hzero⟩ := hF
  refine ⟨max T 1, hT.trans (le_max_left _ _), ?_⟩
  intro t ht x
  have hj : 7 / 8 ≤ t := (by norm_num : (7 / 8 : ℝ) ≤ 1).trans
    ((le_max_right T 1).trans ht)
  rw [assembledForce_eq_after_join u p F hj x]
  exact hzero t ((le_max_left T 1).trans ht) x

/-- Conditional outer assembly: the explicitly activated fields and joined
force satisfy every property in the candidate specification. Existence of
the incoming fields and the late-matching future force remains an input. -/
theorem assembled_candidate_properties
    (u : VelocityField) (p : PressureField) (F : VelocityField)
    (hu : ContDiffOn ℝ ∞ u preSingularDomain)
    (hp : ContDiffOn ℝ ∞ p preSingularDomain)
    (huper : UnitSpatialPeriodsOn (Ico (0 : ℝ) 1) u)
    (hpper : UnitSpatialPeriodsOn (Ico (0 : ℝ) 1) p)
    (hdiv : ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Space, spatialDivergence u t x = 0)
    (hunbounded : SpeedUnboundedAtOne u)
    (hF : ContDiffOn ℝ ∞ F futureDomain)
    (hFper : UnitSpatialPeriodsOn (Ici (0 : ℝ)) F)
    (hFsupport : CompactFutureTimeSupport F)
    (hmatch : ∀ t ∈ Ioo (3 / 4 : ℝ) 1, ∀ x : Space,
      F (t, x) = navierStokesResidual u p t x) :
    CandidateProperties (activatedVelocity u) (activatedPressure p) (assembledForce u p F) := by
  refine ⟨activatedVelocity_smooth u hu, activatedPressure_smooth p hp,
    assembledForce_smooth u p F hu hp hF hmatch,
    activatedVelocity_periodic u _ huper, activatedPressure_periodic p _ hpper,
    assembledForce_periodic u p F huper hpper hFper,
    activatedVelocity_zero_initial u, assembledForce_time_support u p F hFsupport,
    activatedVelocity_divergence_free u hu hdiv, ?_,
    activatedVelocity_speed_unbounded u hunbounded⟩
  intro t ht x
  exact (assembledForce_eq_residual u p F hmatch ht x).symm

/-- A conditional implication, not a proof that its analytic inputs exist. -/
theorem candidateStatement_of_late_force
    (u : VelocityField) (p : PressureField) (F : VelocityField)
    (hu : ContDiffOn ℝ ∞ u preSingularDomain)
    (hp : ContDiffOn ℝ ∞ p preSingularDomain)
    (huper : UnitSpatialPeriodsOn (Ico (0 : ℝ) 1) u)
    (hpper : UnitSpatialPeriodsOn (Ico (0 : ℝ) 1) p)
    (hdiv : ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Space, spatialDivergence u t x = 0)
    (hunbounded : SpeedUnboundedAtOne u)
    (hF : ContDiffOn ℝ ∞ F futureDomain)
    (hFper : UnitSpatialPeriodsOn (Ici (0 : ℝ)) F)
    (hFsupport : CompactFutureTimeSupport F)
    (hmatch : ∀ t ∈ Ioo (3 / 4 : ℝ) 1, ∀ x : Space,
      F (t, x) = navierStokesResidual u p t x) :
    candidateStatement :=
  ⟨activatedVelocity u, activatedPressure p, assembledForce u p F,
    assembled_candidate_properties u p F hu hp huper hpper hdiv hunbounded
      hF hFper hFsupport hmatch⟩

end

end NavierStokes.CandidateAssembly
