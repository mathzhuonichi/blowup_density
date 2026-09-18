import NSFormalization.Section3.T11.LocalExistence
import NSFormalization.Section3.T11.CriterionBridge
import NSFormalization.Section3.T10.ForcePaths
import Mathlib.MeasureTheory.Group.LIntegral

/-!
# Uniform periodic restart and the selected local solution

The amended quantitative local-existence input accepts a separate finite
forcing bound at every integer Sobolev order.  Positive time translation only
discards an initial part of the half-line integral, so the unshifted force
norms provide one order-wise family of bounds for an entire compact restart
window.  Specializing the resulting restart theorem at time zero supplies the
first three fields of the periodic local-theory API.
-/

noncomputable section

namespace NSFormalization.Section3.T11

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField forceTimeMeasure)
open NSFormalization.Section3.T10
open scoped ContDiff ENNReal

/-- Positive time translation can only decrease the periodic `L¹_t H^s_x`
extended norm.  This is the torus-data analogue of
`Section4.A04.forceSobolevENormL1_timeShift_le`. -/
theorem forceSobolevENormT_timeShift_le (s : ℝ) (f : SpaceTimeField)
    (t₀ : ℝ) (ht₀ : 0 ≤ t₀) :
    forceSobolevENormT 1 s (timeShiftT t₀ f) ≤ forceSobolevENormT 1 s f := by
  apply le_iInf
  rintro ⟨G, hpath, hmeas⟩
  let Gshift : ℝ → PeriodicSobolev s := fun t ↦ G (t + t₀)
  have hshiftpath : IsPeriodicSobolevPath s (timeShiftT t₀ f) Gshift := by
    intro t ht
    exact hpath (t + t₀) (by linarith)
  have hq : Measure.QuasiMeasurePreserving (fun t : ℝ ↦ t + t₀)
      forceTimeMeasure forceTimeMeasure := by
    apply (measurePreserving_add_right (volume : Measure ℝ) t₀).quasiMeasurePreserving.restrict
    intro t ht
    show 0 < t + t₀
    have ht' : 0 < t := ht
    linarith
  have hshiftmeas : AEStronglyMeasurable Gshift forceTimeMeasure :=
    hmeas.comp_quasiMeasurePreserving hq
  refine (iInf_le _ ⟨Gshift, hshiftpath, hshiftmeas⟩).trans ?_
  show eLpNorm Gshift 1 forceTimeMeasure ≤ eLpNorm G 1 forceTimeMeasure
  rw [eLpNorm_one_eq_lintegral_enorm, eLpNorm_one_eq_lintegral_enorm]
  exact NSFormalization.Section4.A04.lintegral_enorm_shift_le G ht₀

/-- Time translation preserves the global smoothness required by the amended
local-existence input. -/
theorem timeShiftT_contDiff {f : SpaceTimeField} (hf : ContDiff ℝ ∞ f) (t₀ : ℝ) :
    ContDiff ℝ ∞ (timeShiftT t₀ f) := by
  exact hf.comp ((contDiff_fst.add contDiff_const).prodMk contDiff_snd)

/-- Time translation preserves unit spatial periods. -/
theorem timeShiftT_periodic {f : SpaceTimeField} (hf : IsPeriodicOn univ f) (t₀ : ℝ) :
    IsPeriodicOn univ (timeShiftT t₀ f) := by
  intro t _ht x i
  exact hf (t + t₀) (mem_univ _) x i

/-- Translation by zero is literally the original spacetime field. -/
theorem timeShiftT_zero (f : SpaceTimeField) : timeShiftT 0 f = f := by
  funext z
  simp [timeShiftT, NSFormalization.Section4.A04.timeShift]

/-- The `PeriodicContinuationAPI.restart` field, verbatim, conditional only on
the named amended quantitative local-existence input. -/
theorem restart (H : PeriodicQuantitativeLocalInput') :
    ∀ (ν : ℝ), 0 < ν →
    ∀ (f : SpaceTimeField), f ∈ forceClassT →
      ∀ (S : ℝ), 0 ≤ S → ∀ (K : ℝ≥0∞), K ≠ ⊤ →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ t₀ ∈ Icc (0 : ℝ) S,
            ∀ (a' : SpatialField), a' ∈ initialClassT →
              periodicSobolevENorm 1 a' ≤ K →
                ∃ w : ClassicalSolutionT ν a' (timeShiftT t₀ f) δ,
                  PeriodicLocalRegularity ν a' (timeShiftT t₀ f) δ w := by
  intro ν hν f hf S _hS K hK
  let M : ℕ → ℝ≥0∞ := fun m ↦ forceSobolevENormT 1 (m : ℝ) f
  have hM : ∀ m, M m ≠ ⊤ := by
    intro m
    exact forceSobolevENormT_ne_top hf m 1
  obtain ⟨δ, hδ, hlocal⟩ := H ν hν K hK M hM
  refine ⟨δ, hδ, ?_⟩
  intro t₀ ht₀ a' ha' hKa'
  apply hlocal a' ha' hKa' (timeShiftT t₀ f)
  · exact timeShiftT_contDiff hf.1 t₀
  · exact timeShiftT_periodic hf.2.1 t₀
  · intro m
    exact forceSobolevENormT_timeShift_le (m : ℝ) f t₀ ht₀.1

/-- At admissible parameters the named input produces a positive horizon, a
classical solution, and all three local-regularity clauses. -/
theorem exists_periodicLocalSolution_of_input (H : PeriodicQuantitativeLocalInput') :
    ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∃ δ : ℝ, 0 < δ ∧ ∃ w : ClassicalSolutionT ν a f δ,
          PeriodicLocalRegularity ν a f δ w := by
  intro ν hν a ha f hf
  have hK : periodicSobolevENorm 1 a ≠ ⊤ :=
    periodicSobolevENorm_ne_top_smooth 1 ha.1 ha.2.1
  obtain ⟨δ, hδ, hlocal⟩ := restart H ν hν f hf 0 le_rfl
    (periodicSobolevENorm 1 a) hK
  obtain ⟨w, hw⟩ := hlocal 0 (by simp) a ha le_rfl
  have hex : ∃ w : ClassicalSolutionT ν a (timeShiftT 0 f) δ,
      PeriodicLocalRegularity ν a (timeShiftT 0 f) δ w := ⟨w, hw⟩
  rw [timeShiftT_zero] at hex
  exact ⟨δ, hδ, hex⟩

/-- The solution and its regularity are selected together, so dependent
transport to the public horizon cannot separate the witness from its proof. -/
noncomputable def periodicLocalChoice (H : PeriodicQuantitativeLocalInput')
    (ν : ℝ) (hν : 0 < ν)
    (a : SpatialField) (ha : a ∈ initialClassT)
    (f : SpaceTimeField) (hf : f ∈ forceClassT) :
    Σ δ : ℝ, {w : ClassicalSolutionT ν a f δ //
      PeriodicLocalRegularity ν a f δ w} := by
  let hex := exists_periodicLocalSolution_of_input H ν hν a ha f hf
  let δ := Classical.choose hex
  let hδ := Classical.choose_spec hex
  exact ⟨δ, Classical.choose hδ.2, Classical.choose_spec hδ.2⟩

/-- The selected horizon.  Its value is `1` away from the admissible input
class, exactly as prescribed by the split; those values are never consumed by
the dependent solution field. -/
noncomputable def periodicLocalHorizonOfInput (H : PeriodicQuantitativeLocalInput')
    (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) : ℝ := by
  classical
  exact if h : 0 < ν ∧ a ∈ initialClassT ∧ f ∈ forceClassT then
      (periodicLocalChoice H ν h.1 a h.2.1 f h.2.2).1
    else 1

theorem periodicLocalHorizonOfInput_eq (H : PeriodicQuantitativeLocalInput')
    {ν : ℝ} (hν : 0 < ν) {a : SpatialField} (ha : a ∈ initialClassT)
    {f : SpaceTimeField} (hf : f ∈ forceClassT) :
    periodicLocalHorizonOfInput H ν a f =
      (periodicLocalChoice H ν hν a ha f hf).1 := by
  classical
  unfold periodicLocalHorizonOfInput
  split
  · rfl
  · rename_i h
    exact False.elim (h ⟨hν, ha, hf⟩)

/-- The jointly selected solution/regularity bundle, transported to the public
horizon. -/
noncomputable def periodicLocalBundleOfInput (H : PeriodicQuantitativeLocalInput')
    (ν : ℝ) (hν : 0 < ν)
    (a : SpatialField) (ha : a ∈ initialClassT)
    (f : SpaceTimeField) (hf : f ∈ forceClassT) :
    {w : ClassicalSolutionT ν a f (periodicLocalHorizonOfInput H ν a f) //
      PeriodicLocalRegularity ν a f (periodicLocalHorizonOfInput H ν a f) w} := by
  rw [periodicLocalHorizonOfInput_eq H hν ha hf]
  exact (periodicLocalChoice H ν hν a ha f hf).2

/-- The selected classical solution on `periodicLocalHorizonOfInput`. -/
noncomputable def periodicLocalSolutionOfInput (H : PeriodicQuantitativeLocalInput')
    (ν : ℝ) (hν : 0 < ν)
    (a : SpatialField) (ha : a ∈ initialClassT)
    (f : SpaceTimeField) (hf : f ∈ forceClassT) :
    ClassicalSolutionT ν a f (periodicLocalHorizonOfInput H ν a f) :=
  (periodicLocalBundleOfInput H ν hν a ha f hf).1

/-- Regularity of the selected classical solution on the same selected
horizon. -/
theorem periodicLocalRegularityOfInput (H : PeriodicQuantitativeLocalInput')
    (ν : ℝ) (hν : 0 < ν)
    (a : SpatialField) (ha : a ∈ initialClassT)
    (f : SpaceTimeField) (hf : f ∈ forceClassT) :
    PeriodicLocalRegularity ν a f (periodicLocalHorizonOfInput H ν a f)
      (periodicLocalSolutionOfInput H ν hν a ha f hf) := by
  exact (periodicLocalBundleOfInput H ν hν a ha f hf).2

/-- The first three, existence-side fields of `PeriodicLocalTheoryAPI`.  The
five uniqueness/maximality fields are supplied by U5/U15/U16 before the final
API assembly. -/
structure PeriodicLocalTheoryInitialAPI : Type where
  horizon : ℝ → SpatialField → SpaceTimeField → ℝ
  solution : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ClassicalSolutionT ν a f (horizon ν a f)
  regularity : ∀ (ν : ℝ) (hν : 0 < ν)
    (a : SpatialField) (ha : a ∈ initialClassT)
    (f : SpaceTimeField) (hf : f ∈ forceClassT),
      PeriodicLocalRegularity ν a f (horizon ν a f)
        (solution ν hν a ha f hf)

/-- Partial local-theory assembly from the one allowed named input. -/
noncomputable def periodicLocalTheoryAPI_of_input
    (H : PeriodicQuantitativeLocalInput') : PeriodicLocalTheoryInitialAPI where
  horizon := periodicLocalHorizonOfInput H
  solution := periodicLocalSolutionOfInput H
  regularity := periodicLocalRegularityOfInput H

/-- The named input's conclusion is non-vacuous: it is inhabited by a
nonzero solution driven by a nonzero smooth periodic force. -/
example :
    ∃ (K : ℝ≥0∞) (M : ℕ → ℝ≥0∞) (a : SpatialField) (g : SpaceTimeField),
      K ≠ ⊤ ∧ (∀ m, M m ≠ ⊤) ∧ a ∈ initialClassT ∧
      periodicSobolevENorm 1 a ≤ K ∧ ContDiff ℝ ∞ g ∧ IsPeriodicOn univ g ∧
      (∀ m : ℕ, forceSobolevENormT 1 (m : ℝ) g ≤ M m) ∧
      ∃ w : ClassicalSolutionT 1 a g 1,
        PeriodicLocalRegularity 1 a g 1 w ∧
        w.velocity (0, 0) ≠ 0 ∧ g (0, 0) ≠ 0 :=
  nonzero_forced_witness'

end NSFormalization.Section3.T11
