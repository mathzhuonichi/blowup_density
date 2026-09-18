import NSFormalization.Section3.T11.MildClassical

/-! # U9d2c probe: the U9d target closes

The first `example` is the U9d existential target copied **verbatim** from
`research/T11/EXISTENCE_ROUTE.md` (also reproduced in `REPORT_318.md` and
`REPORT_320.md`); it is closed by `mild_to_classical`, with no named input.
The following examples copy the two residual fields recorded by lanes 326/327
(`ClassicalSolutionT.velocity_smooth`, `ClassicalSolutionT.pressure_smooth`) and
the `PeriodicLocalRegularity.sobolev_smooth` clause, each in the exact shape of
`Section3/T10/PeriodicData.lean` / `Section3/T11/LocalTheory.lean`.

Non-vacuity is the affine constant-force family: a genuine nonzero forced mild
solution on an arbitrary positive horizon whose recovered classical velocity is
nonzero at the origin.
-/
noncomputable section
open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField SpaceTimeScalar)
open NSFormalization.Section3.T10 NSFormalization.Section3.T11
open scoped ContDiff BigOperators

local instance mildClassicalProbeNormedGroup (s : ℝ) :
    NormedAddCommGroup (PeriodicSobolev s) :=
  realPeriodicSubmodule.normedAddCommGroup
local instance mildClassicalProbeNormedSpace (s : ℝ) : NormedSpace ℝ (PeriodicSobolev s) :=
  realPeriodicSubmodule.normedSpace

/-! ## 1. The U9d target, verbatim -/

example :
    ∀ (ν : ℝ), 0 < ν → ∀ (C : TorusTwoSpaceContract ν)
      (a : SpatialField) (g : SpaceTimeField) (T : ℝ),
      a ∈ initialClassT → ContDiff ℝ ∞ g → IsPeriodicOn univ g → 0 < T →
      ∀ (A : PeriodicSobolev 3) (F P u : ℝ → PeriodicSobolev 3),
        IsPeriodicDatum 3 a A → IsPeriodicSobolevPath 3 g F →
        (∀ t : ℝ, 0 ≤ t → IsPeriodicLerayDatum (F t) (P t)) →
        TorusForcedMildOn C A P T u →
        ∃ w : ClassicalSolutionT ν a g T,
          PeriodicLocalRegularity ν a g T w ∧
          IsPeriodicSobolevPathOn 3 (Ico 0 T) w.velocity u :=
  fun ν hν C a g T ha hg hp hT A F P u hA hF hP hu ↦
    mild_to_classical ν hν C a g T ha hg hp hT A F P u hA hF hP hu

/-! ## 2. The two residual fields of lanes 326/327, verbatim -/

section Fields

variable {ν : ℝ} (hν : 0 < ν) (C : TorusTwoSpaceContract ν)
  {a : SpatialField} {g : SpaceTimeField} {T : ℝ}
  (ha : a ∈ initialClassT) (hg : ContDiff ℝ ∞ g) (hgp : IsPeriodicOn univ g) (hT : 0 < T)
  {A : PeriodicSobolev 3} {F P u : ℝ → PeriodicSobolev 3}
  (hA : IsPeriodicDatum 3 a A) (hF : IsPeriodicSobolevPath 3 g F)
  (hPL : ∀ t : ℝ, 0 ≤ t → IsPeriodicLerayDatum (F t) (P t))
  (hu : TorusForcedMildOn C A P T u)

/-- `ClassicalSolutionT.velocity_smooth`, verbatim. -/
example : ContDiffOn ℝ ∞ (torusPhysicalVelocity u) (Ico (0 : ℝ) T ×ˢ (univ : Set Space)) :=
  torusPhysicalVelocity_contDiffOn hν C ha hg hgp hT hA hF hPL hu
    (forcedLeray_continuousOn hg hgp hF hPL T)

/-- `ClassicalSolutionT.pressure_smooth`, verbatim. -/
example : ContDiffOn ℝ ∞ (mildPressure g u) (Ico (0 : ℝ) T ×ˢ (univ : Set Space)) :=
  mildPressure_contDiffOn hν C ha hg hgp hT hA hF hPL hu
    (forcedLeray_continuousOn hg hgp hF hPL T)

/-- `PeriodicLocalRegularity.sobolev_smooth`, verbatim. -/
example : ∀ m : ℕ, ∃ G : ℝ → PeriodicSobolev (m : ℝ),
    IsPeriodicSobolevPathOn (m : ℝ) (Ico (0 : ℝ) T) (torusPhysicalVelocity u) G ∧
      ContDiffOn ℝ ∞ G (Ico (0 : ℝ) T) := by
  intro m
  obtain ⟨v, hvre, _, _⟩ :=
    persistence_unconditional ν hν C a g T ha hg hgp hT A F P u hA hF hPL hu m
  exact ⟨v, torusPhysicalVelocity_reweight hvre,
    mildTower_contDiffOn hν C ha hg hgp hT hA hF hPL hu
      (forcedLeray_continuousOn hg hgp hF hPL T) m v hvre⟩

end Fields

/-! ## 3. The corollary in the shape lane 321's restart consumes -/

example (ν : ℝ) (hν : 0 < ν) (a : SpatialField) (ha : a ∈ initialClassT)
    (g : SpaceTimeField) (hg : ContDiff ℝ ∞ g) (hgp : IsPeriodicOn univ g) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ w : ClassicalSolutionT ν a g δ,
      PeriodicLocalRegularity ν a g δ w :=
  exists_classical_of_picard ν hν a ha g hg hgp

/-! ## 4. Non-vacuity: the affine constant-force family -/

theorem mildClassical_probe_nonzero :
    ∃ (C : TorusTwoSpaceContract 1) (w : ClassicalSolutionT 1
        (fun _ ↦ coordinateVector 0) (fun _ : SpaceTime ↦ coordinateVector 0) 1),
      PeriodicLocalRegularity 1 (fun _ ↦ coordinateVector 0)
          (fun _ : SpaceTime ↦ coordinateVector 0) 1 w ∧
        IsPeriodicSobolevPathOn 3 (Ico 0 1) w.velocity
          (fun t ↦ (1 + t) • torusConstantDatum 3 (coordinateVector 0)) ∧
        w.velocity (0, 0) ≠ 0 ∧
        TorusForcedMildOn C (torusConstantDatum 3 (coordinateVector 0))
          (fun _ ↦ torusConstantDatum 3 (coordinateVector 0)) 1
          (fun t ↦ (1 + t) • torusConstantDatum 3 (coordinateVector 0)) := by
  obtain ⟨C⟩ := torusTwoSpaceContract_nonempty' 1 one_pos
  obtain ⟨w, hreg, hpath, hinit⟩ :=
    mild_to_classical_affine_constant one_pos C 1 one_pos (coordinateVector 0)
  refine ⟨C, w, hreg, hpath, ?_, torusForcedMildOn_affine_constant C _ zero_le_one⟩
  rw [hinit 0]
  intro h
  have hc := congrArg (fun v : Space ↦ v 0) h
  norm_num [coordinateVector] at hc

example : ∃ (C : TorusTwoSpaceContract 1) (w : ClassicalSolutionT 1
      (fun _ ↦ coordinateVector 0) (fun _ : SpaceTime ↦ coordinateVector 0) 1),
    PeriodicLocalRegularity 1 (fun _ ↦ coordinateVector 0)
        (fun _ : SpaceTime ↦ coordinateVector 0) 1 w ∧
      IsPeriodicSobolevPathOn 3 (Ico 0 1) w.velocity
        (fun t ↦ (1 + t) • torusConstantDatum 3 (coordinateVector 0)) ∧
      w.velocity (0, 0) ≠ 0 ∧
      TorusForcedMildOn C (torusConstantDatum 3 (coordinateVector 0))
        (fun _ ↦ torusConstantDatum 3 (coordinateVector 0)) 1
        (fun t ↦ (1 + t) • torusConstantDatum 3 (coordinateVector 0)) :=
  mildClassical_probe_nonzero

/-! ## 5. Axiom guards for the two headline theorems -/

/-- info: 'NSFormalization.Section3.T11.mild_to_classical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NSFormalization.Section3.T11.mild_to_classical

/-- info: 'NSFormalization.Section3.T11.exists_classical_of_picard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NSFormalization.Section3.T11.exists_classical_of_picard

/-- info: 'mildClassical_probe_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mildClassical_probe_nonzero
