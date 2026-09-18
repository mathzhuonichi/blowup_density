import NSFormalization.Section3.T11.DuhamelHalfStep

/-!
Probe for lane 330 (T11 U9d1c).  Every target of the brief is restated verbatim
here and shown to close from
`formalization/NSFormalization/Section3/T11/DuhamelHalfStep.lean`:

* the lane's theorem `TorusHalfStepInput` (the `Persistence.lean` statement,
  copied out in full below so that no re-indexing can hide behind the `def`);
* the two consumers of lane 319 (`persistence_halfOrder_ladder`,
  `torusForcedMildOn_persistence`) with the input discharged;
* non-vacuity: a nonzero, nonstationary, forced mild solution for which the
  conclusion produces a genuinely nonzero datum at every integer order.
-/

noncomputable section

namespace NSFormalization.Section3.T11.DuhamelHalfStepProbe

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T11
open scoped ContDiff ENNReal NNReal BigOperators

local instance halfStepProbeNormedGroup : NormedAddCommGroup (PeriodicSobolev 3) :=
  realPeriodicSubmodule.normedAddCommGroup

local instance halfStepProbeNormedSpace : NormedSpace ℝ (PeriodicSobolev 3) :=
  realPeriodicSubmodule.normedSpace

/-! ## 1. The lane's target, verbatim -/

/-- The statement of `TorusHalfStepInput` written out, with no reference to the
`def`.  It closes from the lane's theorem. -/
example :
    ∀ (ν : ℝ), 0 < ν → ∀ (C : TorusTwoSpaceContract ν)
      (a : SpatialField) (g : SpaceTimeField) (T : ℝ),
      a ∈ initialClassT → ContDiff ℝ ∞ g → IsPeriodicOn univ g → 0 < T →
      ∀ (A : PeriodicSobolev 3) (F P u : ℝ → PeriodicSobolev 3),
        IsPeriodicDatum 3 a A → IsPeriodicSobolevPath 3 g F →
        (∀ t : ℝ, 0 ≤ t → IsPeriodicLerayDatum (F t) (P t)) →
        TorusForcedMildOn C A P T u →
        ∀ r : ℝ, 3 ≤ r → ∀ v : ℝ → PeriodicSobolev r,
          ContinuousOn v (Ico 0 T) →
          (∀ t ∈ Ico 0 T, IsPeriodicReweight 3 r (u t) (v t)) →
          ∃ w : ℝ → PeriodicSobolev (r + 1 / 2),
            ContinuousOn w (Ico 0 T) ∧
            ∀ t ∈ Ico 0 T, IsPeriodicReweight r (r + 1 / 2) (v t) (w t) :=
  torusHalfStepInput

/-- The same, through the named `def`. -/
example : TorusHalfStepInput := torusHalfStepInput

/-! ## 2. The two consumers of lane 319, with the input discharged -/

example (ν : ℝ) (hν : 0 < ν) (C : TorusTwoSpaceContract ν)
    (a : SpatialField) (g : SpaceTimeField) (T : ℝ)
    (ha : a ∈ initialClassT) (hg : ContDiff ℝ ∞ g) (hp : IsPeriodicOn univ g)
    (hT : 0 < T) (A : PeriodicSobolev 3) (F P u : ℝ → PeriodicSobolev 3)
    (hA : IsPeriodicDatum 3 a A) (hF : IsPeriodicSobolevPath 3 g F)
    (hP : ∀ t : ℝ, 0 ≤ t → IsPeriodicLerayDatum (F t) (P t))
    (hu : TorusForcedMildOn C A P T u) (n : ℕ) :
    ∃ v : ℝ → PeriodicSobolev (3 + (n : ℝ) / 2),
      ContinuousOn v (Ico 0 T) ∧
      ∀ t ∈ Ico 0 T, IsPeriodicReweight 3 (3 + (n : ℝ) / 2) (u t) (v t) :=
  persistence_halfOrder_ladder torusHalfStepInput ν hν C a g T ha hg hp hT A F P u hA hF hP hu n

example (ν : ℝ) (hν : 0 < ν) (C : TorusTwoSpaceContract ν)
    (a : SpatialField) (g : SpaceTimeField) (T : ℝ)
    (ha : a ∈ initialClassT) (hg : ContDiff ℝ ∞ g) (hp : IsPeriodicOn univ g)
    (hT : 0 < T) (A : PeriodicSobolev 3) (F P u : ℝ → PeriodicSobolev 3)
    (hA : IsPeriodicDatum 3 a A) (hF : IsPeriodicSobolevPath 3 g F)
    (hP : ∀ t : ℝ, 0 ≤ t → IsPeriodicLerayDatum (F t) (P t))
    (hu : TorusForcedMildOn C A P T u) (m : ℕ) :
    ∃ u_m : ℝ → PeriodicSobolev m,
      (∀ t ∈ Ico 0 T, IsPeriodicReweight 3 (m : ℝ) (u t) (u_m t)) ∧
      ContinuousOn u_m (Ico 0 T) ∧
      (∀ K : Set ℝ, IsCompact K → K ⊆ Ico 0 T →
        ∃ B : ℝ, ∀ t ∈ K, ‖u_m t‖ ≤ B) :=
  torusForcedMildOn_persistence torusHalfStepInput ν hν C a g T ha hg hp hT A F P u
    hA hF hP hu m

/-! ## 3. The intermediate objects of the route also close -/

/-- The smooth force really does have a continuous Leray datum path at every
real order. -/
example (σ : ℝ) (g : SpaceTimeField) (hg : ContDiff ℝ ∞ g) (hp : IsPeriodicOn univ g)
    (F P : ℝ → PeriodicSobolev 3) (hF : IsPeriodicSobolevPath 3 g F)
    (hP : ∀ t : ℝ, 0 ≤ t → IsPeriodicLerayDatum (F t) (P t)) :
    ∃ Pσ : ℝ → PeriodicSobolev σ, Continuous Pσ ∧
      ∀ t : ℝ, 0 ≤ t → IsPeriodicReweight 3 σ (P t) (Pσ t) :=
  exists_continuous_lerayForcePath σ hg hp hF hP

/-- The fractional smoothing really is an endpoint-safe two-space contract from
`H^{r-1}` to `H^{r+1/2}`. -/
example (r : ℝ) (hr : 3 ≤ r) {ν : ℝ} (hν : 0 < ν) :
    MNS2.EndpointSafeTwoSpaceDuhamelContract ℝ
      (PeriodicSobolev (r + 1 / 2)) (PeriodicSobolev (r - 1)) :=
  torusFracContract r hr hν

/-- The Leray projector is bounded at every real order. -/
example (s : ℝ) : PeriodicSobolev s →L[ℝ] PeriodicSobolev s := torusLerayCLM s

/-! ## 4. Non-vacuity -/

/-- The constant-datum family of `Persistence.lean` satisfies every hypothesis,
so the unconditional persistence theorem has nonempty content. -/
example {ν : ℝ} (hν : 0 < ν) (C : TorusTwoSpaceContract ν) (c : Space) (m : ℕ) :
    ∃ u_m : ℝ → PeriodicSobolev m,
      (∀ t ∈ Ico (0 : ℝ) 1,
        IsPeriodicReweight 3 (m : ℝ) ((1 + t) • torusConstantDatum 3 c) (u_m t)) ∧
      ContinuousOn u_m (Ico (0 : ℝ) 1) ∧
      (∀ K : Set ℝ, IsCompact K → K ⊆ Ico (0 : ℝ) 1 →
        ∃ B : ℝ, ∀ t ∈ K, ‖u_m t‖ ≤ B) :=
  persistence_unconditional_constant hν C c m

/-- And the produced order-`m` datum is genuinely nonzero for a nonzero
constant: the zero mode carries `(1+t)c`, so nothing is being proved about the
zero solution. -/
theorem constant_persistence_nonzero {ν : ℝ} (hν : 0 < ν)
    (C : TorusTwoSpaceContract ν) (c : Space) (i : Fin 3) (hc : c i ≠ 0) (m : ℕ) :
    ∃ u_m : ℝ → PeriodicSobolev m,
      ContinuousOn u_m (Ico (0 : ℝ) 1) ∧ ∀ t ∈ Ico (0 : ℝ) 1, u_m t ≠ 0 := by
  obtain ⟨u_m, hrw, hcont, _⟩ := persistence_unconditional_constant hν C c m
  refine ⟨u_m, hcont, fun t ht hzero ↦ ?_⟩
  have h := hrw t ht i 0
  rw [hzero] at h
  have hw : periodicFrequencyWeight (0 : PeriodicFrequency) = 1 := by
    simp [periodicFrequencyWeight]
  have hval : ((1 + t) • torusConstantDatum 3 c).1 i 0 = ((1 + t : ℝ) : ℂ) * (c i : ℂ) := by
    change ((1 + t : ℝ) : ℂ) *
      (lp.single 2 (0 : PeriodicFrequency) ((c i : ℝ) : ℂ) : PeriodicScalarData) 0 = _
    simp
  rw [hval, hw, Real.one_rpow, one_smul] at h
  have hz : (0 : ℂ) = ((1 + t : ℝ) : ℂ) * (c i : ℂ) := by
    simpa using h
  have ht1 : (1 + t : ℝ) ≠ 0 := by
    have := ht.1
    positivity
  exact (mul_ne_zero (Complex.ofReal_ne_zero.mpr ht1)
    (Complex.ofReal_ne_zero.mpr hc)) hz.symm

/-! ## 5. Axiom conformance of the probe's own results -/

/-- info: 'NSFormalization.Section3.T11.DuhamelHalfStepProbe.constant_persistence_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NSFormalization.Section3.T11.DuhamelHalfStepProbe.constant_persistence_nonzero

/-- info: 'NSFormalization.Section3.T11.torusHalfStepInput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NSFormalization.Section3.T11.torusHalfStepInput

/-- info: 'NSFormalization.Section3.T11.persistence_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NSFormalization.Section3.T11.persistence_unconditional

end NSFormalization.Section3.T11.DuhamelHalfStepProbe
