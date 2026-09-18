import NSFormalization.Section3.T11.Persistence
import NSFormalization.Section3.T11.ConvolutionBound

noncomputable section
namespace NSFormalization.Section3.T11.PersistenceProbe
open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T11
open scoped ContDiff ENNReal NNReal BigOperators

local instance persistenceProbeNormedGroup : NormedAddCommGroup (PeriodicSobolev 3) :=
  realPeriodicSubmodule.normedAddCommGroup
local instance persistenceProbeNormedSpace : NormedSpace ℝ (PeriodicSobolev 3) :=
  realPeriodicSubmodule.normedSpace

-- The physical-coefficient statement; exactly one residual input.
example (H : TorusHalfStepInput)
    (ν : ℝ) (hν : 0 < ν) (C : TorusTwoSpaceContract ν)
    (a : SpatialField) (g : SpaceTimeField) (T : ℝ)
    (ha : a ∈ initialClassT) (hg : ContDiff ℝ ∞ g) (hp : IsPeriodicOn univ g)
    (hT : 0 < T) (A : PeriodicSobolev 3) (F P u : ℝ → PeriodicSobolev 3)
    (hA : IsPeriodicDatum 3 a A) (hF : IsPeriodicSobolevPath 3 g F)
    (hP : ∀ t : ℝ, 0 ≤ t → IsPeriodicLerayDatum (F t) (P t))
    (hu : TorusForcedMildOn C A P T u) :
    ∀ m : ℕ, ∃ u_m : ℝ → PeriodicSobolev m,
      (∀ t ∈ Ico 0 T, IsPeriodicReweight 3 (m : ℝ) (u t) (u_m t)) ∧
      ContinuousOn u_m (Ico 0 T) ∧
      (∀ K : Set ℝ, IsCompact K → K ⊆ Ico 0 T →
        ∃ B : ℝ, ∀ t ∈ K, ‖u_m t‖ ≤ B) := by
  exact torusForcedMildOn_persistence H ν hν C a g T ha hg hp hT A F P u hA hF hP hu

-- The brief's literal conclusion, with all its premises. This is diagnostic,
-- NOT a proof of the sobolev_smooth field in api_on_canonical.lean.
example (ν : ℝ) (_hν : 0 < ν) (C : TorusTwoSpaceContract ν)
    (a : SpatialField) (g : SpaceTimeField) (T : ℝ)
    (_ha : a ∈ initialClassT) (_hg : ContDiff ℝ ∞ g) (_hp : IsPeriodicOn univ g)
    (_hT : 0 < T) (A : PeriodicSobolev 3) (F P u : ℝ → PeriodicSobolev 3)
    (_hA : IsPeriodicDatum 3 a A) (_hF : IsPeriodicSobolevPath 3 g F)
    (_hP : ∀ t : ℝ, 0 ≤ t → IsPeriodicLerayDatum (F t) (P t))
    (hu : TorusForcedMildOn C A P T u) :
    ∀ m : ℕ, ∃ u_m : ℝ → PeriodicSobolev m,
      (∀ t ∈ Ico 0 T, ∀ i k, (u_m t).1 i k = (u t).1 i k) ∧
      ContinuousOn u_m (Ico 0 T) ∧
      (∀ K : Set ℝ, IsCompact K → K ⊆ Ico 0 T →
        ∃ B : ℝ, ∀ t ∈ K, ‖u_m t‖ ≤ B) :=
  persistence_literal_target C A P u hu

-- Non-vacuity: an inhabited contract, nonzero force, nonzero initial solution,
-- and every half-order gain on the same interval for u(t)=(1+t)e₁.
example : ∃ C : TorusTwoSpaceContract 1,
    let A := torusConstantDatum 3 (coordinateVector 0)
    A ≠ 0 ∧
    TorusForcedMildOn C A (fun _ ↦ A) 1 (fun t ↦ (1+t) • A) ∧
    (∀ r : ℝ, ∃ w : ℝ → PeriodicSobolev (r+1/2),
      ContinuousOn w (Ico 0 1) ∧
      ∀ t ∈ Ico (0 : ℝ) 1,
        IsPeriodicReweight r (r+1/2)
          ((1+t) • torusConstantDatum r (coordinateVector 0)) (w t)) := by
  obtain ⟨C⟩ := torusTwoSpaceContract_nonempty' 1 (by norm_num)
  refine ⟨C, ?_, persistence_constant_mild C (by norm_num) _, ?_⟩
  · intro h
    have hc := congrArg (fun A : PeriodicSobolev 3 ↦ A.1 0 (0 : PeriodicFrequency)) h
    norm_num [torusConstantDatum, coordinateVector] at hc
  · intro r
    refine ⟨fun t ↦ (1+t) • torusConstantDatum (r+1/2) (coordinateVector 0),
      ((continuous_const.add continuous_id).smul continuous_const).continuousOn, ?_⟩
    intro t ht
    exact persistence_constant_reweight r (r+1/2) (1+t) _

end NSFormalization.Section3.T11.PersistenceProbe
