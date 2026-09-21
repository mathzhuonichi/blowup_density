import NSFormalization.Section4.A01.LocalForce
import NSFormalization.Section4.A01.LocalTheoryBundle
import NSFormalization.Section4.A04.ShiftedExtension

/-! Whole-space local existence, maximal development and continuation for
locally smooth Sobolev forces, without global time-integrability assumptions.
-/
noncomputable section
namespace NSFormalization.Section4.A01
open Set MeasureTheory
open NavierStokes.ProblemStatement
open A02 A04
open scoped ContDiff ENNReal

/-- Reindex a classical solution by a force agreeing during its lifespan. -/
def withForceR {ν T : ℝ} {a : SpatialField} {f g : SpaceTimeField}
    (w : ClassicalSolutionR ν a g T)
    (hfg : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : Space, g (t, x) = f (t, x)) :
    ClassicalSolutionR ν a f T :=
  { w with momentum := fun t ht x => (w.momentum t ht x).trans (hfg t ht x) }

/-- A common smooth local solution for every locally smooth Sobolev force. -/
theorem exists_local_regular_of_smoothForceR
    (ν : ℝ) (hν : 0 < ν) (a : SpatialField) (ha : a ∈ initialClassR)
    (f : SpaceTimeField) (hf : SmoothForceR f) :
    ∃ T : ℝ, 0 < T ∧ ∃ v : ClassicalSolutionR ν a f T,
      ManuscriptLocalRegularity ν a f T v := by
  obtain ⟨g, hg, he⟩ := exists_memForceR_eqOn hf 1
  let w := (localCarrier ν a g hν ha hg).w
  let T := min (localHorizon' ν a g) 1
  have hT : 0 < T := lt_min w.horizon_pos zero_lt_one
  have heT : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space, g (t, x) = f (t, x) :=
    fun t ht x => he t ⟨ht.1, ht.2.le.trans (min_le_right _ _)⟩ x
  let v : ClassicalSolutionR ν a f T := withForceR (w.restrict hT (min_le_left _ _))
    (fun t ht x => heT t ⟨ht.1.le, ht.2⟩ x)
  have hr : ManuscriptLocalRegularity ν a g (localHorizon' ν a g) w :=
    (localCarrier ν a g hν ha hg).regularity
  have hsub : Ico (0 : ℝ) T ⊆ Ico 0 (localHorizon' ν a g) :=
    Ico_subset_Ico_right (min_le_left _ _)
  refine ⟨T, hT, v, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m
    obtain ⟨G, hp, hc⟩ := hr.sobolev_smooth m
    exact ⟨G, fun t ht => hp t (hsub ht), hc.mono hsub⟩
  · intro t ht
    have h := hr.pressure_recovery t (hsub ht)
    simpa only [v, withForceR, ClassicalSolutionR.restrict, heT t ht] using h
  · intro t ht x
    have h := hr.projected t ⟨ht.1, ht.2.trans_le (min_le_left _ _)⟩ x
    simpa only [v, withForceR, ClassicalSolutionR.restrict, heT t ⟨ht.1.le, ht.2⟩ x] using h
  · obtain ⟨c, hc⟩ := hr.pressure_potential
    exact ⟨c, fun t ht x => hc t (hsub ht) x⟩

/-- The underlying local solution on the same common horizon. -/
theorem exists_local_of_smoothForceR
    (ν : ℝ) (hν : 0 < ν) (a : SpatialField) (ha : a ∈ initialClassR)
    (f : SpaceTimeField) (hf : SmoothForceR f) :
    ∃ T : ℝ, 0 < T ∧ Nonempty (ClassicalSolutionR ν a f T) := by
  obtain ⟨T, hT, w, _⟩ := exists_local_regular_of_smoothForceR ν hν a ha f hf
  exact ⟨T, hT, ⟨w⟩⟩

/-- Maximal development only needs one actual local solution; the force
does not need to belong to a globally integrable class. -/
theorem exists_maximal_of_smoothForceR
    (ν : ℝ) (hν : 0 < ν) (a : SpatialField) (ha : a ∈ initialClassR)
    (f : SpaceTimeField) (hf : SmoothForceR f) :
    ∃ u p, IsMaximalSolution ν a f u p := by
  obtain ⟨T, _, ⟨w₀⟩⟩ := exists_local_of_smoothForceR ν hν a ha f hf
  have hpos : 0 < maximalLifespanR ν a f :=
    lt_of_lt_of_le (ENNReal.ofReal_pos.mpr w₀.horizon_pos) (horizon_le_lifespan w₀)
  refine ⟨uField ν a f, pField ν a f, hpos, ?_⟩
  intro S hS hSlt
  obtain ⟨S', hSS', hne'⟩ := exists_horizon_gt_of_lt_lifespan hS.le hSlt
  let w : ClassicalSolutionR ν a f S := hne'.some.restrict hS hSS'.le
  refine exists_eq_fields_of_agree (w.normalizePressure (0 : Space))
    (uField ν a f) (pField ν a f) ?_ ?_
  · intro t ht x
    exact uField_eq hν w ht x
  · intro t ht x
    exact pField_eq hν w ht x

/-- Localizing the force on a window larger than `S` transfers the existing
squared-`H²` continuation theorem without changing the solution below `S`. -/
theorem continuation_of_smoothForceR
    (ν : ℝ) (hν : 0 < ν) (a : SpatialField) (ha : a ∈ initialClassR)
    (f : SpaceTimeField) (hf : SmoothForceR f)
    (S : ℝ) (hS : 0 < S) (u : SpaceTimeField) (p : SpaceTimeScalar)
    (hu : SolvesBelow ν a f S u p) (hfin : squaredHTwoIntegral S u ≠ ⊤) :
    ENNReal.ofReal S < maximalLifespanR ν a f := by
  obtain ⟨g, hg, he⟩ := exists_memForceR_eqOn hf (S + 1)
  have hug : SolvesBelow ν a g S u p := by
    intro b hb hbS
    obtain ⟨w, hw, hp⟩ := hu b hb hbS
    refine ⟨withForceR w ?_, hw, hp⟩
    intro t ht x
    exact (he t ⟨ht.1.le, by linarith [ht.2]⟩ x).symm
  have hgLife := extendsBeyond_of_memForceR' ν a g hν ha hg S hS u p hug hfin
  obtain ⟨R, hSR, ⟨w⟩⟩ := exists_horizon_gt_of_lt_lifespan hS.le hgLife
  let L := min R (S + 1)
  have hSL : S < L := lt_min hSR (by linarith)
  have hL : 0 < L := hS.trans hSL
  let v : ClassicalSolutionR ν a f L :=
    withForceR (w.restrict hL (min_le_left _ _)) (fun t ht x =>
      he t ⟨ht.1.le, ht.2.le.trans (min_le_right _ _)⟩ x)
  exact (ENNReal.ofReal_lt_ofReal_iff hL).mpr hSL |>.trans_le (horizon_le_lifespan v)

/-- The continuation conclusion is realized by a genuine extension of the
original velocity, rather than just by a larger supremal lifespan. -/
theorem extends_of_smoothForceR
    (ν : ℝ) (hν : 0 < ν) (a : SpatialField) (ha : a ∈ initialClassR)
    (f : SpaceTimeField) (hf : SmoothForceR f)
    (S : ℝ) (hS : 0 < S) (u : SpaceTimeField) (p : SpaceTimeScalar)
    (hu : SolvesBelow ν a f S u p) (hfin : squaredHTwoIntegral S u ≠ ⊤) :
    ∃ R : ℝ, S < R ∧ ∃ w : ClassicalSolutionR ν a f R,
      ∀ t ∈ Ico (0 : ℝ) S, ∀ x : Space, w.velocity (t, x) = u (t, x) := by
  obtain ⟨R, hSR, ⟨w⟩⟩ := exists_horizon_gt_of_lt_lifespan hS.le
    (continuation_of_smoothForceR ν hν a ha f hf S hS u p hu hfin)
  refine ⟨R, hSR, w, ?_⟩
  intro t ht x
  obtain ⟨b, htb, hbS⟩ := exists_between ht.2
  obtain ⟨v, hv, _⟩ := hu b (ht.1.trans_lt htb) hbS
  have he := velocity_unique_core hν w v t ⟨ht.1, lt_min (ht.2.trans hSR) htb⟩ x
  simpa only [hv] using he

end NSFormalization.Section4.A01
