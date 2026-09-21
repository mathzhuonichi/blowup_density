import NSFormalization.Section3.T11.LocalForceRestart

/-! Periodic local theory for smooth periodic forcing, without temporal
support or global time-integrability assumptions. -/
noncomputable section
namespace NSFormalization.Section3.T11
open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField SpaceTimeScalar)
open NSFormalization.Section3.T10
open NSFormalization.Paper1
open NSFormalization.Paper1.PeriodicLifespan
open NSFormalization.Paper1.PeriodicLocalLifespan
open NSFormalization.Paper1.PeriodicPressureNormalization
open scoped ContDiff ENNReal

/-- Smooth periodic forcing on each finite closed future slab, represented
by restrictions of smooth periodic fields. No condition is imposed on the
original field at negative times or on its behavior as time tends to infinity. -/
def SmoothForceT (f : SpaceTimeField) : Prop :=
  ∀ S : ℝ, 0 < S → ∃ g : SpaceTimeField,
    ContDiff ℝ ∞ g ∧ IsPeriodicOn univ g ∧
      ∀ t ∈ Icc (0 : ℝ) S, ∀ x : Space, g (t, x) = f (t, x)

/-- Globally smooth periodic representatives give the local slab class. -/
theorem smoothForceT_of_contDiff {f : SpaceTimeField} (hf : ContDiff ℝ ∞ f)
    (hp : IsPeriodicOn univ f) : SmoothForceT f :=
  fun _ _ => ⟨f, hf, hp, fun _ _ _ => rfl⟩

/-- Local existence only consumes one smooth representative near `[0,1]`. -/
theorem exists_local_regular_smoothForceT
    (ν : ℝ) (hν : 0 < ν) (a : SpatialField) (ha : a ∈ initialClassT)
    (f : SpaceTimeField) (hf : SmoothForceT f) :
    ∃ T : ℝ, 0 < T ∧ ∃ v : ClassicalSolutionT ν a f T,
      PeriodicLocalRegularity ν a f T v := by
  obtain ⟨g, hgs, hgp, he⟩ := hf 1 zero_lt_one
  obtain ⟨T, hT, w, hr⟩ := exists_classical_of_picard ν hν a ha g hgs hgp
  have hL : 0 < min T 1 := lt_min hT zero_lt_one
  have heL : ∀ t ∈ Ico (0 : ℝ) (min T 1), ∀ x : Space, g (t, x) = f (t, x) :=
    fun t ht x => he t ⟨ht.1, ht.2.le.trans (min_le_right _ _)⟩ x
  let v : ClassicalSolutionT ν a f (min T 1) :=
    withForceT (restrictClassicalSolutionT w hL (min_le_left _ _))
      (fun t ht x => heL t ⟨ht.1.le, ht.2⟩ x)
  have hsub : Ico (0 : ℝ) (min T 1) ⊆ Ico 0 T := Ico_subset_Ico_right (min_le_left _ _)
  refine ⟨min T 1, hL, v, ?_, ?_, ?_⟩
  · intro m
    obtain ⟨G, hp, hc⟩ := hr.sobolev_smooth m
    exact ⟨G, fun t ht => hp t (hsub ht), hc.mono hsub⟩
  · intro t ht x
    have h := hr.pressure_poisson t (hsub ht) x
    simpa only [v, withForceT, restrictClassicalSolutionT,
      spatialDivergence, spatialDerivative, heL t ht] using h
  · intro t ht x
    have h := hr.projected t ⟨ht.1, ht.2.trans_le (min_le_left _ _)⟩ x
    simpa only [v, withForceT, restrictClassicalSolutionT, heL t ⟨ht.1.le, ht.2⟩ x] using h

/-- The underlying local classical solution. -/
theorem exists_local_smoothForceT
    (ν : ℝ) (hν : 0 < ν) (a : SpatialField) (ha : a ∈ initialClassT)
    (f : SpaceTimeField) (hf : SmoothForceT f) :
    ∃ T : ℝ, 0 < T ∧ Nonempty (ClassicalSolutionT ν a f T) := by
  obtain ⟨T, hT, w, _⟩ := exists_local_regular_smoothForceT ν hν a ha f hf
  exact ⟨T, hT, ⟨w⟩⟩

/-- Common-interval uniqueness needs no force-class hypothesis. -/
theorem velocity_unique_local {ν T₁ T₂ : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (hν : 0 < ν) (u₁ : ClassicalSolutionT ν a f T₁) (u₂ : ClassicalSolutionT ν a f T₂) :
    ∀ t ∈ Ico (0 : ℝ) (min T₁ T₂), ∀ x : Space,
      u₁.velocity (t, x) = u₂.velocity (t, x) :=
  flow_velocity_agree_on_common_interval hν (toFlow u₁) (toFlow u₂)

/-- Normalized pressures also agree on every common interval. -/
theorem pressure_unique_local {ν T₁ T₂ : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (hν : 0 < ν) (u₁ : ClassicalSolutionT ν a f T₁) (u₂ : ClassicalSolutionT ν a f T₂) :
    ∀ t ∈ Ico (0 : ℝ) (min T₁ T₂), ∀ x : Space,
      u₁.pressure (t, x) = u₂.pressure (t, x) := by
  have normalized (w : ClassicalSolutionT ν a f T₁) :
      IsNormalized (toFlow w) := by
    intro t ht
    rw [← integral_torusLift]
    exact w.pressure_gauge t ht
  have normalized₂ : IsNormalized (toFlow u₂) := by
    intro t ht
    rw [← integral_torusLift]
    exact u₂.pressure_gauge t ht
  exact fun t ht x ↦ (normalized_flows_agree hν (toFlow u₁) (toFlow u₂)
    (normalized u₁) normalized₂ t ht x).2

/-- A maximal periodic velocity exists for arbitrary smooth periodic forcing. -/
theorem exists_maximal_smoothForceT
    (ν : ℝ) (hν : 0 < ν) (a : SpatialField) (ha : a ∈ initialClassT)
    (f : SpaceTimeField) (hf : SmoothForceT f) :
    ∃ u p, IsMaximalPeriodicSolution ν a f u p := by
  obtain ⟨T, _hT, ⟨w₀⟩⟩ := exists_local_smoothForceT ν hν a ha f hf
  have hmaxPos : 0 < maximalLifespanT ν a f :=
    lt_of_lt_of_le (ENNReal.ofReal_pos.mpr w₀.horizon_pos)
      (le_iSup_of_le T (le_iSup_of_le ⟨w₀⟩ le_rfl))
  have hflowPos : 0 < lifespan ν a f := by
    rwa [← maximalLifespanT_eq_lifespan]
  let M : MaximalSolution ν a f :=
    (exists_maximal_periodic_solution_of_lifespan_pos hν hflowPos).some
  refine ⟨M.velocity, M.pressure, hmaxPos, ?_⟩
  intro S hS hSmax
  have hSlife : ENNReal.ofReal S < M.endpoint := by
    rw [M.endpoint_eq_lifespan, ← maximalLifespanT_eq_lifespan]
    exact hSmax
  let U : Flow ν a f S := M.flow S hS hSlife
  let w : ClassicalSolutionT ν a f S := ofNormalizedFlow U (M.normalized S hS hSlife)
  exact ⟨w, M.velocity_eq S hS hSlife, M.pressure_eq S hS hSlife⟩

/-- A bounded `H³` trajectory restarts uniformly across its endpoint. -/
theorem restartBeyond_smoothForceT
    (ν : ℝ) (hν : 0 < ν) (a : SpatialField) (f : SpaceTimeField)
    (hf : ContDiff ℝ ∞ f) (hper : IsPeriodicOn univ f)
    (S : ℝ) (hS : 0 < S) (u : SpaceTimeField) (p : SpaceTimeScalar)
    (hsolve : SolvesBelowT ν a f S u p) (K : ℝ≥0∞) (hK : K ≠ ⊤)
    (hbound : ∀ t ∈ Ico (0 : ℝ) S, periodicSobolevENorm 3 (fun x => u (t, x)) ≤ K) :
    ExtendsBeyondT ν a f S u p := by
  obtain ⟨d, hd, hloc⟩ := restartH3_smoothForceT ν hν f hf hper S K hK
  obtain ⟨t₀, ht₀0, ht₀S, ht₀d⟩ : ∃ t₀ : ℝ, 0 ≤ t₀ ∧ t₀ < S ∧ S < t₀ + d :=
    ⟨max 0 (S - d / 2), le_max_left _ _, max_lt hS (by linarith),
      by have := le_max_right 0 (S - d / 2); linarith⟩
  refine ⟨t₀ + d - S, by linarith, ?_⟩
  obtain ⟨w, hwv, hwp⟩ := hsolve ((t₀ + S) / 2) (by linarith) (by linarith)
  have hbmem : t₀ ∈ Ico (0 : ℝ) ((t₀ + S) / 2) := ⟨ht₀0, by linarith⟩
  have hKa : periodicSobolevENorm 3 (fun x => w.velocity (t₀, x)) ≤ K := by
    rw [hwv]
    exact hbound t₀ ⟨ht₀0, ht₀S⟩
  obtain ⟨w₂⟩ := hloc t₀ ⟨ht₀0, ht₀S.le⟩ (fun x => w.velocity (t₀, x))
    (velocitySlice_mem_initialClassT w hbmem) hKa
  obtain ⟨v, -, -⟩ := glueClassicalSolutionT hν w hbmem w₂ (by linarith : (t₀ + S) / 2 < t₀ + d)
  have hrew : S + (t₀ + d - S) = t₀ + d := by ring
  rw [hrew]
  refine ⟨v, ?_, ?_⟩
  · intro t ht x
    obtain ⟨wc, hwcv, -⟩ := hsolve ((t + S) / 2) (by linarith [ht.1]) (by linarith [ht.2])
    have hag := velocity_unique_local hν v wc t
      ⟨ht.1, lt_min (by linarith [ht.2]) (by linarith [ht.2])⟩ x
    rw [hag, hwcv]
  · intro t ht x
    obtain ⟨wc, -, hwcp⟩ := hsolve ((t + S) / 2) (by linarith [ht.1]) (by linarith [ht.2])
    have hag := pressure_unique_local hν v wc t
      ⟨ht.1, lt_min (by linarith [ht.2]) (by linarith [ht.2])⟩ x
    rw [hag, hwcp]

/-- The article's squared-`H²` continuation criterion for smooth periodic
forcing, without any temporal support or global integrability assumption. -/
theorem extendsBeyond_smoothForceT
    (ν : ℝ) (hν : 0 < ν) (a : SpatialField) (f : SpaceTimeField)
    (hf : ContDiff ℝ ∞ f) (hper : IsPeriodicOn univ f)
    (S : ℝ) (hS : 0 < S) (u : SpaceTimeField) (p : SpaceTimeScalar)
    (hu : SolvesBelowT ν a f S u p) (hfin : squaredHTwoIntegralT S u ≠ ⊤) :
    ExtendsBeyondT ν a f S u p := by
  obtain ⟨K, hK, hb⟩ := higherOrderBound_smoothForceT ν hν a f hf hper S hS u p hu hfin 3
  exact restartBeyond_smoothForceT ν hν a f hf hper S hS u p hu K hK hb

/-- Integral continuation only consumes a representative on `[0,S+1]`;
the extension solves the equation with the original force and agrees with
both original fields throughout `[0,S)`. -/
theorem extendsBeyond_locallySmoothForceT
    (ν : ℝ) (hν : 0 < ν) (a : SpatialField) (f : SpaceTimeField)
    (hf : SmoothForceT f) (S : ℝ) (hS : 0 < S)
    (u : SpaceTimeField) (p : SpaceTimeScalar)
    (hu : SolvesBelowT ν a f S u p) (hfin : squaredHTwoIntegralT S u ≠ ⊤) :
    ExtendsBeyondT ν a f S u p := by
  obtain ⟨g, hgs, hgp, he⟩ := hf (S + 1) (by linarith)
  have hug : SolvesBelowT ν a g S u p := by
    intro b hb hbS
    obtain ⟨w, hw, hp⟩ := hu b hb hbS
    refine ⟨withForceT w ?_, hw, hp⟩
    intro t ht x
    exact (he t ⟨ht.1.le, by linarith [ht.2]⟩ x).symm
  obtain ⟨δ, hδ, w, hw, hp⟩ := extendsBeyond_smoothForceT ν hν a g hgs hgp S hS u p hug hfin
  have hmin : 0 < min δ 1 := lt_min hδ zero_lt_one
  have hL : 0 < S + min δ 1 := add_pos hS hmin
  refine ⟨min δ 1, hmin,
    withForceT (restrictClassicalSolutionT w hL (by linarith [min_le_left δ 1])) ?_,
    hw, hp⟩
  intro t ht x
  exact he t ⟨ht.1.le, by linarith [ht.2, min_le_right δ 1]⟩ x

end NSFormalization.Section3.T11
