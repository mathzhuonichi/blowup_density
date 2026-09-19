import NSFormalization.Section3.T15.SobolevBound
import NSFormalization.Section3.T11.HighOrder

/-!
# T15 U14: convergence of the rescaled packet force

This module proves the complete `q = 1` conclusion of Proposition 3.3,
including all negative Sobolev orders.  The order-lowering theorem is stated
for every time exponent because it is independent of the packet.

The canonical `ScalingAPI.forceConvergence` field also asks for `q = 2` below
order `-1/2`.  That branch is not claimed here: the registered mixed scaling
at spatial exponent `2` has exponent `alphaT 2 2 = -1/2`, so the order-zero
norm grows rather than tends to zero.  A negative-order periodization estimate
preserving the whole-space `L²_t H^s_x` scaling is required; no such bridge is
present in the current tree.
-/

noncomputable section

namespace NSFormalization.Section3.T15

open Set MeasureTheory Filter Topology
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Section3.T11
open NSFormalization.Section4.A02 (SpaceTimeField forceTimeMeasure)
open scoped ContDiff ENNReal Topology

/-! ## Order lowering -/

theorem persistenceDown_norm_le_one {s r : ℝ} (hsr : s ≤ r)
    (A : PeriodicSobolev r) :
    ‖persistenceDown r s hsr A‖ ≤ ‖A‖ := by
  change ‖torusOrderDown r s hsr A‖ ≤ ‖A‖
  exact torusOrderDown_norm_le r s hsr A

/- Lowering the spatial Sobolev order contracts the complete time-Sobolev
norm.  The proof maps every admissible order-`r` datum path through the genuine
bounded Fourier reweighting `persistenceDown`; it does not identify the two
phantom-indexed datum types by definitional equality. -/
-- The nested subtype infimum and the two phantom Sobolev indices need extra elaboration budget.
set_option maxHeartbeats 400000 in
theorem forceSobolevENormT_mono_order {q : ℝ≥0∞} {s r : ℝ} (hsr : s ≤ r)
    (F : SpaceTimeField) :
    forceSobolevENormT q s F ≤ forceSobolevENormT q r F := by
  unfold forceSobolevENormT
  apply le_iInf
  rintro ⟨G, hpath, hmeas⟩
  let L : PeriodicSobolev r →L[ℝ] PeriodicSobolev s := persistenceDown r s hsr
  let H : ℝ → PeriodicSobolev s := fun t ↦ L (G t)
  have hHpath : IsPeriodicSobolevPath s F H := by
    intro t ht
    exact persistence_datum_of_reweight (hpath t ht)
      (persistenceDown_reweight r s hsr (G t))
  have hHmeas : AEStronglyMeasurable H forceTimeMeasure :=
    L.continuous.comp_aestronglyMeasurable hmeas
  refine (iInf_le _ ⟨H, hHpath, hHmeas⟩).trans (eLpNorm_mono fun t ↦ ?_)
  exact persistenceDown_norm_le_one hsr (G t)

/-! ## The nonnegative part of the `q = 1` range -/

/-- The packet estimate tends to zero at every `0 ≤ s < 1/2`.  The estimate
is only required on the admissible interval `(0, place.ε₀]`; that interval is
eventually present in the right-neighbourhood filter at zero. -/
theorem forceConvergence_one_nonnegative
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hf : ContDiff ℝ ∞ f)
    (hc : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f)
    (place : PlacementData u p f K) :
    ∀ s : ℝ, 0 ≤ s → s < (1 : ℝ) / 2 →
      Tendsto
        (fun ε : ℝ ↦ forceSobolevENormT 1 s
          (periodizedScaledForce f place.x₀ place.T ε))
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  intro s hs0 hs
  have hhalf : Tendsto (fun ε : ℝ ↦ ε ^ ((1 : ℝ) / 2)) (nhds 0) (nhds 0) := by
    simpa only [id_eq] using
      (Filter.tendsto_id.rpow_const_nhds_zero (by norm_num : 0 < (1 : ℝ) / 2))
  have hsub : Tendsto (fun ε : ℝ ↦ ε ^ ((1 : ℝ) / 2 - s)) (nhds 0) (nhds 0) := by
    simpa only [id_eq] using
      (Filter.tendsto_id.rpow_const_nhds_zero (by linarith : 0 < (1 : ℝ) / 2 - s))
  have hreal : Tendsto (fun ε : ℝ ↦ sobolevConst f s *
      (ε ^ ((1 : ℝ) / 2) + ε ^ ((1 : ℝ) / 2 - s))) (nhds 0) (nhds 0) := by
    simpa using (hhalf.add hsub).const_mul (sobolevConst f s)
  have hupper : Tendsto (fun ε : ℝ ↦ ENNReal.ofReal (sobolevConst f s *
      (ε ^ ((1 : ℝ) / 2) + ε ^ ((1 : ℝ) / 2 - s))))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa only [ENNReal.ofReal_zero] using
      (ENNReal.tendsto_ofReal hreal).mono_left nhdsWithin_le_nhds
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · exact Eventually.of_forall (fun _ ↦ bot_le)
  · filter_upwards [Ioc_mem_nhdsGT place.eps_pos] with ε hε
    exact packetSobolevBound hf hc place s hs0 (by linarith) ε hε

/-! ## All real orders below the `q = 1` threshold -/

/-- The literal `q = 1` specialization of `ScalingAPI.forceConvergence`, over
exactly the raw packet clauses used by the proof.  Negative orders contract to
the already proved order-zero limit. -/
theorem forceConvergence_one
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hf : ContDiff ℝ ∞ f)
    (hc : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f)
    (place : PlacementData u p f K) :
    ∀ s : ℝ, s < criticalOrder ((1 : ℝ≥0∞).toReal) →
      Tendsto
        (fun ε : ℝ ↦ forceSobolevENormT 1 s
          (periodizedScaledForce f place.x₀ place.T ε))
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  intro s hs
  have hs' : s < (1 : ℝ) / 2 := by
    norm_num [criticalOrder] at hs ⊢
    exact hs
  by_cases hs0 : 0 ≤ s
  · exact forceConvergence_one_nonnegative hf hc place s hs0 hs'
  · have hzero := forceConvergence_one_nonnegative hf hc place 0 le_rfl (by norm_num)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hzero
    · exact Eventually.of_forall (fun _ ↦ bot_le)
    · exact Eventually.of_forall (fun ε ↦ forceSobolevENormT_mono_order
        (show s ≤ 0 from le_of_not_ge hs0)
        (periodizedScaledForce f place.x₀ place.T ε))

end NSFormalization.Section3.T15
