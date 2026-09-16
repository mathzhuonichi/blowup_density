import NSFormalization.Section4.A04.RestartWiring
import NSFormalization.Section4.C01.EnergyDerivative
import NSFormalization.Section4.R43.CriticalDatumPath
import NSFormalization.Section4.A04.MomentumDatum

/-! # Smooth critical trajectories and momentum

The carrier-window argument below is copied from lane 215 (whose module is
not present in this baseline), with a separate namespace. The half-order
bridge uses the existing order-two momentum theorem.
-/
noncomputable section
namespace NSFormalization.Section4.R43.CarrierWindow
open NSFormalization.Section4
open A04
open Set MeasureTheory
open NavierStokes.ProblemStatement (Space)
open NSFormalization.Section4.A02
open NSFormalization.Section4.D01 (sobolevENorm)
open EulerSmoothFieldSobolevTime EulerCylinderSobolevSpace
open scoped ENNReal

/-- One duration is chosen before both the restart time and the H⁷-bounded datum. -/
def RestartFixedForce (ν : ℝ) (f : SpaceTimeField) (S : ℝ) : Prop :=
  ∀ K : ℝ≥0∞, K ≠ ⊤ → ∃ δ : ℝ, 0 < δ ∧
    ∀ t₀ ∈ Icc (0 : ℝ) S, ∀ a' : SpatialField, a' ∈ initialClassR →
      sobolevENorm 7 a' ≤ K → δ ≤ A01.localHorizon' ν a' (timeShift t₀ f)

/-- Restricting one compact force path controls every translated unit window. -/
theorem referenceForce_timeShift_norm_le (f : SpaceTimeField) (hf : A02.MemForceR f)
    (S t₀ : ℝ) (ht₀ : t₀ ∈ Icc (0 : ℝ) S) :
    ‖A01.referenceForce (timeShift t₀ f) (restart_force f hf t₀ ht₀.1)‖ ≤
      ‖sobolevPath (C01.forcePath (S := S + 1) hf)
        (C01.forcePath_jetLp_continuous (S := S + 1) hf) 6‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro t
  let s : Icc (0 : ℝ) (S + 1) :=
    ⟨t.1 + t₀, by constructor <;> linarith [t.2.1, t.2.2, ht₀.1, ht₀.2]⟩
  have he : C01.forcePath (S := 1) (restart_force f hf t₀ ht₀.1) t =
      C01.forcePath hf s := by
    apply EulerOrdinarySobolev.field_ext
    rfl
  change ‖EulerMeanSmoothRepresentative.ordinarySobolev 6 _ _‖ ≤ _
  simp only [he]
  exact ContinuousMap.norm_coe_le_norm
    (sobolevPath (C01.forcePath hf) (C01.forcePath_jetLp_continuous hf) 6) s

/-- The antitone selected horizon, rather than an unrelated existential horizon,
gives the required lower bound for every shifted force. -/
theorem restartFixedForce_of_memForceR (ν : ℝ) (hν : 0 < ν)
    (f : SpaceTimeField) (hf : A02.MemForceR f) (S : ℝ) (_hS : 0 ≤ S) :
    RestartFixedForce ν f S := by
  intro K hK
  let B := ‖sobolevPath (C01.forcePath (S := S + 1) hf)
    (C01.forcePath_jetLp_continuous (S := S + 1) hf) 6‖
  refine ⟨A01.uniformHorizon ν (A01.datumRadiusConstant * K.toReal) B,
    A01.uniformHorizon_pos _ _ _, ?_⟩
  intro t₀ ht₀ a ha hbound
  rw [A01.localHorizon'_eq hν ha (restart_force f hf t₀ ht₀.1)]
  apply A01.uniformHorizon_antitone ν _ (referenceForce_timeShift_norm_le f hf S t₀ ht₀)
  obtain ⟨D, hD⟩ := ha.1.2 7
  have hD' : D01.IsSobolevDatum 7 (A01.selectedDatum a ha).field D := by
    rw [(A01.selectedDatum_spec a ha).1]
    exact hD
  have hn : ‖D‖ ≤ K.toReal := by
    have h := ENNReal.toReal_mono hK hbound
    have he : sobolevENorm 7 a = ‖D‖ₑ := sobolevENorm_eq hD
    rw [he] at h
    simpa only [toReal_enorm] using h
  exact (A01.cylinderDatum_norm_le (A01.selectedDatum a ha) D hD').trans
    (mul_le_mul_of_nonneg_left hn A01.datumRadiusConstant_nonneg)

open NavierStokes.ProblemStatement
open scoped ContDiff

/-- A classical solution viewed from a nonnegative interior time. -/
def shiftedSolution {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionR ν a f T) (b : ℝ) (hb : b ∈ Ico (0 : ℝ) T) :
    ClassicalSolutionR ν (fun x => w.velocity (b, x)) (timeShift b f) (T - b) where
  velocity := timeShift b w.velocity
  pressure := fun z => w.pressure (z.1 + b, z.2)
  horizon_pos := sub_pos.mpr hb.2
  velocity_smooth := w.velocity_smooth.comp
    ((contDiff_fst.add contDiff_const).prodMk contDiff_snd).contDiffOn
    (fun z hz => ⟨⟨by linarith [hz.1.1, hb.1], by linarith [hz.1.2]⟩, mem_univ _⟩)
  pressure_smooth := w.pressure_smooth.comp
    ((contDiff_fst.add contDiff_const).prodMk contDiff_snd).contDiffOn
    (fun z hz => ⟨⟨by linarith [hz.1.1, hb.1], by linarith [hz.1.2]⟩, mem_univ _⟩)
  initial := fun x => by simp [timeShift]
  divergence := fun t ht x => w.divergence (t + b)
    ⟨by linarith [ht.1, hb.1], by linarith [ht.2]⟩ x
  momentum := by
    intro t ht x
    have ht' : t + b ∈ Ioo (0 : ℝ) T :=
      ⟨by linarith [ht.1, hb.1], by linarith [ht.2]⟩
    have hd := C01.velocity_hasDerivAt_time w ht' x
    have hadd : HasDerivAt (fun s : ℝ => s + b) 1 t := (hasDerivAt_id t).add_const b
    have hs := hd.scomp t hadd
    have he : temporalDerivative (timeShift b w.velocity) t x =
        temporalDerivative w.velocity (t + b) x := by
      simpa [temporalDerivative, timeShift, Function.comp_def]
        using congrArg (fun L : ℝ →L[ℝ] Space => L 1) hs.hasFDerivAt.fderiv
    change temporalDerivative (timeShift b w.velocity) t x + _ - _ + _ = _
    rw [he]
    exact w.momentum (t + b) ht' x
  sobolev := fun m => by
    obtain ⟨G, hGc, hG⟩ := w.sobolev m
    exact ⟨fun t => G (t + b), hGc.comp (continuous_id.add continuous_const).continuousOn
      (fun t ht => ⟨by linarith [ht.1, hb.1], by linarith [ht.2]⟩),
      fun t ht => hG (t + b) ⟨by linarith [ht.1, hb.1], by linarith [ht.2]⟩⟩
  pressure_gradient := fun t ht => w.pressure_gradient (t + b)
    ⟨by linarith [ht.1, hb.1], by linarith [ht.2]⟩

/-- Compact interior velocity intervals have a finite H⁷ bound. -/
theorem compact_hSeven_bound {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionR ν a f T) {c : ℝ} (hc : c < T) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ t ∈ Icc (0 : ℝ) c,
      sobolevENorm 7 (fun x => w.velocity (t, x)) ≤ K := by
  obtain ⟨G, hGc, hG⟩ := w.sobolev 7
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hGc.mono (show Icc (0 : ℝ) c ⊆ Ico 0 T from fun t ht => ⟨ht.1, ht.2.trans_lt hc⟩))
  refine ⟨ENNReal.ofReal C, ENNReal.ofReal_ne_top, ?_⟩
  intro t ht
  have hd : D01.IsSobolevDatum 7 (fun x => w.velocity (t, x)) (G t) :=
    hG t ⟨ht.1, ht.2.trans_lt hc⟩
  rw [sobolevENorm_eq hd, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (hC t ht)

/-- A backward choice of restart point puts each time inside a regular local
carrier window. The window begins at zero only when needed at the left endpoint. -/
theorem exists_carrier_window {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (hν : 0 < ν) (hf : A02.MemForceR f) (w : ClassicalSolutionR ν a f T)
    (t : ℝ) (ht : t ∈ Ico (0 : ℝ) T) :
    ∃ b : ℝ, ∃ _hb : b ∈ Ico (0 : ℝ) T,
      b ≤ t ∧ (b < t ∨ b = 0) ∧
      t - b < A01.localHorizon' ν (fun x => w.velocity (b, x)) (timeShift b f) := by
  obtain ⟨K, hK, hbound⟩ := compact_hSeven_bound w ht.2
  obtain ⟨δ, hδ, hr⟩ := restartFixedForce_of_memForceR ν hν f hf t ht.1 K hK
  let b := max 0 (t - δ / 2)
  have hb0 : 0 ≤ b := le_max_left _ _
  have hbt : b ≤ t := max_le ht.1 (by linarith)
  have hbT : b < T := hbt.trans_lt ht.2
  refine ⟨b, ⟨hb0, hbT⟩, hbt, ?_, ?_⟩
  · by_cases ht0 : t = 0
    · exact Or.inr (le_antisymm (ht0 ▸ hbt) hb0)
    · exact Or.inl (max_lt (lt_of_le_of_ne ht.1 (Ne.symm ht0)) (by linarith))
  · have hd := hr b ⟨hb0, hbt⟩ _ (w.restart_datum ⟨hb0, hbT⟩) (hbound b ⟨hb0, hbt⟩)
    have : t - b < δ := by have := le_max_right (0 : ℝ) (t - δ / 2); dsimp [b]; linarith
    exact this.trans_le hd

open Filter Topology

/-- Uniqueness transfers the selected carrier's smooth Sobolev paths to every
classical solution, using overlapping windows rather than endpoint extension. -/
theorem classical_hasSmoothSobolevPath {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (hν : 0 < ν) (hf : A02.MemForceR f) (w : ClassicalSolutionR ν a f T) :
    HasSmoothSobolevPath T w.velocity := by
  intro m
  obtain ⟨G, _hGc, hG⟩ := w.sobolev m
  refine ⟨G, hG, ?_⟩
  intro t ht
  obtain ⟨b, hb, hbt, hbt0, hlen⟩ := exists_carrier_window hν hf w t ht
  let c := A01.localCarrier ν (fun x => w.velocity (b, x)) (timeShift b f) hν
    (w.restart_datum hb) (restart_force f hf b hb.1)
  let L := A01.localHorizon' ν (fun x => w.velocity (b, x)) (timeShift b f)
  obtain ⟨H, hH, hHc⟩ := c.regularity.sobolev_smooth m
  let J := Ico b (min T (b + L))
  have htJ : t ∈ J := ⟨hbt, lt_min ht.2 (by dsimp [L] at *; linarith)⟩
  have hJ : J ∈ 𝓝[Ico (0 : ℝ) T] t := by
    have hu : Iio (min T (b + L)) ∈ 𝓝 t := Iio_mem_nhds htJ.2
    rcases hbt0 with hlt | hz
    · exact mem_nhdsWithin_of_mem_nhds
        (Ico_mem_nhds hlt htJ.2)
    · filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hu] with r hr hr'
      exact ⟨by simpa [hz] using hr.1, hr'⟩
  have heq : ∀ r ∈ J, G r = H (r - b) := by
    intro r hr
    have hrT : r ∈ Ico (0 : ℝ) T := ⟨hb.1.trans hr.1, hr.2.trans_le (min_le_left _ _)⟩
    have hrL : r - b ∈ Ico (0 : ℝ) L :=
      ⟨sub_nonneg.mpr hr.1, by have := hr.2.trans_le (min_le_right _ _); linarith⟩
    have hv := velocity_unique_core hν (shiftedSolution w b hb) c.w (r - b)
      ⟨hrL.1, lt_min (by linarith [hrT.2]) hrL.2⟩
    have hv' : (fun x => w.velocity (r, x)) = (fun x => c.w.velocity (r - b, x)) := by
      funext x
      simpa only [shiftedSolution, timeShift, sub_add_cancel] using hv x
    apply D01.isSobolevDatum_unique (hG r hrT)
    rw [hv']
    exact hH (r - b) hrL
  have hc : ContDiffOn ℝ ∞ (fun r => H (r - b)) J :=
    hHc.comp (contDiff_id.sub contDiff_const).contDiffOn (fun r hr =>
      ⟨sub_nonneg.mpr hr.1, by have := hr.2.trans_le (min_le_right _ _); linarith⟩)
  exact ((hc.congr heq) t htJ).mono_of_mem_nhdsWithin hJ

end NSFormalization.Section4.R43.CarrierWindow

namespace NSFormalization.Section4.R43

open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Paper3 NSFormalization.Source NSFormalization.Source.RealSobolev
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField ClassicalSolutionR MemForceR)
open NSFormalization.Section4.D01
open scoped ContDiff ENNReal

namespace CriticalHomogeneous

/-- The Bessel-to-homogeneous multiplier is real linear. -/
def ofSobolevScalarLM (s : ℝ) (hs : 0 ≤ s) :
    RealSobolevHilbert s →ₗ[ℝ] RealSobolevHilbert s where
  toFun := ofSobolevScalar s hs
  map_add' A B := by
    apply Subtype.ext
    exact (BesselFractionalData.datum s hs).map_add _ _
  map_smul' c A := by
    apply Subtype.ext
    exact (BesselFractionalData.datum s hs).map_smul_of_tower c _

/-- Contractivity gives the continuous linear scalar conversion. -/
def ofSobolevScalarL (s : ℝ) (hs : 0 ≤ s) :
    RealSobolevHilbert s →L[ℝ] RealSobolevHilbert s :=
  (ofSobolevScalarLM s hs).mkContinuous 1 (fun A => by
    change ‖BesselFractionalData.datum s hs (A : FourierData)‖ ≤ 1 * ‖(A : FourierData)‖
    simpa only [one_mul] using BesselFractionalData.datum_norm_le s hs (A : FourierData))

/-- Componentwise continuous linear Bessel-to-homogeneous conversion. -/
def ofSobolevVectorL (s : ℝ) (hs : 0 ≤ s) :
    RealVectorSobolev s →L[ℝ] RealVectorSobolev s :=
  (PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : Fin 3 => RealSobolevHilbert s)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i : Fin 3 =>
      (ofSobolevScalarL s hs).comp
        ((ContinuousLinearMap.proj i).comp
          (PiLp.continuousLinearEquiv 2 ℝ
            (fun _ : Fin 3 => RealSobolevHilbert s)).toContinuousLinearMap)))

@[simp] theorem ofSobolevVectorL_apply (s : ℝ) (hs : 0 ≤ s)
    (A : RealVectorSobolev s) :
    ofSobolevVectorL s hs A = ofSobolevVector s hs A := rfl

/-- A chosen homogeneous slice equals the continuous linear conversion of
any inhomogeneous datum at a sufficiently high order. Uniqueness holds at
all real orders, including the homogeneous endpoint. -/
theorem chosenHomogeneousDatum_eq {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s)
    {z : SpatialField} {A : RealVectorSobolev s} (hA : IsSobolevDatum s z A) :
    chosenHomogeneousDatum r z =
      ofSobolevVectorL r hr (lowerVectorL s r hrs A) := by
  have hd := ofSobolevVector_isHomogeneousSliceDatum hr
    (Leray.isSobolevDatum_lower hrs hA)
  exact Homogeneous.isHomogeneousSliceDatum_unique
    (chosenHomogeneousDatum_isDatum ⟨_, hd⟩) hd

/-- The single bounded map used for both the path and its momentum equation. -/
def orderTwoToHalf : RealVectorSobolev 2 →L[ℝ] RealVectorSobolev (1 / 2) :=
  (ofSobolevVectorL (1 / 2) (by norm_num)).comp
    (lowerVectorL 2 (1 / 2) (by norm_num))

/-- Identification of the map on any physical order-two datum. -/
theorem chosenHomogeneousDatum_eq_orderTwoToHalf {z : SpatialField}
    {A : RealVectorSobolev 2} (hA : IsSobolevDatum 2 z A) :
    chosenHomogeneousDatum (1 / 2) z = orderTwoToHalf A :=
  chosenHomogeneousDatum_eq (by norm_num) (by norm_num) hA

end CriticalHomogeneous

open CriticalHomogeneous

/-- The canonical half-order path is smooth for every classical solution. -/
theorem criticalVelocityHalf_smooth
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (hν : 0 < ν) (hf : A02.MemForceR f) (w : ClassicalSolutionR ν a f T) :
    ContDiffOn ℝ ∞ (criticalVelocityHalf w) (Ico (0 : ℝ) T) := by
  obtain ⟨G, hG, hGc⟩ := CarrierWindow.classical_hasSmoothSobolevPath hν hf w 2
  have heq : ∀ t ∈ Ico (0 : ℝ) T,
      criticalVelocityHalf w t = orderTwoToHalf (G t) :=
    fun t ht => chosenHomogeneousDatum_eq_orderTwoToHalf (hG t ht)
  exact (orderTwoToHalf.contDiff.comp_contDiffOn hGc).congr heq

-- The dependent order-two carrier construction and derivative transport
-- exceed the default elaboration budget; keep the increase local.
set_option maxHeartbeats 400000 in
/-- The physical momentum equation transported through the bounded half-order
multiplier. Order two permits the existing datum differentiation theorem. -/
theorem criticalVelocityHalf_momentum
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (hν : 0 < ν) (hf : A02.MemForceR f) (w : ClassicalSolutionR ν a f T) :
    ∀ t ∈ Ioo (0 : ℝ) T,
      deriv (criticalVelocityHalf w) t =
        ν • criticalLaplacianHalf w t - criticalAdvectionHalf w t -
          criticalPressureHalf w t + criticalForceHalf (f := f) t := by
  obtain ⟨G, hG, hGc⟩ := CarrierWindow.classical_hasSmoothSobolevPath hν hf w 2
  intro t ht
  have hl := laplacian_slice_smoothL2 w ht
  have hn := advection_slice_smoothL2 w ht
  have hp := pressureGradient_slice_smoothSquareIntegrableJets_of_memForceR w hf ht
  have hf' := forceSlice_smoothL2_of_memForceR hf ht.1.le
  obtain ⟨L, hL⟩ := exists_isSobolevDatum_of_contDiff_memLp hl.1 hl.2 (2 : ℝ)
  obtain ⟨N, hN⟩ := exists_isSobolevDatum_of_contDiff_memLp hn.1 hn.2 (2 : ℝ)
  obtain ⟨P, hP⟩ := exists_isSobolevDatum_of_contDiff_memLp hp.1 hp.2 (2 : ℝ)
  obtain ⟨F, hF⟩ := exists_isSobolevDatum_of_contDiff_memLp hf'.1 hf'.2 (2 : ℝ)
  have hm := A04.momentum_datum w hf (m := 2) (by norm_num) hG hGc ht hL hN hP hF
  have hd : HasDerivAt G (deriv G t) t :=
    ((hGc.differentiableOn (by simp) t (Ioo_subset_Ico_self ht)).differentiableAt
      (Ico_mem_nhds ht.1 ht.2)).hasDerivAt
  have heq : criticalVelocityHalf w =ᶠ[nhds t] (fun r => orderTwoToHalf (G r)) := by
    filter_upwards [Ico_mem_nhds ht.1 ht.2] with r hr
    exact chosenHomogeneousDatum_eq_orderTwoToHalf (hG r hr)
  have hd' : HasDerivAt (criticalVelocityHalf w) (orderTwoToHalf (deriv G t)) t :=
    (orderTwoToHalf.hasFDerivAt.comp_hasDerivAt t hd).congr_of_eventuallyEq heq
  rw [hd'.deriv, hm, orderTwoToHalf.map_add, orderTwoToHalf.map_sub,
    orderTwoToHalf.map_sub, orderTwoToHalf.map_smul]
  exact congrArg₂ (fun X Y => X + Y)
    (congrArg₂ (fun X Y => X - Y)
      (congrArg₂ (fun X Y => X - Y)
        (congrArg (fun X => ν • X)
          (chosenHomogeneousDatum_eq_orderTwoToHalf hL).symm)
        (chosenHomogeneousDatum_eq_orderTwoToHalf hN).symm)
      (chosenHomogeneousDatum_eq_orderTwoToHalf hP).symm)
    (chosenHomogeneousDatum_eq_orderTwoToHalf hF).symm

/-- Both time-path obligations are unconditional for positive viscosity. -/
theorem criticalDatumInputs_of_classical
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (hν : 0 < ν) (hf : A02.MemForceR f) (w : ClassicalSolutionR ν a f T) :
    CriticalDatumInputs w hf :=
  ⟨criticalVelocityHalf_smooth hν hf w, criticalVelocityHalf_momentum hν hf w⟩

/-- Every positive-viscosity classical solution has the exact critical carrier. -/
theorem exists_criticalDatumPath'
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (hν : 0 < ν) (hf : A02.MemForceR f) (w : ClassicalSolutionR ν a f T) :
    Nonempty (CriticalDatumPath w hf) :=
  exists_criticalDatumPath w hf (criticalDatumInputs_of_classical hν hf w)

/-- `eq:Rcritical1` with no datum-path or momentum hypothesis. -/
theorem rcritical1_of_classical'
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (hν : 0 < ν) (hf : A02.MemForceR f) (w : ClassicalSolutionR ν a f T) :
    (∀ t ∈ Ioo (0 : ℝ) T,
      HasDerivAt (fun r => criticalNormAt w.velocity r ^ 2)
        (criticalEnergyDerivative
          (criticalDatumPath w hf (criticalDatumInputs_of_classical hν hf w)) t) t) ∧
      ∀ t ∈ Ioo (0 : ℝ) T,
        criticalEnergyDerivative
            (criticalDatumPath w hf (criticalDatumInputs_of_classical hν hf w)) t / 2 +
            (ν - trilinearConst * criticalNormAt w.velocity t) *
              criticalDissipationAt w.velocity t ^ 2
          ≤ criticalForceAt f t * criticalNormAt w.velocity t :=
  rcritical1_of_classical w hf (criticalDatumInputs_of_classical hν hf w)

end NSFormalization.Section4.R43
