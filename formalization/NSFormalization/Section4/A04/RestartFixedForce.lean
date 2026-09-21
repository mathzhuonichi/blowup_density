import NSFormalization.Section4.A04.RestartWiring
import NSFormalization.Section4.C01.EnergyDerivative

/-! Uniformity over all restart times in a compact interval for one force. -/
noncomputable section
namespace NSFormalization.Section4.A04
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
theorem referenceForce_timeShift_norm_le (f : SpaceTimeField) (hf : MemForceR f)
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
    (f : SpaceTimeField) (hf : MemForceR f) (S : ℝ) (_hS : 0 ≤ S) :
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
    (hν : 0 < ν) (hf : MemForceR f) (w : ClassicalSolutionR ν a f T)
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
    (hν : 0 < ν) (hf : MemForceR f) (w : ClassicalSolutionR ν a f T) :
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

/-- The retained carrier supplies precisely lane 179's closed-cylinder inputs
for its own solution and horizon, including the norm bound of that same path. -/
theorem localCarrier_gronwall_bound {ν S : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (ha : a ∈ initialClassR) (c : A01.LocalCarrier ν a f S) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ m : ℕ, 3 ≤ m → ∀ t ∈ Ico (0 : ℝ) S,
      sobolevNormAt (m : ℝ) c.w.velocity t ≤
        (sobolevNormAt (m : ℝ) c.w.velocity 0 + (forceSobolevENormL1 (m : ℝ) f).toReal) *
          Real.exp (Cgron m ν * (256 * R ^ 2 * S)) := by
  obtain ⟨v, hv, _hdiv, hinv, _hduh⟩ := c.hpairs 6 (le_refl 6)
  refine ⟨‖v‖, norm_nonneg _, ?_⟩
  intro m hm
  exact A01.highOrder_bddAbove_of_kbnd_Ico_full c.hν ha c.hf c.w
    c.regularity.sobolev_smooth c.hS v c.U hinv hv (by norm_num)
    (by simpa only [c.velocity_eq] using c.hslice) le_rfl hm

/-- The finite ENNReal criterion controls every running real H² integral.
No value at the terminal time is used. -/
theorem running_hTwo_integral_le {ν T S : ℝ} {a : SpatialField} {f u : SpaceTimeField}
    (w : ClassicalSolutionR ν a f T) (hwu : w.velocity = u) (hTS : T ≤ S)
    (hfin : squaredHTwoIntegral S u ≠ ⊤) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    (∫ r in (0 : ℝ)..t, sobolevNormAt 2 u r ^ 2) ≤ (squaredHTwoIntegral S u).toReal := by
  have hc : ContinuousOn (fun r => sobolevNormAt 2 u r ^ 2) (Icc (0 : ℝ) t) := by
    rw [← hwu]
    exact ((continuousOn_sobolevNormAt_velocity w 2).mono
      (fun r hr => ⟨hr.1, hr.2.trans_lt ht.2⟩)).pow 2
  have hint : IntegrableOn (fun r => sobolevNormAt 2 u r ^ 2) (Ioo (0 : ℝ) t) :=
    hc.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hle : ENNReal.ofReal (∫ r in (0 : ℝ)..t, sobolevNormAt 2 u r ^ 2) ≤
      squaredHTwoIntegral S u := by
    rw [intervalIntegral.integral_of_le ht.1, integral_Ioc_eq_integral_Ioo,
      ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ (fun r => sq_nonneg _))]
    calc
      _ = ∫⁻ r in Ioo (0 : ℝ) t, sobolevENorm 2 (fun x => u (r, x)) ^ 2 := by
        apply setLIntegral_congr_fun measurableSet_Ioo
        intro r hr
        have hn : sobolevENorm 2 (fun x => u (r, x)) ≠ ⊤ := by
          rw [← hwu]
          exact sobolevENorm_velocity_ne_top w 2 ⟨hr.1.le, hr.2.trans ht.2⟩
        change ENNReal.ofReal (sobolevNormAt 2 u r ^ 2) = _
        rw [sobolevNormAt, ENNReal.ofReal_pow ENNReal.toReal_nonneg,
          ENNReal.ofReal_toReal hn]
      _ ≤ squaredHTwoIntegral S u :=
        lintegral_mono' (Measure.restrict_mono
          (Ioo_subset_Ioo le_rfl (ht.2.le.trans hTS)) le_rfl) le_rfl
  have hnn : 0 ≤ ∫ r in (0 : ℝ)..t, sobolevNormAt 2 u r ^ 2 :=
    intervalIntegral.integral_nonneg ht.1 (fun r _ => sq_nonneg _)
  simpa only [ENNReal.toReal_ofReal hnn] using ENNReal.toReal_mono hfin hle

/-- Exact `HigherOrderBound`, using the same Grönwall engine as lane 179.
The actual integral criterion supplies its cap directly, so a terminal closed
cylinder and an endpoint value are unnecessary. -/
theorem higherOrderBound_of_gronwall : HigherOrderBound := by
  intro ν a f hν ha hf hf1 S hS u p hu hfin m
  let n := max m 3
  let B := (sobolevNormAt (n : ℝ) u 0 + (forceSobolevENormL1 (n : ℝ) f).toReal) *
    Real.exp (Cgron n ν * (squaredHTwoIntegral S u).toReal)
  have hmn : (m : ℝ) ≤ n := by exact_mod_cast (le_max_left m 3)
  let L := D01.lowerVectorL (n : ℝ) (m : ℝ) hmn
  refine ⟨ENNReal.ofReal (‖L‖ * B), ENNReal.ofReal_ne_top, ?_⟩
  intro t ht
  obtain ⟨w, hw, _⟩ := hu ((t + S) / 2) (by linarith [ht.1]) (by linarith [ht.2])
  have ht' : t ∈ Ico (0 : ℝ) ((t + S) / 2) := ⟨ht.1, by linarith [ht.2]⟩
  have hb := A01.highOrder_bddAbove_of_kbnd hν ha hf hf1 w
    (classical_hasSmoothSobolevPath hν hf w) (le_max_right m 3)
    w.horizon_pos le_rfl
    (fun r hr => running_hTwo_integral_le (S := S) w rfl (by linarith [ht.2])
      (by simpa only [hw] using hfin) hr) t ht'
  rw [hw] at hb
  obtain ⟨G, _, hG⟩ := w.sobolev n
  have hd : D01.IsSobolevDatum (n : ℝ) (fun x => u (t, x)) (G t) := by
    rw [← hw]
    exact hG t ht'
  have hn : ‖G t‖ ≤ B := by
    change (sobolevENorm (n : ℝ) (fun x => u (t, x))).toReal ≤ B at hb
    rw [sobolevENorm_eq hd] at hb
    simpa only [toReal_enorm] using hb
  rw [sobolevENorm_eq (D01.Leray.isSobolevDatum_lower hmn hd), ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal ((L.le_opNorm (G t)).trans
    (mul_le_mul_of_nonneg_left hn (norm_nonneg L)))

/-- The one remaining gluing obligation: an actual shifted local solution
extends the lifespan of the original problem. This is not `A02.patch`, whose
two inputs have the same zero-time initial datum. -/
def ShiftedLocalExtension : Prop :=
  ∀ (ν : ℝ), 0 < ν → ∀ (a : SpatialField) (f : SpaceTimeField) (T : ℝ)
    (w : ClassicalSolutionR ν a f T) (b : ℝ), b ∈ Ico (0 : ℝ) T →
    ∀ L : ℝ, ClassicalSolutionR ν (fun x => w.velocity (b, x)) (timeShift b f) L →
      ENNReal.ofReal (b + L) ≤ maximalLifespanR ν a f

/-- Fixed-force R1. Unlike the H¹/all-force draft, the force and compact
restart interval precede δ, and the datum bound is H⁷. -/
theorem restartBeyond_fixed (extension : ShiftedLocalExtension)
    (ν : ℝ) (hν : 0 < ν) (f : SpaceTimeField) (hf : MemForceR f)
    (S : ℝ) (hS : 0 < S) (restart : RestartFixedForce ν f S)
    (K : ℝ≥0∞) (hK : K ≠ ⊤) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (a : SpatialField) (u : SpaceTimeField) (p : SpaceTimeScalar),
      a ∈ initialClassR → SolvesBelow ν a f S u p →
      (∀ t ∈ Ico (0 : ℝ) S, sobolevENorm 7 (fun x => u (t, x)) ≤ K) →
      ENNReal.ofReal (S + δ) ≤ maximalLifespanR ν a f := by
  obtain ⟨δ, hδ, hr⟩ := restart K hK
  refine ⟨δ, hδ, ?_⟩
  intro a u p _ha hu hbound
  apply restartBeyond_of_restartAt hS hδ
  intro t ht
  obtain ⟨w, hw, _⟩ := hu ((t + S) / 2) (by linarith [ht.1]) (by linarith [ht.2])
  have ht' : t ∈ Ico (0 : ℝ) ((t + S) / 2) := ⟨ht.1, by linarith [ht.2]⟩
  have ha' := w.restart_datum ht'
  have hf' := restart_force f hf t ht.1
  let c := A01.localCarrier ν (fun x => w.velocity (t, x)) (timeShift t f) hν ha' hf'
  have hd : δ ≤ A01.localHorizon' ν (fun x => w.velocity (t, x)) (timeShift t f) :=
    hr t ⟨ht.1, ht.2.le⟩ _ ha' (by simpa only [hw] using hbound t ht)
  exact extension ν hν a f _ w t ht' δ (c.w.restrict hδ hd)

/-- Fixed-force integral continuation. Only shifted gluing remains explicit;
`HigherOrderBound` supplies H⁷ instead of the former H¹ restart datum. -/
theorem extendsBeyond_fixed (extension : ShiftedLocalExtension)
    (higherOrderBound : HigherOrderBound)
    (ν : ℝ) (a : SpatialField) (f : SpaceTimeField)
    (hν : 0 < ν) (ha : a ∈ initialClassR) (hf : MemForceR f) (hf1 : MemL1Hm f)
    (S : ℝ) (hS : 0 < S) (restart : RestartFixedForce ν f S)
    (u : SpaceTimeField) (p : SpaceTimeScalar)
    (hu : SolvesBelow ν a f S u p) (hfin : squaredHTwoIntegral S u ≠ ⊤) :
    ENNReal.ofReal S < maximalLifespanR ν a f := by
  obtain ⟨K, hK, hbound⟩ := higherOrderBound ν a f hν ha hf hf1 S hS u p hu hfin 7
  obtain ⟨δ, hδ, hr⟩ := restartBeyond_fixed extension ν hν f hf S hS restart K hK
  have he := hr a u p ha hu hbound
  exact ((ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < S + δ)).mpr
    (by linarith : S < S + δ)).trans_le he

/-- The fixed-force window and Grönwall inputs have both been discharged. -/
theorem extendsBeyond_of_memForceR (extension : ShiftedLocalExtension)
    (ν : ℝ) (a : SpatialField) (f : SpaceTimeField)
    (hν : 0 < ν) (ha : a ∈ initialClassR) (hf : MemForceR f)
    (S : ℝ) (hS : 0 < S) (u : SpaceTimeField) (p : SpaceTimeScalar)
    (hu : SolvesBelow ν a f S u p) (hfin : squaredHTwoIntegral S u ≠ ⊤) :
    ENNReal.ofReal S < maximalLifespanR ν a f :=
  extendsBeyond_fixed extension higherOrderBound_of_gronwall ν a f hν ha hf
    (memL1Hm_of_memForceR hf) S hS (restartFixedForce_of_memForceR ν hν f hf S hS.le)
    u p hu hfin

/-- C1 with fixed-force restart windows; no cross-force uniformity is used. -/
theorem lifespanInfiniteOfLocallyFinite_fixed (extension : ShiftedLocalExtension)
    (restart : ∀ ν, 0 < ν → ∀ f, MemForceR f → ∀ S, 0 ≤ S → RestartFixedForce ν f S)
    (higherOrderBound : HigherOrderBound) :
    ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField),
      0 < ν → a ∈ initialClassR → MemForceR f → MemL1Hm f →
      0 < maximalLifespanR ν a f →
      ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
        (∀ b : ℝ, 0 < b → ENNReal.ofReal b < maximalLifespanR ν a f →
          ∃ w : ClassicalSolutionR ν a f b, w.velocity = u ∧ w.pressure = p) →
        (∀ S : ℝ, 0 < S → ENNReal.ofReal S ≤ maximalLifespanR ν a f →
          squaredHTwoIntegral S u ≠ ⊤) →
        maximalLifespanR ν a f = ⊤ := by
  apply lifespanInfiniteOfLocallyFinite_of_extendsBeyond
  intro ν a f hν ha hf hf1 S hS u p hu hfin
  exact extendsBeyond_fixed extension higherOrderBound ν a f hν ha hf hf1 S hS
    (restart ν hν f hf S hS.le) u p hu hfin

/-- All analytic bounds discharged; the displayed extension input is solely
the shifted classical gluing statement, not a uniform restart hypothesis. -/
theorem lifespanInfiniteOfLocallyFinite_of_memForceR (extension : ShiftedLocalExtension)
    (ν : ℝ) (a : SpatialField) (f : SpaceTimeField)
    (hν : 0 < ν) (ha : a ∈ initialClassR) (hf : MemForceR f)
    (u : SpaceTimeField) (p : SpaceTimeScalar)
    (hu : IsMaximalSolution ν a f u p)
    (hfin : ∀ S : ℝ, 0 < S → ENNReal.ofReal S ≤ maximalLifespanR ν a f →
      squaredHTwoIntegral S u ≠ ⊤) : maximalLifespanR ν a f = ⊤ :=
  lifespanInfiniteOfLocallyFinite_fixed extension restartFixedForce_of_memForceR
    higherOrderBound_of_gronwall ν a f hν ha hf (memL1Hm_of_memForceR hf) hu.1
    u p hu.2 hfin

end NSFormalization.Section4.A04
