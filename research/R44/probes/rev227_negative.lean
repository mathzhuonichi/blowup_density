import NSFormalization.Section4.R44.Pieces
import NSFormalization.Section4.R44.EnergyIdentity
import NSFormalization.Section4.R43.Endpoint

/-! Proposition 4.4, conditional only on the locally integrable S1 differential
inequality. No value at a singular endpoint is used. The final unconditional
instantiation is deliberately left to the S1 absorption lane. -/
noncomputable section
namespace NSFormalization.Section4.R44
open Set MeasureTheory
open A02 (SpaceTimeField SpatialField ClassicalSolutionR maximalLifespanR IsMaximalSolution
  exists_maximal' presingularTimes)
open D01
open NSFormalization.Paper3
open scoped ENNReal

/-- The manuscript L² force norm; definitionally the D01 path-infimum norm. -/
abbrev forceSobolevENormL2 (s : ℝ) (f : SpaceTimeField) : ℝ≥0∞ :=
  forceSobolevENorm 2 s f

/-- Universal threshold, including room for the cubic critical embedding. -/
def theta : ℝ := min R43.criticalConst (1 / (100 * (A05.criticalL3Const + 1) ^ 3))
def C₂ : ℝ := 2
def C₃ : ℝ := 4

theorem theta_pos : 0 < theta := by
  exact lt_min R43.criticalConst_pos (by positivity [A05.criticalL3Const_pos])
theorem C₂_pos : 0 < C₂ := by norm_num [C₂]
theorem C₃_pos : 0 < C₃ := by norm_num [C₃]

def radiusCoefficient : ℝ := theta / (4 * (C₃ + 1))
def radiusRate : ℝ := C₂ + 1
def radius (ν S : ℝ) : ℝ :=
  radiusCoefficient * ν ^ (3 / 2 : ℝ) * Real.exp (-(radiusRate * ν * S))

theorem radiusCoefficient_pos : 0 < radiusCoefficient := by
  unfold radiusCoefficient
  positivity [theta_pos, C₃_pos]
theorem radiusRate_pos : 0 < radiusRate := by unfold radiusRate; linarith [C₂_pos]
theorem radius_pos {ν S : ℝ} (hν : 0 < ν) : 0 < radius ν S :=
  mul_pos (mul_pos radiusCoefficient_pos (Real.rpow_pos_of_pos hν _)) (Real.exp_pos _)

theorem radiusCoefficient_small : C₃ * radiusCoefficient ^ 2 < theta ^ 2 / 4 := by
  have hpos : 0 < C₃ + 1 := by linarith [C₃_pos]
  have heq : (C₃ + 1) * radiusCoefficient ^ 2 = theta ^ 2 / (16 * (C₃ + 1)) := by
    unfold radiusCoefficient
    field_simp
    ring
  calc
    _ < (C₃ + 1) * radiusCoefficient ^ 2 := by nlinarith [sq_pos_of_pos radiusCoefficient_pos]
    _ = theta ^ 2 / (16 * (C₃ + 1)) := heq
    _ < theta ^ 2 / 4 := div_lt_div_of_pos_left (sq_pos_of_pos theta_pos)
      (by norm_num) (by linarith [C₃_pos])

/-- Exactly S1: a single derivative, integrable on every closed presingular
window, and eq:Rcritical2 on the open classical interval. -/
structure RCritical2Differential {ν T : ℝ} {f : SpaceTimeField}
    (w : ClassicalSolutionR ν (fun _ => 0) f T) (_hf : A02.MemForceR f) : Prop where
  differential : ∃ E' : ℝ → ℝ,
    (∀ S, 0 ≤ S → S < T → IntervalIntegrable E' volume 0 S) ∧
    ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasDerivAt (fun s => Y (C01.slice w.velocity s) ^ 2) (E' t) t ∧
      (Y (C01.slice w.velocity t) ≤ theta * ν →
        E' t + ν * Z (C01.slice w.velocity t) ^ 2 ≤
          C₂ * ν * Y (C01.slice w.velocity t) ^ 2 +
            C₃ * ν⁻¹ * B (C01.slice f t) ^ 2)

/-- The physical negative-half-order force norm is continuous on future times. -/
theorem forceB_continuousOn {f : SpaceTimeField} (hf : A02.MemForceR f) :
    ContinuousOn (fun t => B (C01.slice f t)) (Ici (0 : ℝ)) := by
  obtain ⟨G, hG, hGc, _, _⟩ := hf.2 2
  have hc := ((lowerVectorL 2 (-1 / 2) (by norm_num)).continuous.comp_continuousOn
    hGc.continuousOn).norm
  refine hc.congr ?_
  intro t ht
  change (sobolevENorm (-1 / 2) (fun x => f (t,x))).toReal = _
  rw [sobolevENorm_eq_of_isSobolevDatum
    (Leray.isSobolevDatum_lower (by norm_num : (-1 / 2 : ℝ) ≤ 2) (hG t ht))]
  simp

/-- The canonical negative-order path realizes the exact global L² time norm.
Datum uniqueness makes every competitor in the defining infimum equal a.e. -/
theorem force_norm_eq_path {f : SpaceTimeField}
    {G : ℝ → RealVectorSobolev (-1 / 2)} (hG : IsSobolevPath (-1 / 2) f G)
    (hGm : AEStronglyMeasurable G forceTimeMeasure) :
    forceSobolevENorm 2 (-1 / 2) f = eLpNorm G 2 forceTimeMeasure := by
  apply le_antisymm
  · exact iInf_le_of_le ⟨G, hG, hGm⟩ le_rfl
  · refine le_iInf ?_
    rintro ⟨H, hH, _⟩
    apply le_of_eq
    apply eLpNorm_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    exact isSobolevDatum_unique (hG t ht.le) (hH t ht.le)

/-- G3: the force-square prefix is bounded by the square of the manuscript norm. -/
theorem forceB_prefix_le {f : SpaceTimeField} (hf : A02.MemForceR f)
    {S : ℝ} (hS : 0 ≤ S) :
    ∫ t in (0 : ℝ)..S, B (C01.slice f t) ^ 2 ≤
      (forceSobolevENorm 2 (-1 / 2) f).toReal ^ 2 := by
  obtain ⟨G, hG, _, _, hG2⟩ := hf.2 2
  let H := fun t => lowerVectorL 2 (-1 / 2) (by norm_num) (G t)
  have hH : IsSobolevPath (-1 / 2) f H := isSobolevPath_lower (by norm_num) hG
  have hHm : MemLp H 2 forceTimeMeasure :=
    (lowerVectorL 2 (-1 / 2) (by norm_num)).comp_memLp' hG2
  rw [force_norm_eq_path hH hHm.aestronglyMeasurable]
  have hi : ContinuousOn (fun t => B (C01.slice f t) ^ 2) (Icc 0 S) :=
    ((forceB_continuousOn hf).mono Icc_subset_Ici_self).pow 2
  have hint : IntervalIntegrable (fun t => B (C01.slice f t) ^ 2) volume 0 S :=
    hi.intervalIntegrable_of_Icc hS
  have he : ENNReal.ofReal (∫ t in (0 : ℝ)..S, B (C01.slice f t) ^ 2) ≤
      (eLpNorm H 2 forceTimeMeasure) ^ 2 := by
    rw [intervalIntegral.integral_of_le hS,
      ofReal_integral_eq_lintegral_ofReal hint.1 (ae_of_all _ (fun t => sq_nonneg _)),
      eLpNorm_two_sq]
    calc
      _ = ∫⁻ t in Ioc 0 S, ‖H t‖ₑ ^ (2 : ℝ) := by
        apply setLIntegral_congr_fun measurableSet_Ioc
        intro t ht
        change ENNReal.ofReal ((sobolevENorm (-1 / 2) (fun x => f (t,x))).toReal ^ 2) = _
        rw [sobolevENorm_eq_of_isSobolevDatum (hH t ht.1.le)]
        rw [← ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg _),
          ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
        exact R43.enorm_npow_two_eq_rpow_two _
      _ ≤ _ := lintegral_mono' (Measure.restrict_mono Ioc_subset_Ioi_self le_rfl) le_rfl
  have hn : 0 ≤ ∫ t in (0 : ℝ)..S, B (C01.slice f t) ^ 2 :=
    intervalIntegral.integral_nonneg hS (fun _ _ => sq_nonneg _)
  have hr := ENNReal.toReal_mono (ENNReal.pow_ne_top hHm.eLpNorm_lt_top.ne) he
  simpa only [ENNReal.toReal_ofReal hn, ENNReal.toReal_pow] using hr

/-- S2 on a closed presingular window; the global radius may use a later S. -/
theorem Y_bound_of_differential {ν T S b : ℝ} {f : SpaceTimeField}
    (hν : 0 < ν) (hf : A02.MemForceR f)
    (w : ClassicalSolutionR ν (fun _ => 0) f T) (hd : RCritical2Differential w hf)
    (hb : 0 ≤ b) (hbT : b < T) (hbS : b ≤ S)
    (hsmall : forceSobolevENormL2 (-1 / 2) f < ENNReal.ofReal (radius ν S)) :
    ∀ t ∈ Icc (0 : ℝ) b, Y (C01.slice w.velocity t) ≤ -(theta * ν / 2) := by
  obtain ⟨E', hEi, hE⟩ := hd.differential
  let y := fun t => Y (C01.slice w.velocity t)
  let yExt := fun t => y (projIcc 0 b hb t)
  have hy : ContinuousOn y (Icc (0 : ℝ) b) := by
    have hc := (energyVelocity_smooth hν hf w (by norm_num : (1/2 : ℝ) ≤ 2)).continuousOn.norm
    refine (hc.mono (fun t ht => ⟨ht.1, ht.2.trans_lt hbT⟩)).congr ?_
    intro t ht
    exact Y_eq_norm (jWeightDatumPath w hf t ⟨ht.1, ht.2.trans_lt hbT⟩)
  have hyExt : Continuous yExt :=
    (continuousOn_iff_continuous_domRestrict.mp hy).comp continuous_projIcc
  have hy0 : yExt 0 = 0 := by
    have hz : C01.slice w.velocity 0 = (0 : SpatialField) := funext w.initial
    simp only [yExt, projIcc_left, y, hz, Y]
    erw [sobolevENorm_eq_of_isSobolevDatum (isSobolevDatum_zero (1/2))]
    simp
  have hfinite := forceSobolevENorm_ne_top hf (m := 0)
    (by norm_num : (-1 / 2 : ℝ) ≤ (0 : ℕ)) (Or.inr rfl)
  have hsmallReal : (forceSobolevENormL2 (-1 / 2) f).toReal < radius ν S := by
    exact (ENNReal.toReal_lt_toReal hfinite ENNReal.ofReal_ne_top).mpr hsmall |>.trans_eq
      (ENNReal.toReal_ofReal (radius_pos hν).le)
  have hs := radius_forces_gronwall_small hν (hb.trans hbS) C₂_pos.le C₃_pos
    radiusCoefficient_pos radiusCoefficient_small ENNReal.toReal_nonneg hsmallReal
  have hs' : C₃ * ν⁻¹ * (forceSobolevENormL2 (-1 / 2) f).toReal ^ 2 *
      Real.exp (C₂ * ν * b) < (theta * ν) ^ 2 / 4 := by
    apply lt_of_le_of_lt _ hs
    apply mul_le_mul_of_nonneg_left
    · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hbS (mul_pos C₂_pos hν).le)
    · positivity [C₃_pos]
  have hbound := criticalSquaredNormBound_radius hb hν theta_pos C₂_pos.le C₃_pos.le
    (sq_nonneg _) hs' hyExt hy0 (fun _ _ => ENNReal.toReal_nonneg)
    (((forceB_continuousOn hf).mono Icc_subset_Ici_self).pow 2)
    (fun t ht => forceB_prefix_le hf ht.1)
    (Y := yExt) (Z := fun t => Z (C01.slice w.velocity t))
    (B := fun t => B (C01.slice f t)) (E' := E')
    (fun t ht => by
      have heq : (fun r => yExt r ^ 2) =ᶠ[nhds t] (fun r => y r ^ 2) := by
        filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
        simp only [yExt, projIcc_of_mem hb ⟨hr.1.le, hr.2.le⟩]
      exact ((hE t ⟨ht.1, ht.2.trans hbT⟩).1).congr_of_eventuallyEq heq)
    (hEi b hb hbT)
    (fun t ht => by
      simpa only [yExt, projIcc_of_mem hb ⟨ht.1.le, ht.2.le⟩, y] using
        (hE t ⟨ht.1, ht.2.trans hbT⟩).2)
  intro t ht
  simpa only [yExt, projIcc_of_mem hb ht, y] using hbound t ht

/-- Homogeneous-to-inhomogeneous comparison on a classical slice. -/
theorem velocity_dot_le_sobolev {ν T : ℝ} {f : SpaceTimeField}
    (w : ClassicalSolutionR ν (fun _ => 0) f T) {t : ℝ} (ht : t ∈ Ico 0 T) :
    A05.dotHomogeneousENorm (1 / 2) (C01.slice w.velocity t) ≤
      sobolevENorm (1 / 2) (C01.slice w.velocity t) := by
  have hu := energyVelocity_isDatum w (1 / 2) ht
  have hh := R43.CriticalHomogeneous.ofSobolevVector_isHomogeneousSliceDatum
    (by norm_num : (0 : ℝ) ≤ 1/2) hu
  unfold C01.slice
  rw [A05.u1_dotHomogeneousENorm_eq hh, sobolevENorm_eq_of_isSobolevDatum hu]
  rw [← ofReal_norm, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (R43.ofSobolevVector_norm_le _ (by norm_num) _)

/-- S3: the same theta discharges C01 V4's viscosity-scaled L³ gate. -/
theorem absorption_of_differential {ν T S : ℝ} {f : SpaceTimeField}
    (hν : 0 < ν) (hf : A02.MemForceR f)
    (w : ClassicalSolutionR ν (fun _ => 0) f T) (hd : RCritical2Differential w hf)
    (hsmall : forceSobolevENormL2 (-1 / 2) f < ENNReal.ofReal (radius ν S))
    {t : ℝ} (ht : t ∈ Ico 0 T) (htS : t ≤ S) :
    ENNReal.ofReal A05.gradientL6Const * C01.criticalL3 (C01.slice w.velocity t) ≤
      ENNReal.ofReal (ν / 4) := by
  have hy := Y_bound_of_differential hν hf w hd ht.1 ht.2 htS hsmall t ⟨ht.1, le_rfl⟩
  apply R43.criticalL3_gate_enorm A05.gradientL6Const_pos.le A05.criticalL3Const_pos.le
    (c := theta) hν (hy.trans (show theta * ν / 2 ≤ theta * ν by linarith [mul_pos theta_pos hν]))
  · have he := (A05.velocityCriticalL3 _ (C01.velocity_slice_memHInfty w ht)).trans
      (mul_le_mul_right (velocity_dot_le_sobolev w ht) _)
    have hn : sobolevENorm (1/2) (C01.slice w.velocity t) ≠ ⊤ :=
      ne_top_of_le_ne_top (by simp)
        (sobolevENorm_le_of_isSobolevDatum (energyVelocity_isDatum w (1/2) ht))
    rw [Y, ENNReal.ofReal_mul A05.criticalL3Const_pos.le, ENNReal.ofReal_toReal hn]
    exact he
  · exact (mul_le_mul_of_nonneg_left (min_le_left _ _)
      (mul_pos A05.gradientL6Const_pos A05.criticalL3Const_pos).le).trans
        R43.criticalConst_absorption

/-- The maximal family inherits the L³ gate up to the prescribed horizon. -/
theorem maximal_absorption_of_differential {ν S : ℝ}
    {f u : SpaceTimeField} {p : A02.SpaceTimeScalar}
    (hν : 0 < ν) (hf : A02.MemForceR f)
    (hd : ∀ T (w : ClassicalSolutionR ν (fun _ => 0) f T), RCritical2Differential w hf)
    (hu : IsMaximalSolution ν (fun _ => 0) f u p)
    (hsmall : forceSobolevENormL2 (-1 / 2) f < ENNReal.ofReal (radius ν S))
    {t : ℝ} (ht : t ∈ presingularTimes ν (fun _ => 0) f) (htS : t ≤ S) :
    ENNReal.ofReal A05.gradientL6Const * C01.criticalL3 (C01.slice u t) ≤
      ENNReal.ofReal (ν / 4) := by
  obtain ⟨T, htT, w, hw, _⟩ := hu.exists_solution_after ht
  simpa only [hw] using absorption_of_differential hν hf w (hd T w) hsmall ⟨ht.1, htT⟩ htS

/-- S4/G4: C01's explicit budget at every finite endpoint L ≤ S, including
L equal to the maximal lifespan. G5 is supplied by R43.MaximalEndpoint. -/
theorem maximal_h2TimeIntegral_of_differential {ν S L : ℝ}
    {f u : SpaceTimeField} {p : A02.SpaceTimeScalar}
    (hν : 0 < ν) (hf : A02.MemForceR f)
    (hd : ∀ T (w : ClassicalSolutionR ν (fun _ => 0) f T), RCritical2Differential w hf)
    (hu : IsMaximalSolution ν (fun _ => 0) f u p)
    (hsmall : forceSobolevENormL2 (-1 / 2) f < ENNReal.ofReal (radius ν S))
    (hL : 0 < L) (hLS : L ≤ S)
    (hLL : ENNReal.ofReal L ≤ maximalLifespanR ν (fun _ => 0) f) :
    ∫⁻ t in Ioo (0 : ℝ) L, sobolevENorm 2 (C01.slice u t) ^ (2 : ℝ) ≤
      ENNReal.ofReal (32 * L * C01.forcePrimitive f L ^ 2 +
        32 * (ν⁻¹) ^ 2 * ∫ t in (0 : ℝ)..L, C01.l2Sq (C01.slice f t)) := by
  have hb := R43.maximal_h2TimeIntegral hν A04.zero_mem_initialClassR hf hu hL hLL
    (fun t ht => maximal_absorption_of_differential hν hf hd hu hsmall
      ⟨ht.1, ((ENNReal.ofReal_lt_ofReal_iff hL).mpr ht.2).trans_le hLL⟩
      (ht.2.le.trans hLS))
  simpa [C01.energyBudget, C01.l2Norm, C01.l2Sq, C01.gradientSq] using hb

/-- The explicit finite budget in A04's natural-square spelling. -/
theorem maximal_squaredHTwoIntegral_of_differential {ν S L : ℝ}
    {f u : SpaceTimeField} {p : A02.SpaceTimeScalar}
    (hν : 0 < ν) (hf : A02.MemForceR f)
    (hd : ∀ T (w : ClassicalSolutionR ν (fun _ => 0) f T), RCritical2Differential w hf)
    (hu : IsMaximalSolution ν (fun _ => 0) f u p)
    (hsmall : forceSobolevENormL2 (-1 / 2) f < ENNReal.ofReal (radius ν S))
    (hL : 0 < L) (hLS : L ≤ S)
    (hLL : ENNReal.ofReal L ≤ maximalLifespanR ν (fun _ => 0) f) :
    A04.squaredHTwoIntegral L u ≠ ⊤ := by
  have hb := maximal_h2TimeIntegral_of_differential hν hf hd hu hsmall hL hLS hLL
  have heq : A04.squaredHTwoIntegral L u =
      ∫⁻ t in Ioo (0 : ℝ) L, sobolevENorm 2 (C01.slice u t) ^ (2 : ℝ) := by
    simp only [A04.squaredHTwoIntegral, R43.enorm_npow_two_eq_rpow_two]
    rfl
  rw [heq]
  exact ne_of_lt (lt_of_le_of_lt hb ENNReal.ofReal_lt_top)

/-- S5/S6: the exact strict finite-horizon conclusion, with S1 as the only
remaining named input. In particular this does not assert infinite lifespan. -/
theorem rcritical2_endpoint_of_differential
    (ν S : ℝ) (hν : 0 < ν) (hS : 0 < S)
    (f : SpaceTimeField) (hf : A02.MemForceR f)
    (hd : ∀ T (w : ClassicalSolutionR ν (fun _ => 0) f T), RCritical2Differential w hf)
    (hsmall : forceSobolevENormL2 (-1 / 2) f < ENNReal.ofReal (radius ν S)) :
    ENNReal.ofReal S < maximalLifespanR ν (fun _ => 0) f := by
  obtain ⟨u, p, hu⟩ := exists_maximal' ν (fun _ => 0) f hν A04.zero_mem_initialClassR hf
  by_contra hn
  have hle := le_of_not_gt hn
  have hfinite : maximalLifespanR ν (fun _ => 0) f ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  let L := (maximalLifespanR ν (fun _ => 0) f).toReal
  have heq : ENNReal.ofReal L = maximalLifespanR ν (fun _ => 0) f :=
    ENNReal.ofReal_toReal hfinite
  have hL : 0 < L := ENNReal.toReal_pos hu.1.ne' hfinite
  have hLS : L ≤ S := (ENNReal.ofReal_le_ofReal_iff hS.le).mp (heq.trans_le hle)
  have hbelow : A04.SolvesBelow ν (fun _ => 0) f L u p := by
    intro b hb hbL
    apply hu.2 b hb
    rw [← heq]
    exact (ENNReal.ofReal_lt_ofReal_iff hL).mpr hbL
  have hbad := A04.extendsBeyond_of_memForceR' ν (fun _ => 0) f hν
    A04.zero_mem_initialClassR hf L hL u p hbelow
    (maximal_squaredHTwoIntegral_of_differential hν hf hd hu hsmall hL hLS heq.le)
  rw [heq] at hbad
  exact (lt_irrefl _ hbad)

/-- Instantiation skeleton: S1d supplies the first argument. After that argument
is discharged, the remaining binders are the RCritical2API.main field. -/
theorem rcritical2_endpoint
    (differential : ∀ (ν : ℝ), 0 < ν → ∀ (f : SpaceTimeField) (hf : A02.MemForceR f),
      ∀ T (w : ClassicalSolutionR ν (fun _ => 0) f T), RCritical2Differential w hf) :
    ∀ ν S : ℝ, 0 < ν → 0 < S →
      ∀ f : SpaceTimeField, A02.MemForceR f →
        forceSobolevENormL2 (-1 / 2) f < ENNReal.ofReal (radius ν S) →
          ENNReal.ofReal S < maximalLifespanR ν (fun _ => 0) f := by
  intro ν S hν hS f hf hsmall
  exact rcritical2_endpoint_of_differential ν S hν hS f hf (differential ν hν f hf) hsmall

/-- S1 is satisfiable: the zero solution uses the identically zero derivative. -/
theorem zeroSol_differential (ν T : ℝ) (hν : 0 < ν) (hT : 0 < T) :
    RCritical2Differential (A04.zeroSol ν T hν hT) A04.memForceR_zero := by
  refine ⟨0, fun _ _ _ => intervalIntegrable_const, ?_⟩
  intro t ht
  have hy : Y (0 : SpatialField) = 0 := by
    erw [Y, sobolevENorm_eq_of_isSobolevDatum (isSobolevDatum_zero (1/2))]
    simp
  have hz := (zero_energy_terms ν T hν hT ⟨ht.1.le, ht.2⟩).2.1
  have hb : B (0 : SpatialField) = 0 := by
    erw [B, sobolevENorm_eq_of_isSobolevDatum (isSobolevDatum_zero (-1/2))]
    simp
  constructor
  · change HasDerivAt (fun _ => Y (0 : SpatialField) ^ 2) 0 t
    rw [hy]
    exact hasDerivAt_const t _
  · intro _
    change 0 + ν * Z (0 : SpatialField) ^ 2 ≤ C₂ * ν * Y (0 : SpatialField) ^ 2 +
      C₃ * ν⁻¹ * B (0 : SpatialField) ^ 2
    change Z (0 : SpatialField) = 0 at hz
    rw [hy, hz, hb]
    simp

end NSFormalization.Section4.R44
