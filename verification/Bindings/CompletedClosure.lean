import Bindings.CompactClassDensity
import Bindings.ScalingHomogeneous
import Bindings.HomogeneousPartialV2

/-! Proposition 4.6: the homogeneous completion and simultaneous closure.
The only analytic input is compact homogeneous path measurability. -/
noncomputable section
namespace BlowupDensity.Bindings
open Set Filter MeasureTheory
open Contracts.V1 Contracts.V1.Data
open NSFormalization.Section4
open NSFormalization.Paper3 (RealVectorSobolev)
open scoped ENNReal Topology ContDiff

/-- Compact smooth slices pair integrably with every Schwartz test. -/
theorem closure_pairable {f : SpaceTimeField} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (t : ℝ) :
    ∀ (i : Fin 3) (ψ : SchwartzMap Space ℂ),
      Integrable (fun x : Space => ψ x * ((f (t, x) i : ℝ) : ℂ)) := by
  exact D01.Homogeneous.integrable_schwartz_mul_component
    (D01.Homogeneous.compactSchwartzComponents
      (hf.comp (contDiff_const.prodMk contDiff_id))
      (D01.Homogeneous.compact_spatial_slice' hc t)) (fun _ _ => rfl)

/-- Path subtraction on smooth compact physical fields. -/
theorem closure_path_sub {s : ℝ} {f g : SpaceTimeField}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    {D E : ℝ → RealVectorSobolev s}
    (hD : IsHomogeneousPath s f D) (hE : IsHomogeneousPath s g E) :
    IsHomogeneousPath s (f - g) (D - E) := by
  intro t ht
  exact D01.Homogeneous.isHomogeneousSliceDatum_sub (hD t ht) (hE t ht)
    (closure_pairable hf hfc t) (closure_pairable hg hgc t)

/-- Path addition, with the integrability conditions explicit. -/
theorem closure_path_add {s : ℝ} {f g : SpaceTimeField}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    {D E : ℝ → RealVectorSobolev s}
    (hD : IsHomogeneousPath s f D) (hE : IsHomogeneousPath s g E) :
    IsHomogeneousPath s (f + g) (D + E) := by
  have hn := closure_path_sub contDiff_const HasCompactSupport.zero hg hgc
    (I03.zero_homogeneous_path s) hE
  have ha := closure_path_sub hf hfc (contDiff_const.sub hg)
    (HasCompactSupport.zero.sub hgc) hD hn
  change IsHomogeneousPath s (f - (0 - g)) (D - (0 - E)) at ha
  simpa only [zero_sub, sub_neg_eq_add] using ha

/-- Uniqueness identifies every measurable homogeneous path with the infimum. -/
theorem closure_norm_eq {q : ℝ≥0∞} {s : ℝ} {f : SpaceTimeField}
    {D : ℝ → RealVectorSobolev s} (hD : IsHomogeneousPath s f D)
    (hm : AEStronglyMeasurable D forceTimeMeasure) :
    forceHomogeneousENorm q s f = bochnerDatumENorm q s D := by
  refine le_antisymm (iInf_le_of_le ⟨D, hD, hm⟩ le_rfl) (le_iInf fun E => ?_)
  apply le_of_eq
  apply eLpNorm_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact D01.Homogeneous.isHomogeneousSliceDatum_unique (hD t ht.le) (E.2.1 t ht.le)

/-- Triangle inequality for the compact differences used by insertion. -/
theorem closure_norm_add (hreal : I03.CompactHomogeneousRealization)
    {f g : SpaceTimeField} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    forceHomogeneousENorm 2 (-1) (f + g) ≤
      forceHomogeneousENorm 2 (-1) f + forceHomogeneousENorm 2 (-1) g := by
  let D := D01.Homogeneous.compactHomogeneousPath (s := -1) (by norm_num) hf hfc
  let E := D01.Homogeneous.compactHomogeneousPath (s := -1) (by norm_num) hg hgc
  have hD : IsHomogeneousPath (-1) f D := D01.Homogeneous.isHomogeneousPath_compact _ hf hfc
  have hE : IsHomogeneousPath (-1) g E := D01.Homogeneous.isHomogeneousPath_compact _ hg hgc
  have hmD := hreal (-1) (by norm_num) (by norm_num) f hf hfc
  have hmE := hreal (-1) (by norm_num) (by norm_num) g hg hgc
  rw [closure_norm_eq (closure_path_add hf hfc hg hgc hD hE) (hmD.add hmE),
    closure_norm_eq hD hmD, closure_norm_eq hE hmE]
  exact eLpNorm_add_le hmD hmE (by norm_num)

/-- Scaling of the compact correction and source gives the homogeneous limit
for any inserted family, on an eventually smaller positive scale interval. -/
theorem closure_homogeneousConvergence (hreal : I03.CompactHomogeneousRealization)
    {ν : ℝ} {P : PacketAPI ν} (A : InsertionFamilyAPI ν P) :
    Tendsto (fun ε : ℝ => forceHomogeneousENorm 2 (-1)
      (fun z => A.force ε z - A.g z)) (𝓝[>] 0) (𝓝 0) := by
  let C := A.scaling.correction
  obtain ⟨K, hK⟩ := I03.correctionNegativeHomogeneous hreal C A.scaling.thresholds
    2 (by norm_num) (-1) (by norm_num) (by norm_num)
  let J := I03.packetHomogeneousConst P.force 2 (-1)
  have hb : A.scaling.thresholds.exponent (2 : ℝ≥0∞).toReal (-1) = (1 : ℝ) / 2 := by
    rw [A.scaling.thresholds.formula]; norm_num
  have hc : Continuous (fun ε : ℝ => ENNReal.ofReal (K * ε ^ ((3 : ℝ) / 2)) +
      ENNReal.ofReal (J * ε ^ ((1 : ℝ) / 2))) :=
    (ENNReal.continuous_ofReal.comp
      (continuous_const.mul (Real.continuous_rpow_const (by norm_num)))).add
    (ENNReal.continuous_ofReal.comp
      (continuous_const.mul (Real.continuous_rpow_const (by norm_num))))
  have hz : Tendsto (fun ε : ℝ => ENNReal.ofReal (K * ε ^ ((3 : ℝ) / 2)) +
      ENNReal.ofReal (J * ε ^ ((1 : ℝ) / 2))) (𝓝[>] 0) (𝓝 0) := by
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hz
    (Eventually.of_forall fun _ => zero_le)
  have hw : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Ioc (0 : ℝ) (scalingThreshold C) :=
    Ioc_mem_nhdsGT (scalingThreshold_pos C)
  filter_upwards [hw] with ε hε
  have he : (fun z => A.force ε z - A.g z) = C.forceCorrection ε + A.scaling.F ε := by
    funext z
    rw [A.force_formula]
    change A.g z + C.forceCorrection ε z + A.scaling.F ε z - A.g z = _
    simp only [Pi.add_apply]; abel
  rw [he]
  apply (closure_norm_add hreal (C.force_smooth ε (mem_correction_range C hε))
    (C.force_compactSupport ε (mem_correction_range C hε))
    (NSFormalization.Source.parabolicForce_smooth _ _ _ P.force_smooth)
    (NSFormalization.Source.parabolicForce_compact _ _ _ P.force_support.1)).trans
  apply add_le_add
  · simpa only [hb, show (1 : ℝ) / 2 + 1 = 3 / 2 by norm_num] using hK ε hε
  · have hp := I03.packetNegativeHomogeneous hreal P C.x₀ C.T
      (scalingThreshold C) A.scaling.thresholds 2 (by norm_num) (-1)
      (by norm_num) (by norm_num) ε hε
    rw [hb] at hp
    exact hp

/-- The raw reference is used directly, preserving its full pressure gauge. -/
theorem strongTrajectoryClosure_of_realization
    (hreal : I03.CompactHomogeneousRealization) :
    ∀ (a : SpatialField), a ∈ initialClassR →
      ∀ ν : ℝ, 0 < ν →
        ∀ T : ℝ, 0 < T →
          ∀ g : SpaceTimeField, MemForceR g →
            ∀ δ : ℝ, 0 < δ →
              ∀ R : ClassicalSolutionR ν a g (T + δ),
                ∃ (P : PacketAPI ν) (A : InsertionFamilyAPI ν P),
                  A.a = a ∧
                  A.scaling.correction.T = T ∧
                  A.scaling.correction.g = g ∧
                  A.scaling.correction.v = R.velocity ∧
                  A.scaling.correction.π = R.pressure ∧
                  (∀ ε ∈ Ioc (0 : ℝ) A.ε₀,
                    MemForceR (A.force ε) ∧
                    maximalLifespanR ν a (A.force ε) = ENNReal.ofReal T ∧
                    ∃ U : ClassicalSolutionR ν a (A.force ε) T,
                      U.velocity = A.velocity ε ∧ U.pressure = A.pressure ε) ∧
                  Tendsto (fun ε : ℝ => energyENorm T
                    (fun z => A.velocity ε z - R.velocity z))
                    (𝓝[>] 0) (𝓝 0) ∧
                  Tendsto (fun ε : ℝ =>
                    forceSobolevENorm 1 0 (fun z => A.force ε z - g z) +
                    forceSobolevENorm 2 (-1) (fun z => A.force ε z - g z) +
                    forceHomogeneousENorm 2 (-1) (fun z => A.force ε z - g z))
                    (𝓝[>] 0) (𝓝 0) := by
  intro a _ha ν hν T hT g hg δ hδ R
  let P := insertionFromData_packet ν hν
  have hsub : Ioo (0 : ℝ) (T + δ) ×ˢ (univ : Set Space) ⊆
      Ico (0 : ℝ) (T + δ) ×ˢ (univ : Set Space) :=
    prod_mono Ioo_subset_Ico_self Subset.rfl
  let C : CorrectionAPI ν P := correction P (T := T) (δ := δ) (r := 1)
    (v := R.velocity) (π := R.pressure) (g := g) 0 hT hδ zero_lt_one
    (R.velocity_smooth.mono hsub) (R.pressure_smooth.mono hsub)
    (fun t ht => R.divergence t ⟨ht.1.le, ht.2⟩) R.momentum
  let A := insertionFamily (scaling C thresholds) R rfl rfl
  refine ⟨P, A, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro ε hε
    exact ⟨InsertionLifespan.memForceR_force A hg hε,
      InsertionLifespan.lifespan_eq A hg hε, InsertionLifespan.sol_fullHorizon A hε⟩
  · exact mainThresholds_energyConvergence A
  · have h1 := A.forceConvergence 1 (Or.inl rfl) 0
      (by rw [A.scaling.thresholds.formula]; norm_num)
    have h2 := A.forceConvergence 2 (Or.inr rfl) (-1)
      (by rw [A.scaling.thresholds.formula]; norm_num)
    have hh := (h1.add h2).add (closure_homogeneousConvergence hreal A)
    simp only [add_zero] at hh
    exact hh

/-- Compact-class relative homogeneous density uses scaling of the difference. -/
theorem closure_relativeHomogeneous (hreal : I03.CompactHomogeneousRealization)
    (a : SpatialField) (ha : a ∈ initialClassR) (ν : ℝ) (hν : 0 < ν)
    (T : ℝ) (hT : 0 < T) (g : SpaceTimeField) (hg : MemForceCompact g)
    (r : ℝ≥0∞) (hr : 0 < r) :
    ∃ f ∈ breakdownSetIn forceClassCompact ν a T,
      forceHomogeneousENorm 2 (-1) (f - g) < r := by
  by_cases hl : maximalLifespanR ν a g ≤ ENNReal.ofReal T
  · refine ⟨g, ⟨hg, hl⟩, ?_⟩
    simpa only [sub_self, I03.forceHomogeneousENorm_zero] using hr
  · obtain ⟨P, L, hLa, hLg, hLT⟩ := insertionLifespanV2_of_data ν hν T hT a ha g
      (memForceR_of_memForceCompact hg) (lt_of_not_ge hl)
    have hc := closure_homogeneousConvergence hreal L.family
    have hs := hc.eventually (gt_mem_nhds hr)
    have hw : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Ioc (0 : ℝ) L.family.ε₀ :=
      Ioc_mem_nhdsGT L.family.eps_pos
    obtain ⟨ε, hε, hd⟩ := (hw.and hs).exists
    refine ⟨L.family.force ε, ⟨?_, (insertionFromData_lifespan L hLa hLT ε hε).le⟩, ?_⟩
    · exact memForceCompact_add_memForceCompact
        (f := L.family.force ε) (g := L.family.g) (hLg.symm ▸ hg)
        (L.family.forceDifference_compact ε hε)
    · change forceHomogeneousENorm 2 (-1) (fun z => L.family.force ε z - g z) < r
      simpa only [hLg] using hd

/-- Proposition 4.6's completed homogeneous clause, verbatim. -/
theorem completedHomogeneousDensity_of_realization
    (hreal : I03.CompactHomogeneousRealization) :
    ∀ (a : SpatialField), a ∈ initialClassR →
      ∀ ν : ℝ, 0 < ν →
        ∀ T : ℝ, 0 < T →
          CompletedDenseHomogeneous 2 (-1)
            (breakdownSetIn forceClassCompact ν a T) := by
  intro a ha ν hν T hT b hb r hr
  have hrhalf : 0 < r / 2 := ENNReal.half_pos hr.ne'
  obtain ⟨g, hg, Dg, hDg, hm, hd⟩ := homogeneousPartialV2.approxCompactHomogeneous
    2 (by norm_num) (by norm_num) (-1) (by constructor <;> norm_num)
    b hb (r / 2) hrhalf
  obtain ⟨f, hf, hfg⟩ := closure_relativeHomogeneous hreal a ha ν hν T hT g hg
    (r / 2) hrhalf
  rw [forceHomogeneousENorm, iInf_lt_iff] at hfg
  obtain ⟨E, hE⟩ := hfg
  have hp := closure_path_add hg.1 hg.2.1 (hf.1.1.sub hg.1)
    (hf.1.2.1.sub hg.2.1) hDg E.2.1
  change IsHomogeneousPath (-1) (g + (f - g)) (Dg + E.1) at hp
  have he : g + (f - g) = f := by abel
  refine ⟨f, hf, Dg + E.1, ?_, hm.add E.2.2, ?_⟩
  · simpa only [he] using hp
  · change eLpNorm ((Dg + E.1) - b) 2 forceTimeMeasure < r
    rw [show (Dg + E.1) - b = E.1 + (Dg - b) by abel]
    exact (eLpNorm_add_le E.2.2 (hm.sub hb.1) (by norm_num)).trans_lt
      ((ENNReal.add_lt_add hE hd).trans_eq (ENNReal.add_halves r))

/-- The zero completed target still requires an actual finite-lifespan force. -/
example (hreal : I03.CompactHomogeneousRealization) :
    ∀ r : ℝ≥0∞, 0 < r →
      ∃ f ∈ breakdownSetIn forceClassCompact 1 (0 : SpatialField) 1,
        ∃ D : ℝ → RealVectorSobolev (-1),
          IsHomogeneousPath (-1) f D ∧ AEStronglyMeasurable D forceTimeMeasure ∧
            bochnerDatumENorm 2 (-1) (D - (fun _ => 0)) < r := by
  exact completedHomogeneousDensity_of_realization hreal 0 A04.zero_mem_initialClassR
    1 (by norm_num) 1 (by norm_num) (fun _ => 0) (by exact MemLp.zero)

end BlowupDensity.Bindings
