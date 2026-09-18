import NSFormalization.Section3.T11.Uniqueness
import NSFormalization.Section3.T11.CriterionBridge
import NSFormalization.Section3.T10.ForcePaths

/-!
# Maximal periodic solutions

The older Paper 1 `Flow` class and T10's `ClassicalSolutionT` have the same
PDE fields.  This module supplies the three fields forgotten by `toFlow` for
an arbitrary normalized `Flow`.  The only substantial adapter is continuity
of the integer-order Fourier datum path on the original half-open slab; it is
proved from slab smoothness using the local cube-integral continuity theorem.

Consequently the two supremal lifespans agree without an existence
hypothesis.  Maximal gluing then uses Paper 1's unconditional construction.
Until U11 lands, positivity is supplied by the single explicitly named local
existence input below.
-/

noncomputable section

namespace NSFormalization.Section3.T11

open Set MeasureTheory Filter
open NavierStokes NavierStokes.ProblemStatement
open NavierStokes.PeriodicIntegration (spatialPartial)
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField SpaceTimeScalar)
open NSFormalization.Section3.T10
open NSFormalization.Paper1
open NSFormalization.Paper1.PeriodicLifespan
open NSFormalization.Paper1.PeriodicLocalLifespan
open NSFormalization.Paper1.PeriodicPressureNormalization
open scoped ContDiff ENNReal BigOperators Topology

/-! ## Completing a Paper 1 flow -/

/-- Spatial differentiation preserves smoothness on the original half-open
time slab.  At `t = 0` the joint derivative is a within-derivative, while the
spatial slice has an ordinary derivative because its spatial domain is all of
`Space`. -/
theorem spatialPartial_time_contDiffOn_Ico {F : SpaceTime → ℂ} {T : ℝ}
    (hF : ContDiffOn ℝ ∞ F (Ico (0 : ℝ) T ×ˢ (univ : Set Space)))
    (i : Fin 3) :
    ContDiffOn ℝ ∞ (fun z : SpaceTime ↦
      spatialPartial i (fun x ↦ F (z.1, x)) z.2)
      (Ico (0 : ℝ) T ×ˢ (univ : Set Space)) := by
  let D : Set SpaceTime := Ico (0 : ℝ) T ×ˢ (univ : Set Space)
  let G : SpaceTime → ℂ := fun z ↦
    fderivWithin ℝ F D z (0, coordinateVector i)
  have hUD : UniqueDiffOn ℝ D :=
    (uniqueDiffOn_Ico (0 : ℝ) T).prod uniqueDiffOn_univ
  have hG : ContDiffOn ℝ ∞ G D := by
    exact (hF.fderivWithin hUD (by simp)).clm_apply contDiffOn_const
  apply hG.congr
  intro z hz
  have hjoint := (hF.differentiableOn (by simp) z hz).hasFDerivWithinAt
  have hprod : HasFDerivWithinAt (fun x : Space ↦ (z.1, x))
      (ContinuousLinearMap.inr ℝ ℝ Space) univ z.2 :=
    (hasFDerivAt_prodMk_right z.1 z.2).hasFDerivWithinAt
  have hmaps : MapsTo (fun x : Space ↦ (z.1, x)) univ D :=
    fun x _ ↦ ⟨hz.1, mem_univ x⟩
  have hslice : HasFDerivAt (F ∘ fun x : Space ↦ (z.1, x))
      ((fderivWithin ℝ F D z).comp (ContinuousLinearMap.inr ℝ ℝ Space)) z.2 := by
    exact (hjoint.comp z.2 hprod hmaps).hasFDerivAt univ_mem
  change fderiv ℝ (F ∘ fun x : Space ↦ (z.1, x)) z.2 (coordinateVector i) = G z
  rw [hslice.fderiv]
  rfl

/-- The recursively defined integer-order periodic energy is nonnegative. -/
theorem periodicIntegerEnergy_nonneg (n : ℕ) (g : Space → ℂ) :
    0 ≤ periodicIntegerEnergy n g := by
  induction n generalizing g with
  | zero => exact integral_nonneg (fun _ ↦ sq_nonneg _)
  | succ n ih =>
      exact add_nonneg (ih g) (Finset.sum_nonneg (fun i _ ↦ ih (spatialPartial i g)))

/-- Every integer-order periodic energy of a jointly smooth field is
continuous on its original half-open time interval. -/
theorem continuousOn_periodicIntegerEnergy_time_Ico (n : ℕ)
    {F : SpaceTime → ℂ} {T : ℝ}
    (hF : ContDiffOn ℝ ∞ F (Ico (0 : ℝ) T ×ˢ (univ : Set Space))) :
    ContinuousOn (fun t ↦ periodicIntegerEnergy n (fun x ↦ F (t, x)))
      (Ico (0 : ℝ) T) := by
  induction n generalizing F with
  | zero =>
      change ContinuousOn (fun t ↦
        NavierStokes.PeriodicIntegration.cubeIntegral (fun x ↦ ‖F (t, x)‖ ^ 2))
        (Ico (0 : ℝ) T)
      exact cubeIntegral_continuousOn_Ico (hF.continuousOn.norm.pow 2)
  | succ n ih =>
      exact (ih hF).add (by
        simpa only [Prod.fst, Prod.snd] using
          (continuousOn_finsetSum Finset.univ (fun i _ ↦
            ih (spatialPartial_time_contDiffOn_Ico hF i))))

/-- The physical integer-order energy distance between two velocity slices. -/
def periodicDatumEnergyDistance (m : ℕ) (u : SpaceTimeField) (t r : ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin 3,
    NSFormalization.Paper1.periodicIntegerEnergy m
      (fun x ↦ ((u (r, x) - u (t, x)) i : ℂ)))

/-- The distance between two selected data is the physical integer-order
energy of the difference of their represented slices. -/
theorem periodicDatum_path_norm_sub (m : ℕ) {u : SpaceTimeField} {T : ℝ}
    (hs : ContDiffOn ℝ ∞ u (Ico (0 : ℝ) T ×ˢ (univ : Set Space)))
    (G : ℝ → PeriodicSobolev (m : ℝ))
    (hG : ∀ t ∈ Ico (0 : ℝ) T,
      IsPeriodicDatum (m : ℝ) (fun x ↦ u (t, x)) (G t))
    {t r : ℝ} (ht : t ∈ Ico (0 : ℝ) T) (hr : r ∈ Ico (0 : ℝ) T) :
    ‖G r - G t‖ = periodicDatumEnergyDistance m u t r := by
  have hs' : ContDiffOn ℝ ∞ (fun z : SpaceTime ↦ u z - u (t, z.2))
      (Ico (0 : ℝ) T ×ˢ (univ : Set Space)) := by
    have htSlice : ContDiff ℝ ∞ (fun x : Space ↦ u (t, x)) :=
      hs.comp_contDiff (contDiff_const.prodMk contDiff_id)
        (fun x ↦ ⟨ht, mem_univ x⟩)
    exact hs.sub (htSlice.comp contDiff_snd).contDiffOn
  change ‖(G r - G t).1‖ = _
  unfold periodicDatumEnergyDistance
  rw [PiLp.norm_eq_of_L2]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hsliceDiff : ContDiff ℝ ∞ (fun x : Space ↦ u (r, x) - u (t, x)) := by
    simpa [Function.comp_def] using
      hs'.comp_contDiff (contDiff_const.prodMk contDiff_id)
        (fun x ↦ ⟨hr, mem_univ x⟩)
  rw [norm_scalar_datum_nat m hsliceDiff
    (datum_sub (hG r hr) (hG t ht)) i,
    Real.sq_sqrt (periodicIntegerEnergy_nonneg m _)]

/-- The physical energy expression controlling datum distance is continuous
on the half-open slab. -/
theorem continuousOn_periodicDatum_energyDistance (m : ℕ)
    {u : SpaceTimeField} {T t : ℝ}
    (hs : ContDiffOn ℝ ∞ u (Ico (0 : ℝ) T ×ˢ (univ : Set Space)))
    (ht : t ∈ Ico (0 : ℝ) T) :
    ContinuousOn (periodicDatumEnergyDistance m u t) (Ico (0 : ℝ) T) := by
  have htSlice : ContDiff ℝ ∞ (fun x : Space ↦ u (t, x)) :=
    hs.comp_contDiff (contDiff_const.prodMk contDiff_id)
      (fun x ↦ ⟨ht, mem_univ x⟩)
  have hs' : ContDiffOn ℝ ∞ (fun z : SpaceTime ↦ u z - u (t, z.2))
      (Ico (0 : ℝ) T ×ˢ (univ : Set Space)) :=
    hs.sub (htSlice.comp contDiff_snd).contDiffOn
  unfold periodicDatumEnergyDistance
  apply Real.continuous_sqrt.comp_continuousOn
  exact continuousOn_finsetSum Finset.univ (fun i _ ↦
    continuousOn_periodicIntegerEnergy_time_Ico m
      (Complex.ofRealCLM.contDiff.comp_contDiffOn
        ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp_contDiffOn hs')))

-- The coefficient-norm expansion needs bounded elaboration headroom.
set_option maxHeartbeats 400000 in
/-- Datum paths selected from smooth periodic slices are continuous on the
same half-open slab. -/
theorem continuousOn_periodicDatum_path_of_slab (m : ℕ) {u : SpaceTimeField}
    {T : ℝ}
    (hs : ContDiffOn ℝ ∞ u (Ico (0 : ℝ) T ×ˢ (univ : Set Space)))
    (G : ℝ → PeriodicSobolev (m : ℝ))
    (hG : ∀ t ∈ Ico (0 : ℝ) T,
      IsPeriodicDatum (m : ℝ) (fun x ↦ u (t, x)) (G t)) :
    ContinuousOn G (Ico (0 : ℝ) T) := by
  intro t ht
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hcSum := continuousOn_periodicDatum_energyDistance m hs ht
  have hlim := hcSum t ht
  have hzero : periodicDatumEnergyDistance m u t t = 0 := by
    rw [← periodicDatum_path_norm_sub m hs G hG ht ht, sub_self, norm_zero]
  have hlim0 : Tendsto (periodicDatumEnergyDistance m u t)
      (𝓝[Ico (0 : ℝ) T] t) (𝓝 0) := by
    simpa only [ContinuousWithinAt, hzero] using hlim
  apply hlim0.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (periodicDatum_path_norm_sub m hs G hG ht hr).symm

/-- The Sobolev datum field required by `ofFlow`, derived from slab smoothness
and spatial periodicity. -/
theorem flow_sobolev {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (U : Flow ν a f T) :
    ∀ m : ℕ, ∃ G : ℝ → PeriodicSobolev (m : ℝ),
      ContinuousOn G (Ico (0 : ℝ) T) ∧
        ∀ t ∈ Ico (0 : ℝ) T,
          IsPeriodicDatum (m : ℝ) (fun x ↦ U.velocity (t, x)) (G t) := by
  classical
  intro m
  have hex (t : ℝ) (ht : t ∈ Ico (0 : ℝ) T) :
      ∃ A : PeriodicSobolev (m : ℝ),
        IsPeriodicDatum (m : ℝ) (fun x ↦ U.velocity (t, x)) A := by
    apply exists_periodicDatum_smooth
    · exact U.velocity_smooth.comp_contDiff (contDiff_const.prodMk contDiff_id)
        (fun x ↦ ⟨ht, mem_univ x⟩)
    · exact U.velocity_periodic t ht
  let G : ℝ → PeriodicSobolev (m : ℝ) := fun t ↦
    if ht : t ∈ Ico (0 : ℝ) T then (hex t ht).choose else 0
  have hG : ∀ t ∈ Ico (0 : ℝ) T,
      IsPeriodicDatum (m : ℝ) (fun x ↦ U.velocity (t, x)) (G t) := by
    intro t ht
    simp only [G]
    rw [dite_eq_left ht]
    exact (hex t ht).choose_spec
  exact ⟨G, continuousOn_periodicDatum_path_of_slab m U.velocity_smooth G hG, hG⟩

/-- Smooth pressure slices have square-integrable gradients on the compact
torus. -/
theorem flow_pressure_gradient {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (U : Flow ν a f T) :
    ∀ t ∈ Ico (0 : ℝ) T,
      MemLp (NSFormalization.Section3.T10.torusLift
        (fun x ↦ pressureGradient U.pressure t x)) 2
        NSFormalization.Section3.T10.periodicTorusMeasure := by
  intro t ht
  have hp : ContDiff ℝ ∞ (fun x : Space ↦ U.pressure (t, x)) :=
    U.pressure_smooth.comp_contDiff (contDiff_const.prodMk contDiff_id)
      (fun x ↦ ⟨ht, mem_univ x⟩)
  exact NSFormalization.Section3.T10.memLp_torusLift_vector
    (NavierStokes.PeriodicUniqueness.pressureGradient_contDiff hp).continuous 2

/-- Paper 1 cube normalization is exactly the T10 Haar pressure gauge. -/
theorem pressureGaugeT_of_isNormalized {ν T : ℝ} {a : SpatialField}
    {f : SpaceTimeField} (U : Flow ν a f T) (hU : IsNormalized U) :
    PressureGaugeT (Ico (0 : ℝ) T) U.pressure := by
  intro t ht
  rw [pressureMeanT, NSFormalization.Paper1.integral_torusLift]
  exact hU t ht

/-- Upgrade a normalized Paper 1 flow to the richer T10 solution structure. -/
def ofNormalizedFlow {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (U : Flow ν a f T) (hU : IsNormalized U) :
    ClassicalSolutionT ν a f T :=
  ofFlow U (flow_sobolev U) (flow_pressure_gradient U)
    (pressureGaugeT_of_isNormalized U hU)

/-- Normalize an arbitrary Paper 1 flow and upgrade it to `ClassicalSolutionT`. -/
def flowToClassical {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (U : Flow ν a f T) : ClassicalSolutionT ν a f T :=
  ofNormalizedFlow (normalizedFlow U) (normalizedFlow_isNormalized U)

/-! ## Equality of the two supremal lifespans -/

/-- T10's maximal lifespan and Paper 1's flow lifespan are the same supremum. -/
theorem maximalLifespanT_eq_lifespan (ν : ℝ) (a : SpatialField)
    (f : SpaceTimeField) :
    maximalLifespanT ν a f = lifespan ν a f := by
  apply le_antisymm
  · unfold maximalLifespanT lifespan
    apply iSup_le
    intro S
    apply iSup_le
    rintro ⟨w⟩
    exact NSFormalization.Paper1.PeriodicLifespan.horizon_le_lifespan (toFlow w)
  · unfold lifespan maximalLifespanT
    apply iSup_le
    intro S
    apply iSup_le
    rintro ⟨U⟩
    exact le_iSup_of_le S (le_iSup_of_le
      (show Nonempty (ClassicalSolutionT ν a f S) from ⟨flowToClassical U⟩) le_rfl)

/-! ## Maximal existence and uniqueness -/

/-- The single residual input while U11 is absent: admissible data and force
have some positive-horizon T10 classical solution. -/
def PeriodicMaximalExistenceInput : Prop :=
  ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∃ T : ℝ, 0 < T ∧ Nonempty (ClassicalSolutionT ν a f T)

/-- The `PeriodicLocalTheoryAPI.exists_maximal` field, verbatim, conditional
only on the named local-existence input. -/
theorem exists_maximal (H : PeriodicMaximalExistenceInput) :
    ∀ (ν : ℝ), 0 < ν →
      ∀ (a : SpatialField), a ∈ initialClassT →
        ∀ (f : SpaceTimeField), f ∈ forceClassT →
          ∃ (u : SpaceTimeField) (p : SpaceTimeScalar),
            IsMaximalPeriodicSolution ν a f u p := by
  intro ν hν a ha f hf
  obtain ⟨T, _hT, ⟨w₀⟩⟩ := H ν hν a ha f hf
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

/-- The `PeriodicLocalTheoryAPI.maximal_unique` field, verbatim. -/
theorem maximal_unique : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (u₁ u₂ : SpaceTimeField) (p₁ p₂ : SpaceTimeScalar),
          IsMaximalPeriodicSolution ν a f u₁ p₁ →
          IsMaximalPeriodicSolution ν a f u₂ p₂ →
            ∀ t : ℝ, 0 ≤ t →
              ENNReal.ofReal t < maximalLifespanT ν a f →
                ∀ x : Space,
                  u₁ (t, x) = u₂ (t, x) ∧ p₁ (t, x) = p₂ (t, x) := by
  intro ν hν a ha f hf u₁ u₂ p₁ p₂ hM₁ hM₂ t ht htlife x
  have hex : ∃ S : ℝ, t < S ∧ Nonempty (ClassicalSolutionT ν a f S) := by
    by_contra hn
    have hle : maximalLifespanT ν a f ≤ ENNReal.ofReal t := by
      unfold maximalLifespanT
      apply iSup_le
      intro S
      apply iSup_le
      intro hS
      have hSt : S ≤ t := by
        apply le_of_not_gt
        intro htS
        exact hn ⟨S, htS, hS⟩
      exact ENNReal.ofReal_le_ofReal hSt
    exact (not_le_of_gt htlife) hle
  obtain ⟨S', htS', ⟨w'⟩⟩ := hex
  let S : ℝ := (t + S') / 2
  have hSpos : 0 < S := by dsimp [S]; linarith
  have htS : t < S := by dsimp [S]; linarith
  have hSS' : S < S' := by dsimp [S]; linarith
  have hShor : ENNReal.ofReal S < ENNReal.ofReal S' :=
    (ENNReal.ofReal_lt_ofReal_iff w'.horizon_pos).mpr hSS'
  have hSmax : ENNReal.ofReal S < maximalLifespanT ν a f :=
    hShor.trans_le (le_iSup_of_le S' (le_iSup_of_le ⟨w'⟩ le_rfl))
  obtain ⟨w₁, hw₁u, hw₁p⟩ := hM₁.2 S hSpos hSmax
  obtain ⟨w₂, hw₂u, hw₂p⟩ := hM₂.2 S hSpos hSmax
  have htIco : t ∈ Ico (0 : ℝ) (min S S) := by simpa using And.intro ht htS
  constructor
  · have h := velocity_unique ν hν a ha f hf S S w₁ w₂ t htIco x
    simpa only [hw₁u, hw₂u] using h
  · have h := pressure_unique ν hν a ha f hf S S w₁ w₂ t htIco x
    simpa only [hw₁p, hw₂p] using h

end NSFormalization.Section3.T11
