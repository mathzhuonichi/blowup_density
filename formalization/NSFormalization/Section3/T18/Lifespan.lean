import NSFormalization.Section3.T18.Momentum
import NSFormalization.Section3.T11.ExtendsBeyond
import NSFormalization.Section4.R42.BlowupEssSup

/-! T18 U8: the inserted triple is a full-horizon classical torus solution,
its speed blows up at `T` both pointwise and in `L^∞`, its maximal lifespan is
exactly `T`, and it is the maximal periodic solution of its own data. -/

noncomputable section
namespace NSFormalization.Section3.T18
open Set MeasureTheory Filter
open scoped ContDiff ENNReal Topology
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Section3.T15
open NSFormalization.Section3.T16
open NSFormalization.Section3.T11 (velocity_unique exists_periodicDatum_smooth
  continuousOn_periodicDatum_path_of_slab lifespan_ge_of_horizon)
open NSFormalization.Section4.A02 (SpaceTimeField SpaceTimeScalar SpatialField)

/-! ## 1. The two pressure fields that `ClassicalSolutionT` still asks for -/

/-- The un-normalized pressure sum of `eq:insertion`. -/
def rawPressure (data : InsertionData) (ε : ℝ) : SpaceTimeScalar :=
  fun z ↦ data.reference.pressure z +
    periodizedScaledPressure data.packetPressure data.place.x₀ data.place.T ε z

theorem pressure_eq_normalize (data : InsertionData) (ε : ℝ) :
    pressure data ε = normalizePressureT (rawPressure data ε) := rfl

/-- Reference pressure slices are Haar-integrable because they are smooth. -/
theorem reference_pressureSlice_integrable (data : InsertionData) {t : ℝ}
    (ht : t ∈ Ico (0 : ℝ) (data.place.T + data.δ)) :
    Integrable (torusLift (fun x ↦ data.reference.pressure (t, x))) periodicTorusMeasure := by
  have hr : ContDiff ℝ ∞ (fun x : Space ↦ data.reference.pressure (t, x)) :=
    slice_contDiff data.reference.pressure_smooth ht
  exact (NSFormalization.Paper1.memLp_torusLift
    (Complex.continuous_ofReal.comp hr.continuous) 1).re.integrable (by norm_num)

/-- Both summands of the inserted pressure are Haar-integrable on `[0,T)`. -/
theorem rawPressureSlice_integrable (data : InsertionData) {ε : ℝ}
    (hε : ε ∈ Ioc (0 : ℝ) (ε₀ data)) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) data.place.T) :
    Integrable (torusLift (fun x ↦ rawPressure data ε (t, x))) periodicTorusMeasure :=
  (reference_pressureSlice_integrable data (reference_time data ht)).add
    (data.scaling.pressureSlice_integrable ε (scaling_range data hε) t ht)

/-- The mean-zero gauge is honest wherever the slices are integrable. -/
theorem pressureGaugeT_normalize {q : SpaceTimeScalar} {I : Set ℝ}
    (hq : ∀ t ∈ I, Integrable (torusLift (fun x ↦ q (t, x))) periodicTorusMeasure) :
    PressureGaugeT I (normalizePressureT q) := by
  intro t ht
  have hconst : Integrable (fun _ : PeriodicTorus ↦ pressureMeanT q t) periodicTorusMeasure :=
    integrable_const _
  have key : (∫ y : PeriodicTorus,
        torusLift (fun x ↦ normalizePressureT q (t, x)) y ∂periodicTorusMeasure)
      = (∫ y : PeriodicTorus, torusLift (fun x ↦ q (t, x)) y ∂periodicTorusMeasure)
        - (∫ _y : PeriodicTorus, pressureMeanT q t ∂periodicTorusMeasure) :=
    integral_sub (hq t ht) hconst
  show (∫ y : PeriodicTorus,
      torusLift (fun x ↦ normalizePressureT q (t, x)) y ∂periodicTorusMeasure) = 0
  rw [key, integral_const]
  simp [pressureMeanT]

/-- The gauge shift is spatially constant, so it preserves periodicity. -/
theorem isPeriodicOn_normalizePressureT {q : SpaceTimeScalar} {I : Set ℝ}
    (hq : IsPeriodicOn I q) : IsPeriodicOn I (normalizePressureT q) := by
  intro t ht x i
  show q (t, x + coordinateVector i) - pressureMeanT q t = q (t, x) - pressureMeanT q t
  rw [hq t ht x i]

/-- `03-torus.tex:314,318-320`: the inserted pressure has unit spatial periods
on `[0,T)`. -/
theorem pressure_periodic (data : InsertionData) : ∀ ε ∈ Ioc (0 : ℝ) (ε₀ data),
    IsPeriodicOn (Ico (0 : ℝ) data.place.T) (pressure data ε) := by
  intro ε hε
  obtain ⟨S, _, hp⟩ := data.scaling.solution ε (scaling_range data hε)
  have hpacket : IsPeriodicOn (Ico (0 : ℝ) data.place.T)
      (periodizedScaledPressure data.packetPressure data.place.x₀ data.place.T ε) := by
    intro t ht x i
    have h := S.pressure_periodic t ht x i
    rw [hp] at h
    have h' : periodizedScaledPressure data.packetPressure data.place.x₀ data.place.T ε
          (t, x + coordinateVector i)
        - pressureMeanT
            (periodizedScaledPressure data.packetPressure data.place.x₀ data.place.T ε) t
        = periodizedScaledPressure data.packetPressure data.place.x₀ data.place.T ε (t, x)
        - pressureMeanT
            (periodizedScaledPressure data.packetPressure data.place.x₀ data.place.T ε) t := h
    exact sub_left_injective h'
  rw [pressure_eq_normalize]
  refine isPeriodicOn_normalizePressureT ?_
  intro t ht x i
  show data.reference.pressure (t, x + coordinateVector i) +
      periodizedScaledPressure data.packetPressure data.place.x₀ data.place.T ε
        (t, x + coordinateVector i)
    = data.reference.pressure (t, x) +
      periodizedScaledPressure data.packetPressure data.place.x₀ data.place.T ε (t, x)
  rw [data.reference.pressure_periodic t (reference_time data ht) x i, hpacket t ht x i]

/-- `03-torus.tex:318-320`: the inserted pressure is in the zero-mean gauge. -/
theorem pressure_gauge (data : InsertionData) : ∀ ε ∈ Ioc (0 : ℝ) (ε₀ data),
    PressureGaugeT (Ico (0 : ℝ) data.place.T) (pressure data ε) := by
  intro ε hε
  rw [pressure_eq_normalize]
  exact pressureGaugeT_normalize (fun _ ht ↦ rawPressureSlice_integrable data hε ht)

/-! ## 2. The two analytic fields of `ClassicalSolutionT` -/

/-- Every integer Sobolev order of the inserted velocity has a datum path that
is continuous on the whole solution slab. -/
theorem sobolev_path (data : InsertionData) {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) (ε₀ data)) :
    ∀ m : ℕ, ∃ G : ℝ → PeriodicSobolev (m : ℝ),
      ContinuousOn G (Ico (0 : ℝ) data.place.T) ∧
        ∀ t ∈ Ico (0 : ℝ) data.place.T,
          IsPeriodicDatum (m : ℝ) (fun x ↦ velocity data ε (t, x)) (G t) := by
  classical
  intro m
  have hsm := velocity_smooth data ε hε
  have hper := velocity_periodic data ε hε
  have hex : ∀ t ∈ Ico (0 : ℝ) data.place.T,
      ∃ A : PeriodicSobolev (m : ℝ),
        IsPeriodicDatum (m : ℝ) (fun x ↦ velocity data ε (t, x)) A := fun t ht ↦
    exists_periodicDatum_smooth (m : ℝ) (slice_contDiff hsm ht) (fun x i ↦ hper t ht x i)
  let G : ℝ → PeriodicSobolev (m : ℝ) := fun t ↦
    if ht : t ∈ Ico (0 : ℝ) data.place.T then (hex t ht).choose else 0
  have hG : ∀ t ∈ Ico (0 : ℝ) data.place.T,
      IsPeriodicDatum (m : ℝ) (fun x ↦ velocity data ε (t, x)) (G t) := by
    intro t ht
    simp only [G]
    rw [dite_eq_left ht]
    exact (hex t ht).choose_spec
  exact ⟨G, continuousOn_periodicDatum_path_of_slab m hsm G hG, hG⟩

/-- Smooth pressure slices have square-integrable gradients on the torus. -/
theorem pressure_gradient_memLp (data : InsertionData) {ε : ℝ}
    (hε : ε ∈ Ioc (0 : ℝ) (ε₀ data)) :
    ∀ t ∈ Ico (0 : ℝ) data.place.T,
      MemLp (torusLift (fun x ↦ pressureGradient (pressure data ε) t x)) 2
        periodicTorusMeasure := by
  intro t ht
  have hp : ContDiff ℝ ∞ (fun x : Space ↦ pressure data ε (t, x)) :=
    slice_contDiff (pressure_smooth data ε hε) ht
  exact memLp_torusLift_vector
    (NavierStokes.PeriodicUniqueness.pressureGradient_contDiff hp).continuous 2

/-! ## 3. (a) The inserted triple as a classical solution on the full horizon -/

/-- `03-torus.tex:338,344-345`: the inserted pair is a classical torus solution
on all of `[0,T)`. -/
def insertedSolution (data : InsertionData) {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) (ε₀ data)) :
    ClassicalSolutionT data.ν data.a (force data ε) data.place.T where
  velocity := velocity data ε
  pressure := pressure data ε
  horizon_pos := data.place.time_pos
  velocity_smooth := velocity_smooth data ε hε
  pressure_smooth := pressure_smooth data ε hε
  initial := initial data ε hε
  divergence := incompressible data ε hε
  momentum := momentum data ε hε
  sobolev := sobolev_path data hε
  pressure_gradient := pressure_gradient_memLp data hε
  velocity_periodic := velocity_periodic data ε hε
  pressure_periodic := pressure_periodic data ε hε
  pressure_gauge := pressure_gauge data ε hε

/-- `research/T18/Spec.lean:1796`: the `solution` field. -/
theorem solution (data : InsertionData) : ∀ ε ∈ Ioc (0 : ℝ) (ε₀ data),
    ∃ w : ClassicalSolutionT data.ν data.a (force data ε) data.place.T,
      w.velocity = velocity data ε ∧ w.pressure = pressure data ε :=
  fun ε hε ↦ ⟨insertedSolution data (ε := ε) hε, rfl, rfl⟩

/-! ## 4. (b)(c) Blow-up of the inserted speed, pointwise and in `L^∞` -/

/-- `research/T18/Spec.lean:1818`: on the active support the inserted velocity
*is* the periodized packet, because `correction_cancels` removes the corrected
background there; so the packet's pointwise blow-up transfers verbatim. -/
theorem blowup (data : InsertionData) : ∀ ε ∈ Ioc (0 : ℝ) (ε₀ data),
    NSFormalization.Source.PacketScaling.SpeedUnboundedAt data.place.T (velocity data ε) := by
  intro ε hε M hM δ hδ
  obtain ⟨t, x, ht, htδ, hMx⟩ :=
    data.scaling.unboundedSpeed ε (scaling_range data hε) M hM δ hδ
  refine ⟨t, x, ht, htδ, ?_⟩
  have hne : periodizedScaledVelocity data.packetVelocity data.place.x₀ data.place.T ε (t, x)
      ≠ 0 := by
    intro h
    rw [h, norm_zero] at hMx
    exact absurd hMx (not_lt.mpr hM.le)
  have hstart : data.place.T - ε ^ 2 ≤ t := by
    by_contra hlt
    exact hne (congrFun (packet_slice_zero data (le_of_lt (not_le.mp hlt))) x)
  obtain ⟨O, _, hsub, hzero⟩ :=
    data.correction.potential.correction_cancels ε (correction_range data hε) t
      ⟨hstart, ht.2⟩
  have hxO : x ∈ O := hsub (subset_tsupport _ hne)
  have heq : velocity data ε (t, x) =
      periodizedScaledVelocity data.packetVelocity data.place.x₀ data.place.T ε (t, x) := by
    have hsplit : velocity data ε (t, x)
        = correctedBackground data.reference.velocity data.D.correction ε (t, x)
          + periodizedScaledVelocity data.packetVelocity data.place.x₀ data.place.T ε (t, x) :=
      rfl
    rw [hsplit, hzero x hxO, zero_add]
  rw [heq]
  exact hMx

/-- `research/T18/Spec.lean:1825`: the essential-supremum form of the same
display, `limsup_{t↑T} ‖u_ε(t)‖_{L^∞} = ⊤`. -/
theorem blowup_limsup (data : InsertionData) : ∀ ε ∈ Ioc (0 : ℝ) (ε₀ data),
    NSFormalization.Section4.A02.limsupLeft data.place.T
        (fun t ↦ NSFormalization.Section4.A02.speedENorm
          (fun x : Space ↦ velocity data ε (t, x))) = ⊤ := fun ε hε ↦
  NSFormalization.Section4.R42.limsupLeft_speedENorm_eq_top (blowup data ε hε)
    (NSFormalization.Section4.R42.continuous_slice_of_velocity_smooth
      (velocity_smooth data ε hε))

/-! ## 5. (d) The maximal lifespan is exactly `T` -/

/-- Every spatial point is an integer lattice translate of a point of the closed
unit cube. -/
theorem exists_sub_latticeVector_mem_fundamentalCube (x : Space) :
    ∃ n : PeriodicFrequency,
      x - NSFormalization.Section3.T13.latticeVector n ∈
        NSFormalization.Section3.T13.fundamentalCube := by
  refine ⟨fun i ↦ ⌊x i⌋, fun i ↦ ?_⟩
  have h : (x - NSFormalization.Section3.T13.latticeVector (fun i ↦ ⌊x i⌋)) i
      = Int.fract (x i) := rfl
  rw [h]
  exact ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩

/-- The closed unit cube is compact. -/
theorem isCompact_fundamentalCube :
    IsCompact (NSFormalization.Section3.T13.fundamentalCube) := by
  refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : Space) 2)
    NSFormalization.Section3.T13.isClosed_fundamentalCube (fun x hx ↦ ?_)
  have hs : ‖x‖ ^ 2 = ∑ i : Fin 3, ‖x i‖ ^ 2 := PiLp.norm_sq_eq_of_L2 _ x
  have hsum : (∑ i : Fin 3, ‖x i‖ ^ 2) ≤ 3 := by
    calc (∑ i : Fin 3, ‖x i‖ ^ 2) ≤ ∑ _i : Fin 3, (1 : ℝ) := by
          refine Finset.sum_le_sum (fun i _ ↦ ?_)
          rw [Real.norm_eq_abs, abs_of_nonneg (hx i).1]
          nlinarith [(hx i).1, (hx i).2]
      _ = 3 := by simp
  have hx0 : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
  simp only [Metric.mem_closedBall, dist_zero_right]
  nlinarith [hs, hsum, hx0]

/-- A slab-smooth unit-periodic spacetime field is bounded on every compact time
window strictly inside its slab: continuity bounds it on the compact product of
that window with the unit cube, and periodicity carries the bound to all of
space. -/
theorem exists_speed_bound {T₀ T : ℝ} {u : SpaceTimeField}
    (hu : ContDiffOn ℝ ∞ u (Ico (0 : ℝ) T ×ˢ (univ : Set Space)))
    (hper : IsPeriodicOn (Ico (0 : ℝ) T) u) (hT : T₀ < T) :
    ∃ C : ℝ, ∀ t ∈ Icc (0 : ℝ) T₀, ∀ x : Space, ‖u (t, x)‖ ≤ C := by
  have hK : IsCompact (Icc (0 : ℝ) T₀ ×ˢ NSFormalization.Section3.T13.fundamentalCube) :=
    isCompact_Icc.prod isCompact_fundamentalCube
  have hsub : Icc (0 : ℝ) T₀ ×ˢ NSFormalization.Section3.T13.fundamentalCube
      ⊆ Ico (0 : ℝ) T ×ˢ (univ : Set Space) :=
    fun z hz ↦ ⟨⟨hz.1.1, lt_of_le_of_lt hz.1.2 hT⟩, mem_univ _⟩
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hu.continuousOn.mono hsub)
  refine ⟨C, fun t ht x ↦ ?_⟩
  obtain ⟨n, hn⟩ := exists_sub_latticeVector_mem_fundamentalCube x
  have hslice : IsPeriodicSpatial (fun y : Space ↦ u (t, y)) :=
    fun y i ↦ hper t ⟨ht.1, lt_of_le_of_lt ht.2 hT⟩ y i
  have hshift : u (t, x) = u (t, x - NSFormalization.Section3.T13.latticeVector n) := by
    have h := NSFormalization.Section3.T13.periodic_latticeVector hslice
      (x - NSFormalization.Section3.T13.latticeVector n) n
    simpa using h
  rw [hshift]
  exact hC _ ⟨ht, hn⟩

/-- `03-torus.tex:291,344-345`: no classical solution reaches past `T`, because
a longer one would agree with `u_ε` below `T` by uniqueness and would then be
bounded there, contradicting the blow-up. -/
theorem lifespan_le (data : InsertionData) {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) (ε₀ data)) :
    maximalLifespanT data.ν data.a (force data ε) ≤ ENNReal.ofReal data.place.T := by
  by_contra hcon
  rw [not_le] at hcon
  have hcon' : ENNReal.ofReal data.place.T <
      ⨆ S : ℝ, ⨆ _ : Nonempty (ClassicalSolutionT data.ν data.a (force data ε) S),
        ENNReal.ofReal S := hcon
  obtain ⟨S, hS⟩ := lt_iSup_iff.mp hcon'
  obtain ⟨hne, hTS⟩ := lt_iSup_iff.mp hS
  obtain ⟨w⟩ := hne
  have hTSr : data.place.T < S :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg data.place.time_pos.le).mp hTS
  obtain ⟨C, hC⟩ := exists_speed_bound w.velocity_smooth w.velocity_periodic hTSr
  have hCle : C ≤ max C 0 := le_max_left C 0
  have hmax0 : (0 : ℝ) ≤ max C 0 := le_max_right C 0
  have hMpos : 0 < max C 0 + 1 := by linarith
  obtain ⟨t, x, ht, -, hMx⟩ :=
    blowup data ε hε (max C 0 + 1) hMpos data.place.T data.place.time_pos
  have hagree : velocity data ε (t, x) = w.velocity (t, x) :=
    velocity_unique data.ν data.correction.viscosity_pos data.a data.ha
      (force data ε) (force_mem data ε hε) data.place.T S (insertedSolution data hε) w t
      ⟨ht.1.le, by rw [min_eq_left hTSr.le]; exact ht.2⟩ x
  have hbound : ‖w.velocity (t, x)‖ ≤ C := hC t ⟨ht.1.le, ht.2.le⟩ x
  rw [hagree] at hMx
  linarith

/-- `research/T18/Spec.lean:1812`: clause (i), `T_max^ν(a, g_ε) = T`. -/
theorem lifespan (data : InsertionData) : ∀ ε ∈ Ioc (0 : ℝ) (ε₀ data),
    maximalLifespanT data.ν data.a (force data ε) = ENNReal.ofReal data.place.T :=
  fun ε hε ↦ le_antisymm (lifespan_le data (ε := ε) hε)
    (lifespan_ge_of_horizon (insertedSolution data (ε := ε) hε))

/-! ## 6. (e) The inserted pair is the maximal periodic solution -/

/-- The same inserted fields restricted to any shorter positive horizon. -/
def insertedSolutionOn (data : InsertionData) {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) (ε₀ data))
    {S : ℝ} (hS : 0 < S) (hST : S ≤ data.place.T) :
    ClassicalSolutionT data.ν data.a (force data ε) S where
  velocity := velocity data ε
  pressure := pressure data ε
  horizon_pos := hS
  velocity_smooth := (velocity_smooth data ε hε).mono
    (prod_mono (Ico_subset_Ico le_rfl hST) (subset_refl _))
  pressure_smooth := (pressure_smooth data ε hε).mono
    (prod_mono (Ico_subset_Ico le_rfl hST) (subset_refl _))
  initial := initial data ε hε
  divergence := fun t ht x ↦
    incompressible data ε hε t (Ico_subset_Ico le_rfl hST ht) x
  momentum := fun t ht x ↦
    momentum data ε hε t ⟨ht.1, lt_of_lt_of_le ht.2 hST⟩ x
  sobolev := fun m ↦ by
    obtain ⟨G, hGc, hGd⟩ := sobolev_path data hε m
    exact ⟨G, hGc.mono (Ico_subset_Ico le_rfl hST),
      fun t ht ↦ hGd t (Ico_subset_Ico le_rfl hST ht)⟩
  pressure_gradient := fun t ht ↦
    pressure_gradient_memLp data hε t (Ico_subset_Ico le_rfl hST ht)
  velocity_periodic := fun t ht ↦
    velocity_periodic data ε hε t (Ico_subset_Ico le_rfl hST ht)
  pressure_periodic := fun t ht ↦
    pressure_periodic data ε hε t (Ico_subset_Ico le_rfl hST ht)
  pressure_gauge := fun t ht ↦
    pressure_gauge data ε hε t (Ico_subset_Ico le_rfl hST ht)

/-- `research/T18/Spec.lean:1806`: the inserted pair *is* the maximal periodic
solution of `(ν, a, g_ε)`. -/
theorem maximal (data : InsertionData) : ∀ ε ∈ Ioc (0 : ℝ) (ε₀ data),
    NSFormalization.Section3.T11.IsMaximalPeriodicSolution data.ν data.a (force data ε)
      (velocity data ε) (pressure data ε) := by
  intro ε hε
  refine ⟨?_, ?_⟩
  · rw [lifespan data ε hε]
    exact ENNReal.ofReal_pos.mpr data.place.time_pos
  · intro S hS hlt
    rw [lifespan data ε hε] at hlt
    have hST : S ≤ data.place.T :=
      le_of_lt ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hS.le).mp hlt)
    exact ⟨insertedSolutionOn data hε hS hST, rfl, rfl⟩

end NSFormalization.Section3.T18
