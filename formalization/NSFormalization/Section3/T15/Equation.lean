import NSFormalization.Section3.T15.SingleCopy

/-!
# T15 U8: the periodized momentum equation, divergence and initial datum

Uniform compact spatial support lies strictly inside the fundamental cube.
The vendor locally finite lattice family applied to its indicator gives a
neighbourhood on which every nonzero translate vanishes, even at cube faces.
A fixed lattice shift then gives one local copy at every spatial point.
Local congruence of Fréchet derivatives transports the entire residual,
including the nonlinear advection term and the second spatial derivatives.
Section 4 parabolic scaling preserves viscosity, and the pressure mean has
zero spatial derivative. No additional regularity assumptions are needed:
these congruence identities also hold for the totalized Fréchet derivative.
-/
noncomputable section
namespace NSFormalization.Section3.T15
open Set Filter Topology
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Section3.T13
open NSFormalization.Source
open NSFormalization.Source.PacketScaling
open scoped BigOperators

/-- Periodization preserves the entire pre-activation zero interval. -/
theorem periodized_velocity_early {u : VelocityField} {x₀ : Space} {T ε t : ℝ}
    (ht : t ≤ T - ε ^ 2) (x : Space) :
    periodizedScaledVelocity u x₀ T ε (t, x) = 0 := by
  change (∑' n : PeriodicFrequency, scaledVelocity u x₀ T ε
    (t, x - latticeVector n)) = 0
  simp only [scaledVelocity_slice_eq_zero ht, tsum_zero]

/-- The canonical zero initial datum, using the placement time margin. -/
theorem periodized_initial {u f : VelocityField} {p : PressureField} {K : Set Space}
    (place : PlacementData u p f K) :
    ∀ ε ∈ Ioc (0 : ℝ) place.ε₀, ∀ x : Space,
      periodizedScaledVelocity u place.x₀ place.T ε (0, x) = 0 := by
  intro ε hε x
  apply periodized_velocity_early
  nlinarith [place.eps_time ε hε, sq_nonneg ε]

/-- Subtraction of the spatial mean does not affect the pressure gradient. -/
theorem pressureGradient_normalizePressureT (p : PressureField) (t : ℝ) (x : Space) :
    pressureGradient (normalizePressureT p) t x = pressureGradient p t x := by
  unfold pressureGradient normalizePressureT
  simp only [fderiv_sub_const]

/-- Source times of presingular target points are below one. -/
theorem scaled_source_time_lt_one {ε T t : ℝ} (hε : 0 < ε) (ht : t < T) :
    (ε⁻¹) ^ 2 * (t - (T - ε ^ 2)) < 1 := by
  have hk : (0 : ℝ) < (ε⁻¹) ^ 2 := by positivity
  have hc : (ε⁻¹) ^ 2 * ε ^ 2 = 1 := by field_simp
  nlinarith [mul_lt_mul_of_pos_left (show t - (T - ε ^ 2) < ε ^ 2 by linarith) hk]

/-- Raw extension momentum transports at unchanged viscosity. -/
theorem scaled_momentum {ν ε T : ℝ} {u f : VelocityField} {p : PressureField}
    (hf : ∀ t : ℝ, t ≤ 0 → ∀ x : Space, f (t, x) = 0)
    (heq : ∀ t : ℝ, t < 1 → ∀ x : Space,
      NavierStokesR3.ProblemStatement.navierStokesResidual ν
        (zeroPastField u) (zeroPastField p) t x = zeroPastField f (t, x))
    (hε : 0 < ε) (x₀ : Space) {t : ℝ} (ht : t < T) (x : Space) :
    NavierStokesR3.ProblemStatement.navierStokesResidual ν
      (scaledVelocity u x₀ T ε) (scaledPressure p x₀ T ε) t x =
      scaledForce f x₀ T ε (t, x) := by
  have hz : zeroPastField f = f := by
    funext ⟨s, y⟩
    by_cases hs : 0 < s
    · exact zeroPastField_of_pos f hs y
    · rw [zeroPastField_of_nonpos f (le_of_not_gt hs), hf s (le_of_not_gt hs)]
  have h := parabolic_equation ν ε⁻¹ (T - ε ^ 2) x₀
    (zeroPastField u) (zeroPastField p) (zeroPastField f) t x
    (heq _ (scaled_source_time_lt_one hε ht) _)
  rw [hz] at h
  exact h

/-- Raw extension incompressibility transports on the full presingular slab. -/
theorem scaled_divergence {ε T : ℝ} {u : VelocityField}
    (hdiv : ∀ t : ℝ, t < 1 → ∀ x : Space, spatialDivergence (zeroPastField u) t x = 0)
    (hε : 0 < ε) (x₀ : Space) {t : ℝ} (ht : t < T) (x : Space) :
    spatialDivergence (scaledVelocity u x₀ T ε) t x = 0 := by
  change spatialDivergence (dilateField ε⁻¹ ((ε⁻¹)^2) ε⁻¹ (T-ε^2) x₀
    (zeroPastField u)) t x = 0
  rw [dilate_divergence, hdiv _ (scaled_source_time_lt_one hε ht), mul_zero]

/-- Uniform closed support strictly inside the cube upgrades single-copy
agreement to agreement on a spacetime neighbourhood, including cube faces. -/
theorem periodize_eventuallyEq_of_closed_support
    {V : Type*} [NormedAddCommGroup V] {v : SpaceTime → V}
    {C : Set Space} (hC : IsClosed C) (hCQ : C ⊆ interior fundamentalCube)
    {T : ℝ} (hv : ∀ t < T, Function.support (fun x => v (t, x)) ⊆ C)
    {t : ℝ} (ht : t < T) {x : Space} (hx : x ∈ fundamentalCube) :
    NavierStokes.PeriodicLocalization.periodize v =ᶠ[𝓝 (t, x)] v := by
  classical
  let g : Space → ℝ := C.indicator (fun _ => 1)
  have hg : Function.support g = C := by
    ext y
    by_cases hy : y ∈ C <;> simp [g, hy]
  have hgs : tsupport g ⊆ interior fundamentalCube := by
    rw [tsupport, hg, hC.closure_eq]
    exact hCQ
  let G : SpaceTime → ℝ := fun z => g z.2
  have hclosed : ∀ n : PeriodicFrequency,
      IsClosed (Function.support (NavierStokes.PeriodicLocalization.translate G n)) := by
    intro n
    have he : Function.support (NavierStokes.PeriodicLocalization.translate G n) =
        (fun z : SpaceTime => z.2 - latticeVector n) ⁻¹' C := by
      ext z
      change g (z.2 - latticeVector n) ≠ 0 ↔ _
      rw [← Function.mem_support, hg]
      rfl
    rw [he]
    exact hC.preimage (by fun_prop)
  have hloc := NavierStokes.PeriodicLocalization.locallyFinite_support_translate
    (supportedInCube_of_tsupport_subset_interior hgs)
  have hn := hloc.iInter_compl_mem_nhds hclosed (t, x)
  have htime : ∀ᶠ z : SpaceTime in 𝓝 (t, x), z.1 < T :=
    (isOpen_lt continuous_fst continuous_const).mem_nhds ht
  filter_upwards [hn, htime] with z hz hzt
  change (∑' n : PeriodicFrequency, v (z.1, z.2 - latticeVector n)) = v z
  have hzero : ∀ n : PeriodicFrequency, n ≠ 0 →
      v (z.1, z.2 - latticeVector n) = 0 := by
    intro n hnzero
    have hnot : (t, x) ∉ Function.support
        (NavierStokes.PeriodicLocalization.translate G n) := by
      change ¬ g (x - latticeVector n) ≠ 0
      simp only [lattice_term_eq_zero_of_mem_cube hgs hx hnzero, ne_eq, not_true_eq_false, not_false_eq_true]
    have hznot := mem_iInter₂.mp hz n hnot
    by_contra hne
    have hmem := hv z.1 hzt hne
    have hgval : g (z.2 - latticeVector n) = 1 := by
      exact indicator_of_mem hmem _
    exact hznot (by change g (z.2 - latticeVector n) ≠ 0; rw [hgval]; norm_num)
  simpa only [latticeVector_zero, sub_zero] using
    (tsum_eq_single (0 : PeriodicFrequency) hzero)

/-- The residual, including both spatial derivatives in its Laplacian, is
local in the spacetime germ. No smoothness assumption is needed for congruence. -/
theorem residual_eq_of_eventuallyEq {u v : VelocityField} {p q : PressureField}
    {t : ℝ} {x : Space} (hu : u =ᶠ[𝓝 (t, x)] v) (hp : p =ᶠ[𝓝 (t, x)] q)
    (ν : ℝ) :
    NavierStokesR3.ProblemStatement.navierStokesResidual ν u p t x =
      NavierStokesR3.ProblemStatement.navierStokesResidual ν v q t x := by
  have hs : (fun y => u (t, y)) =ᶠ[𝓝 x] (fun y => v (t, y)) := hu.comp_tendsto (continuous_const.prodMk continuous_id).continuousAt
  have hp' : (fun y => p (t, y)) =ᶠ[𝓝 x] (fun y => q (t, y)) := hp.comp_tendsto (continuous_const.prodMk continuous_id).continuousAt
  have ht : (fun s => u (s, x)) =ᶠ[𝓝 t] (fun s => v (s, x)) := hu.comp_tendsto (continuous_id.prodMk continuous_const).continuousAt
  have hd : spatialDerivative u t x = spatialDerivative v t x := hs.fderiv_eq
  have hl : spatialLaplacian u t x = spatialLaplacian v t x := by
    unfold spatialLaplacian
    apply Finset.sum_congr rfl
    intro i _
    have he : (fun y => spatialDerivative u t y (coordinateVector i)) =ᶠ[𝓝 x]
        (fun y => spatialDerivative v t y (coordinateVector i)) :=
      hs.fderiv.mono (fun _ h => congrArg (fun A : Space →L[ℝ] Space => A (coordinateVector i)) h)
    rw [he.fderiv_eq]
  simp only [NavierStokesR3.ProblemStatement.navierStokesResidual,
    temporalDerivative, ht.fderiv_eq, advection, hd, hu.eq_of_nhds,
    hl, pressureGradient, hp'.fderiv_eq]

/-- Divergence likewise depends only on a spacetime neighbourhood. -/
theorem divergence_eq_of_eventuallyEq {u v : VelocityField} {t : ℝ} {x : Space}
    (hu : u =ᶠ[𝓝 (t, x)] v) : spatialDivergence u t x = spatialDivergence v t x := by
  have hs : (fun y => u (t, y)) =ᶠ[𝓝 x] (fun y => v (t, y)) := hu.comp_tendsto (continuous_const.prodMk continuous_id).continuousAt
  simp only [spatialDivergence, spatialDerivative, hs.fderiv_eq]

/-- Move an arbitrary spatial point into the closed fundamental cube. -/
theorem floor_representative_mem_cube (x : Space) :
    x - latticeVector (fun i => ⌊x i⌋) ∈ fundamentalCube := by
  intro i
  change 0 ≤ x i - (⌊x i⌋ : ℝ) ∧ x i - (⌊x i⌋ : ℝ) ≤ 1
  exact ⟨sub_nonneg.mpr (Int.floor_le _), (by linarith [Int.lt_floor_add_one (x i)])⟩

/-- Periodization is invariant under subtraction of a lattice vector. -/
theorem periodize_sub_lattice {V : Type*} [NormedAddCommGroup V]
    (v : SpaceTime → V) (t : ℝ) (x : Space) (n : PeriodicFrequency) :
    NavierStokes.PeriodicLocalization.periodize v (t, x - latticeVector n) =
      NavierStokes.PeriodicLocalization.periodize v (t, x) := by
  have h := NavierStokes.PeriodicLocalization.periodize_add_lattice v t
    (x - latticeVector n) n
  change NavierStokes.PeriodicLocalization.periodize v (t, x - latticeVector n + latticeVector n) = _ at h
  simpa only [sub_add_cancel] using h.symm

/-- At any point, the periodized field agrees locally with one fixed translate.
The lattice vector is fixed on this neighbourhood; no differentiation of a
choice of representative is involved. -/
theorem periodize_eventuallyEq_translate
    {V : Type*} [NormedAddCommGroup V] {v : SpaceTime → V}
    {C : Set Space} (hC : IsClosed C) (hCQ : C ⊆ interior fundamentalCube)
    {T : ℝ} (hv : ∀ t < T, Function.support (fun x => v (t, x)) ⊆ C)
    {t : ℝ} (ht : t < T) (x : Space) :
    NavierStokes.PeriodicLocalization.periodize v =ᶠ[𝓝 (t, x)]
      (fun z => v (z.1, z.2 - latticeVector (fun i => ⌊x i⌋))) := by
  let n : PeriodicFrequency := fun i => ⌊x i⌋
  have he := periodize_eventuallyEq_of_closed_support hC hCQ hv ht
    (floor_representative_mem_cube x)
  have hc : Tendsto (fun z : SpaceTime => (z.1, z.2 - latticeVector n))
      (𝓝 (t, x)) (𝓝 (t, x - latticeVector n)) :=
    (by fun_prop : Continuous (fun z : SpaceTime => (z.1, z.2 - latticeVector n))).continuousAt
  have h := he.comp_tendsto hc
  filter_upwards [h] with z hz
  exact (periodize_sub_lattice v z.1 z.2 n).symm.trans hz

/-- A fixed spatial translation preserves the physical residual. -/
theorem residual_translate (ν : ℝ) (u : VelocityField) (p : PressureField)
    (t : ℝ) (x a : Space) :
    NavierStokesR3.ProblemStatement.navierStokesResidual ν
      (fun z => u (z.1, z.2 - a)) (fun z => p (z.1, z.2 - a)) t x =
      NavierStokesR3.ProblemStatement.navierStokesResidual ν u p t (x - a) := by
  change Source.residual ν (fun z => u (z.1, z.2 - a))
    (fun z => p (z.1, z.2 - a)) t x = Source.residual ν u p t (x - a)
  have hu : parabolicVelocity 1 0 a u = (fun z => u (z.1, z.2 - a)) := by
    funext z; simp [parabolicVelocity, dilateField]
  have hp : parabolicPressure 1 0 a p = (fun z => p (z.1, z.2 - a)) := by
    funext z; simp [parabolicPressure, dilateField]
  have h := parabolic_residual ν 1 0 a u p t x
  rw [hu, hp] at h
  simpa only [one_pow, one_smul, one_mul, sub_zero] using h

/-- A fixed spatial translation preserves divergence. -/
theorem divergence_translate (u : VelocityField) (t : ℝ) (x a : Space) :
    spatialDivergence (fun z => u (z.1, z.2 - a)) t x =
      spatialDivergence u t (x - a) := by
  have hu : dilateField 1 1 1 0 a u = (fun z => u (z.1, z.2 - a)) := by
    funext z; simp [dilateField]
  have h := dilate_divergence 1 1 1 0 a u t x
  rw [hu] at h
  simpa only [one_smul, one_mul, sub_zero] using h

/-- The scaled velocity has one fixed local translate at every presingular point. -/
theorem periodized_velocity_local_translate
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hK : IsCompact K)
    (hu : ∀ t ∈ Ico (0 : ℝ) 1, tsupport (fun x : Space => u (t, x)) ⊆ K)
    (place : PlacementData u p f K) {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) place.ε₀)
    {t : ℝ} (ht : t < place.T) (x : Space) :
    periodizedScaledVelocity u place.x₀ place.T ε =ᶠ[𝓝 (t, x)]
      (fun z => scaledVelocity u place.x₀ place.T ε
        (z.1, z.2 - latticeVector (fun i => ⌊x i⌋))) := by
  apply periodize_eventuallyEq_translate (v := scaledVelocity u place.x₀ place.T ε)
    (affineImage_compact place.Kstar_compact).isClosed
    ((affineImage_subset_ball hε place.eps_space).trans
      (ball_subset_interior_cube place.chartBall_in_cube))
    (T := place.T) _ ht x
  intro s hs y hy
  exact scaledVelocity_tsupp_subset hε.1 hK hu place.carrier_subset hs
    (subset_tsupport _ hy)

/-- The raw scaled pressure has the same fixed local translate. -/
theorem periodized_pressure_local_translate
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hK : IsCompact K)
    (hp : ∀ t ∈ Ico (0 : ℝ) 1, tsupport (fun x : Space => p (t, x)) ⊆ K)
    (place : PlacementData u p f K) {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) place.ε₀)
    {t : ℝ} (ht : t < place.T) (x : Space) :
    periodizedScaledPressure p place.x₀ place.T ε =ᶠ[𝓝 (t, x)]
      (fun z => scaledPressure p place.x₀ place.T ε
        (z.1, z.2 - latticeVector (fun i => ⌊x i⌋))) := by
  apply periodize_eventuallyEq_translate (v := scaledPressure p place.x₀ place.T ε)
    (affineImage_compact place.Kstar_compact).isClosed
    ((affineImage_subset_ball hε place.eps_space).trans
      (ball_subset_interior_cube place.chartBall_in_cube))
    (T := place.T) _ ht x
  intro s hs y hy
  exact scaledPressure_tsupp_subset hε.1 hK hp place.carrier_subset hs
    (subset_tsupport _ hy)

/-- The canonical incompressibility field, including the initial time. -/
theorem periodized_divergence
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hK : IsCompact K)
    (hu : ∀ t ∈ Ico (0 : ℝ) 1, tsupport (fun x : Space => u (t, x)) ⊆ K)
    (hdiv : ∀ t : ℝ, t < 1 → ∀ x : Space, spatialDivergence (zeroPastField u) t x = 0)
    (place : PlacementData u p f K) :
    ∀ ε ∈ Ioc (0 : ℝ) place.ε₀, ∀ t ∈ Ico (0 : ℝ) place.T, ∀ x : Space,
      spatialDivergence (periodizedScaledVelocity u place.x₀ place.T ε) t x = 0 := by
  intro ε hε t ht x
  rw [divergence_eq_of_eventuallyEq (periodized_velocity_local_translate hK hu place hε ht.2 x),
    divergence_translate]
  exact scaled_divergence hdiv hε.1 place.x₀ ht.2 _

/-- The canonical momentum field, at the unchanged viscosity and with the
normalized pressure. All premises are raw packet support or equation clauses. -/
theorem periodized_momentum
    {ν : ℝ} {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hK : IsCompact K)
    (hu : ∀ t ∈ Ico (0 : ℝ) 1, tsupport (fun x : Space => u (t, x)) ⊆ K)
    (hp : ∀ t ∈ Ico (0 : ℝ) 1, tsupport (fun x : Space => p (t, x)) ⊆ K)
    (hf : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f)
    (hfzero : ∀ t : ℝ, t ≤ 0 → ∀ x : Space, f (t, x) = 0)
    (heq : ∀ t : ℝ, t < 1 → ∀ x : Space,
      NavierStokesR3.ProblemStatement.navierStokesResidual ν
        (zeroPastField u) (zeroPastField p) t x = zeroPastField f (t, x))
    (place : PlacementData u p f K) :
    ∀ ε ∈ Ioc (0 : ℝ) place.ε₀, ∀ t ∈ Ioo (0 : ℝ) place.T, ∀ x : Space,
      NavierStokesR3.ProblemStatement.navierStokesResidual ν
        (periodizedScaledVelocity u place.x₀ place.T ε)
        (normalizedScaledPressure p place.x₀ place.T ε) t x =
        periodizedScaledForce f place.x₀ place.T ε (t, x) := by
  intro ε hε t ht x
  have hg : NavierStokesR3.ProblemStatement.navierStokesResidual ν
      (periodizedScaledVelocity u place.x₀ place.T ε)
      (normalizedScaledPressure p place.x₀ place.T ε) t x =
      NavierStokesR3.ProblemStatement.navierStokesResidual ν
      (periodizedScaledVelocity u place.x₀ place.T ε)
      (periodizedScaledPressure p place.x₀ place.T ε) t x := by
    unfold NavierStokesR3.ProblemStatement.navierStokesResidual normalizedScaledPressure
    rw [pressureGradient_normalizePressureT]
  rw [hg, residual_eq_of_eventuallyEq
    (periodized_velocity_local_translate hK hu place hε ht.2 x)
    (periodized_pressure_local_translate hK hp place hε ht.2 x), residual_translate,
    scaled_momentum hfzero heq hε.1 place.x₀ ht.2]
  have hcopy := force_singleCopy hf place ε hε t
    (x - latticeVector (fun i => ⌊x i⌋)) (floor_representative_mem_cube x)
  exact hcopy.symm.trans (periodize_sub_lattice (scaledForce f place.x₀ place.T ε) t x _)

end NSFormalization.Section3.T15
