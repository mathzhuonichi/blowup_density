import NSFormalization.Section3.T24.MultipleOmegaComponents

/-! P5.2, `paper/revised/sections/03-torus.tex:523-526,533`:
"For i ≠ j, the supports of U_i and U_j are separated, so (U_i · ∇)U_j = 0.
The sum therefore satisfies the momentum equation exactly."
"Initial vanishing gives u(0)=0." "Hence u=0 on the boundary." -/
noncomputable section
namespace NSFormalization.Section3.T24
open NSFormalization.Section3.T23
open Set Filter MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10 NSFormalization.Section3.T13 NSFormalization.Section3.T15
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField SpaceTimeScalar)
open scoped ContDiff Topology BigOperators

/-- Finite sums preserve the open-neighborhood slab convention. -/
theorem smoothOnClosedSlab_finset_sum {ι V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (s : Finset ι) (F : ι → SpaceTime → V)
    {I : Set ℝ} {Ω : Set Space} (hF : ∀ i ∈ s, SmoothOnClosedSlab I Ω (F i)) :
    SmoothOnClosedSlab I Ω (fun z => ∑ i ∈ s, F i z) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using smoothOnClosedSlab_of_contDiff
      (contDiff_const : ContDiff ℝ ∞ (fun _ : SpaceTime => (0 : V))) I Ω
  | @insert a s ha ih =>
    simpa only [Finset.sum_insert ha] using
      (hF a (Finset.mem_insert_self a s)).add
        (ih (fun i hi => hF i (Finset.mem_insert_of_mem hi)))

/-- Compact positive temporal support survives finite sums. -/
theorem forceClassOmega_finset_sum {ι : Type*} (s : Finset ι) (F : ι → SpaceTimeField)
    {Ω : Set Space} (hF : ∀ i ∈ s, F i ∈ forceClassOmega Ω) :
    (fun z => ∑ i ∈ s, F i z) ∈ forceClassOmega Ω := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨fun T => ?_, ∅, isCompact_empty, empty_subset _, ?_⟩
    · simpa using smoothOnClosedSlab_of_contDiff
        (contDiff_const : ContDiff ℝ ∞ (fun _ : SpaceTime => (0 : Space))) (Icc 0 T) Ω
    · simp [tsupport]
  | @insert a s ha ih =>
    exact (show MemForceOmega Ω _ from by
      simpa only [Finset.sum_insert ha] using
        (hF a (Finset.mem_insert_self a s)).add
          (ih (fun i hi => hF i (Finset.mem_insert_of_mem hi))))

namespace RegionsOmegaData
variable {ν : ℝ} {u f : VelocityField} {p : PressureField}
  {K : Set Space} {M E : ℝ} (d : RegionsOmegaData ν u p f K M E)

def assembledVelocity : SpaceTimeField := finiteVelocitySum (fun j => (d.component j).velocity)
def assembledPressure : SpaceTimeScalar := finitePressureSum (fun j => (d.component j).pressure)
def assembledForce : SpaceTimeField :=
  finiteForceSum (fun j => scaledForce f (d.placement j).x₀ d.T (d.ε j))

theorem assembled_velocity_formula :
    d.assembledVelocity = finiteVelocitySum (fun j => (d.component j).velocity) := rfl
theorem assembled_pressure_formula :
    d.assembledPressure = finitePressureSum (fun j => (d.component j).pressure) := rfl
theorem assembled_force_formula : d.assembledForce =
    finiteForceSum (fun j => scaledForce f (d.placement j).x₀ d.T (d.ε j)) := rfl

theorem assembled_velocity_smooth : SmoothOnClosedSlab (Ico 0 d.T) d.Ω d.assembledVelocity :=
  smoothOnClosedSlab_finset_sum Finset.univ _ (fun j _ => (d.component j).velocity_smooth)
theorem assembled_pressure_smooth : SmoothOnClosedSlab (Ico 0 d.T) d.Ω d.assembledPressure :=
  smoothOnClosedSlab_finset_sum Finset.univ _ (fun j _ => (d.component j).pressure_smooth)

theorem rest : ∀ x : Space, d.assembledVelocity (0, x) = 0 := by
  intro x
  unfold assembledVelocity finiteVelocitySum
  exact Finset.sum_eq_zero (fun j _ => d.raw_initial j x)

theorem component_force_mem (j : Fin d.N) :
    scaledForce f (d.placement j).x₀ d.T (d.ε j) ∈ forceClassOmega d.Ω := by
  apply memForceOmega_of_compactPositiveTimeSupport
    (NSFormalization.Source.PacketScaling.parabolicForce_smooth d.force_smooth _ _ _)
  exact NSFormalization.Source.PacketScaling.parabolicForce_positive_support d.force_support
    (inv_pos.mpr (d.eps_admissible j).1) (by have := d.eps_time j; change 0 ≤ d.T - d.ε j ^ 2; linarith) _

theorem force_mem : d.assembledForce ∈ forceClassOmega d.Ω :=
  forceClassOmega_finset_sum Finset.univ _ (fun j _ => d.component_force_mem j)

theorem component_slice (j : Fin d.N) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) d.T) :
    ContDiff ℝ ∞ (fun x => (d.component j).velocity (t, x)) :=
  NSFormalization.Section4.I03.scaled_slice_contDiff d.packet _ (d.eps_admissible j).1 ht.2

theorem component_pressure_slice (j : Fin d.N) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) d.T) :
    ContDiff ℝ ∞ (fun x => (d.component j).pressure (t, x)) := by
  change ContDiff ℝ ∞ (fun x => scaledPressure p (d.placement j).x₀ d.T (d.ε j) (t, x) -
    domainPressureMean d.Ω (scaledPressure p (d.placement j).x₀ d.T (d.ε j)) t)
  exact (NSFormalization.Section4.I03.slice_contDiff_of_slab (d.raw_pressure_smooth j) ht.2).sub contDiff_const

theorem component_nonoverlap {i j : Fin d.N} (hij : i ≠ j)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) d.T) (x : Space)
    (hi : (d.component i).velocity (t, x) ≠ 0) : (d.component j).velocity (t, x) = 0 := by
  have hiB : x ∈ Metric.ball (d.regionCenter i) (d.regionRadius i) := by
    by_contra hout
    exact hi (d.component_support i t ht x hout)
  apply d.component_support j t ht x
  exact fun hjB => Set.disjoint_left.mp (d.regions_disjoint hij) hiB hjB

/-- If the advecting component is nonzero, continuity gives a neighbourhood
where it stays nonzero, and the other component is identically zero there. -/
theorem crossTransport_eq_zero {i j : Fin d.N} (hij : i ≠ j)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) d.T) (x : Space) :
    spatialDerivative (d.component j).velocity t x ((d.component i).velocity (t, x)) = 0 := by
  by_cases hi : (d.component i).velocity (t, x) = 0
  · rw [hi, map_zero]
  · have hn : ∀ᶠ y in 𝓝 x, (d.component i).velocity (t, y) ≠ 0 :=
      (d.component_slice i ht).continuous.continuousAt.eventually_ne hi
    have hz : (fun y => (d.component j).velocity (t, y)) =ᶠ[𝓝 x] (fun _ => (0 : Space)) :=
      hn.mono (fun y hy => d.component_nonoverlap hij ht y hy)
    change (fderiv ℝ (fun y => (d.component j).velocity (t, y)) x) _ = 0
    rw [hz.fderiv_eq]
    simp

/-- The spatial derivative of the sum is the sum of the actual derivatives. -/
theorem assembled_spatialDerivative {t : ℝ} (ht : t ∈ Ico (0 : ℝ) d.T) (x : Space) :
    spatialDerivative d.assembledVelocity t x =
      ∑ j : Fin d.N, spatialDerivative (d.component j).velocity t x := by
  unfold spatialDerivative assembledVelocity finiteVelocitySum
  exact fderiv_fun_sum (fun j _ => (d.component_slice j ht).differentiable (by simp) x)

/-- Incompressibility is linear on smooth spatial slices. -/
theorem assembled_divergence : ∀ t ∈ Ico (0 : ℝ) d.T, ∀ x : Space,
    spatialDivergence d.assembledVelocity t x = 0 := by
  intro t ht x
  unfold spatialDivergence
  rw [d.assembled_spatialDerivative ht x]
  simp only [sum_apply, WithLp.ofLp_sum, Finset.sum_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_eq_zero (fun j _ => scaled_divergence d.divergence (d.eps_admissible j).1 _ ht.2 x)

/-- The integral of a finite sum of gauged pressures vanishes. -/
theorem assembled_pressure_gauge : ∀ t ∈ Ico (0 : ℝ) d.T,
    (∫ x in d.Ω, d.assembledPressure (t, x)) = 0 := by
  intro t ht
  change (∫ x in d.Ω, ∑ j : Fin d.N, (d.component j).pressure (t, x)) = 0
  rw [integral_finsetSum _ (fun j _ =>
    (d.component j).pressure_smooth.integrableOn_slice d.hΩ.2.1 ht)]
  exact Finset.sum_eq_zero (fun j _ => (d.component j).pressure_gauge t ht)

theorem component_temporal (j : Fin d.N) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) d.T)
    (x : Space) : DifferentiableAt ℝ (fun s => (d.component j).velocity (s, x)) t := by
  have ha : ContDiffAt ℝ ∞ (scaledVelocity u (d.placement j).x₀ d.T (d.ε j)) (t, x) := (d.raw_velocity_smooth j).contDiffAt
    ((isOpen_Iio.prod isOpen_univ).mem_nhds ⟨ht.2, mem_univ x⟩)
  exact (ha.differentiableAt (by simp)).comp t
    (differentiableAt_id.prodMk (differentiableAt_const x))

/-- Linearity of the temporal term at interior times. -/
theorem assembled_temporalDerivative {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) d.T) (x : Space) :
    temporalDerivative d.assembledVelocity t x =
      ∑ j : Fin d.N, temporalDerivative (d.component j).velocity t x := by
  unfold temporalDerivative assembledVelocity finiteVelocitySum
  rw [fderiv_fun_sum (fun j _ => d.component_temporal j ht x)]
  exact sum_apply _ _ _

/-- Linearity of both spatial derivatives in the Laplacian. -/
theorem assembled_spatialLaplacian {t : ℝ} (ht : t ∈ Ico (0 : ℝ) d.T) (x : Space) :
    spatialLaplacian d.assembledVelocity t x =
      ∑ j : Fin d.N, spatialLaplacian (d.component j).velocity t x := by
  unfold spatialLaplacian
  simp_rw [d.assembled_spatialDerivative ht, sum_apply]
  have hd (i : Fin 3) (j : Fin d.N) : DifferentiableAt ℝ
      (fun y => spatialDerivative (d.component j).velocity t y (coordinateVector i)) x :=
    NavierStokes.ResidualCalculus.differentiable_spatial_direction _ t
      ((d.component_slice j ht).of_le (by simp)) _ x
  simp_rw [fderiv_fun_sum (fun j _ => hd _ j), sum_apply]
  exact Finset.sum_comm

/-- Pressure gradients commute with the finite sum. -/
theorem assembled_pressureGradient {t : ℝ} (ht : t ∈ Ico (0 : ℝ) d.T) (x : Space) :
    pressureGradient d.assembledPressure t x =
      ∑ j : Fin d.N, pressureGradient (d.component j).pressure t x := by
  have hd (j : Fin d.N) : DifferentiableAt ℝ (fun y => (d.component j).pressure (t, y)) x :=
    (d.component_pressure_slice j ht).differentiable (by simp) x
  unfold pressureGradient assembledPressure finitePressureSum
  rw [fderiv_fun_sum (fun j _ => hd j)]
  simp only [sum_apply, Finset.sum_smul]
  exact Finset.sum_comm

/-- Only the diagonal terms in the quadratic transport survive. -/
theorem assembled_advection {t : ℝ} (ht : t ∈ Ico (0 : ℝ) d.T) (x : Space) :
    advection d.assembledVelocity t x = ∑ j : Fin d.N, advection (d.component j).velocity t x := by
  unfold advection
  rw [d.assembled_spatialDerivative ht x]
  change (∑ j : Fin d.N, spatialDerivative (d.component j).velocity t x)
    (∑ i : Fin d.N, (d.component i).velocity (t, x)) = _
  simp only [sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact Finset.sum_eq_single j
    (fun i _ hij => d.crossTransport_eq_zero hij.symm ht x) (by simp)

/-- The literal registered momentum residual of the finite superposition. -/
theorem assembled_momentum : ∀ t ∈ Ioo (0 : ℝ) d.T, ∀ x ∈ d.Ω,
    NavierStokesR3.ProblemStatement.navierStokesResidual ν d.assembledVelocity
      d.assembledPressure t x = d.assembledForce (t, x) := by
  intro t ht x hx
  have hc : t ∈ Ico (0 : ℝ) d.T := ⟨ht.1.le, ht.2⟩
  unfold NavierStokesR3.ProblemStatement.navierStokesResidual
  rw [d.assembled_temporalDerivative ht x, d.assembled_advection hc x,
    d.assembled_spatialLaplacian hc x, d.assembled_pressureGradient hc x]
  simp only [Finset.smul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun j _ => (d.component j).momentum t ht x hx)

/-- The actual classical solution, with the two prescribed finite-sum fields. -/
theorem no_slip : ∀ t ∈ Ico (0 : ℝ) d.T, ∀ x ∈ frontier d.Ω,
    d.assembledVelocity (t, x) = 0 := by
  intro t ht x hx
  unfold assembledVelocity finiteVelocitySum
  exact Finset.sum_eq_zero (fun j _ => (d.component j).no_slip t ht x hx)

def solution : ClassicalSolutionOmega ν d.Ω (0 : SpatialField) d.assembledForce d.T where
  velocity := d.assembledVelocity
  pressure := d.assembledPressure
  horizon_pos := d.hT
  velocity_smooth := d.assembled_velocity_smooth
  pressure_smooth := d.assembled_pressure_smooth
  initial := fun x _ => d.rest x
  divergence := fun t ht x _ => d.assembled_divergence t ht x
  momentum := d.assembled_momentum
  no_slip := d.no_slip
  pressure_gauge := d.assembled_pressure_gauge

theorem solution_pin : d.solution.velocity = d.assembledVelocity ∧
    d.solution.pressure = d.assembledPressure := ⟨rfl, rfl⟩

end RegionsOmegaData
end NSFormalization.Section3.T24
