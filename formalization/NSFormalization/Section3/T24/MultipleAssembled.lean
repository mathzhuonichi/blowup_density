import NSFormalization.Section3.T24.MultipleComponents

/-! Finite superposition of the disjoint T15 components (`03-torus.tex:707-712,719`). -/
noncomputable section
namespace NSFormalization.Section3.T24
open Set Filter MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10 NSFormalization.Section3.T13 NSFormalization.Section3.T15
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField SpaceTimeScalar)
open scoped ContDiff Topology BigOperators

/-- Compact positive-time support and smooth periodicity survive finite sums. -/
theorem forceClassT_finset_sum {ι : Type*} (s : Finset ι) (F : ι → SpaceTimeField)
    (hF : ∀ i ∈ s, F i ∈ forceClassT) : (fun z => ∑ i ∈ s, F i z) ∈ forceClassT := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by simpa using (contDiff_const : ContDiff ℝ ∞ (fun _ : SpaceTime => (0 : Space))), ?_, ∅, isCompact_empty, empty_subset _, ?_⟩
    · intro t ht x i
      simp
    · simp [tsupport]
  | @insert a s ha ih =>
    have hf := hF a (Finset.mem_insert_self a s)
    have hg := ih (fun i hi => hF i (Finset.mem_insert_of_mem hi))
    rcases hf with ⟨hfs, hfp, K, hK, hKpos, hfK⟩
    rcases hg with ⟨hgs, hgp, L, hL, hLpos, hgL⟩
    simp only [Finset.sum_insert ha]
    refine ⟨hfs.add hgs, ?_, K ∪ L, hK.union hL, union_subset hKpos hLpos, ?_⟩
    · intro t ht x i
      dsimp only
      exact congrArg₂ (· + ·) (hfp t ht x i) (hgp t ht x i)
    · intro z hz
      rcases tsupport_add (F a) (fun z => ∑ i ∈ s, F i z) hz with h | h
      · exact ⟨Or.inl (hfK h).1, mem_univ _⟩
      · exact ⟨Or.inr (hgL h).1, mem_univ _⟩

namespace RegionsData
variable {ν : ℝ} {u f : VelocityField} {p : PressureField}
  {K : Set Space} {M E : ℝ} (d : RegionsData ν u p f K M E)

def assembledVelocity : SpaceTimeField := finiteVelocitySum (fun j => (d.component j).velocity)
def assembledPressure : SpaceTimeScalar := finitePressureSum (fun j => (d.component j).pressure)
def assembledForce : SpaceTimeField :=
  finiteForceSum (fun j => periodizedScaledForce f (d.placement j).x₀ d.T (d.ε j))

theorem assembled_velocity_formula :
    d.assembledVelocity = finiteVelocitySum (fun j => (d.component j).velocity) := rfl
theorem assembled_pressure_formula :
    d.assembledPressure = finitePressureSum (fun j => (d.component j).pressure) := rfl
theorem assembled_force_formula : d.assembledForce =
    finiteForceSum (fun j => periodizedScaledForce f (d.placement j).x₀ d.T (d.ε j)) := rfl

theorem assembled_velocity_smooth : ContDiffOn ℝ ∞ d.assembledVelocity
    (Ico (0 : ℝ) d.T ×ˢ (univ : Set Space)) := by
  unfold assembledVelocity finiteVelocitySum
  exact ContDiffOn.sum (fun j _ => (d.component j).velocity_smooth)
theorem assembled_pressure_smooth : ContDiffOn ℝ ∞ d.assembledPressure
    (Ico (0 : ℝ) d.T ×ˢ (univ : Set Space)) := by
  unfold assembledPressure finitePressureSum
  exact ContDiffOn.sum (fun j _ => (d.component j).pressure_smooth)
theorem velocity_periodic : IsPeriodicOn (Ico (0 : ℝ) d.T) d.assembledVelocity := by
  intro t ht x i
  unfold assembledVelocity finiteVelocitySum
  exact Finset.sum_congr rfl (fun j _ => (d.component j).velocity_periodic t ht x i)
theorem pressure_periodic : IsPeriodicOn (Ico (0 : ℝ) d.T) d.assembledPressure := by
  intro t ht x i
  unfold assembledPressure finitePressureSum
  exact Finset.sum_congr rfl (fun j _ => (d.component j).pressure_periodic t ht x i)
theorem rest : ∀ x : Space, d.assembledVelocity (0, x) = 0 := by
  intro x
  unfold assembledVelocity finiteVelocitySum
  exact Finset.sum_eq_zero (fun j _ => (d.component j).initial x)
theorem force_mem : d.assembledForce ∈ forceClassT :=
  forceClassT_finset_sum Finset.univ _ (fun j _ => (d.scaling j).force_mem _ (d.eps_admissible j))

/-- Smooth slices include the initial time. -/
theorem component_slice (j : Fin d.N) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) d.T) :
    ContDiff ℝ ∞ (fun x => (d.component j).velocity (t, x)) :=
  (d.component j).velocity_smooth.comp_contDiff
    (contDiff_const.prodMk contDiff_id) (fun x => ⟨ht, mem_univ x⟩)

/-- One common lattice representative witnesses pointwise non-overlap. -/
theorem component_nonoverlap {i j : Fin d.N} (hij : i ≠ j)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) d.T) (x : Space)
    (hi : (d.component i).velocity (t, x) ≠ 0) : (d.component j).velocity (t, x) = 0 := by
  let y := x - latticeVector (fun k => ⌊x k⌋)
  have hy : y ∈ fundamentalCube := floor_representative_mem_cube x
  have he (k : Fin d.N) : (d.component k).velocity (t, y) = (d.component k).velocity (t, x) := by
    rw [(d.component_pin k).1]
    exact periodize_sub_lattice (scaledVelocity u (d.placement k).x₀ d.T (d.ε k)) t x _
  have hiB : y ∈ Metric.ball (d.regionCenter i) (d.regionRadius i) := by
    by_contra hout
    exact hi ((he i).symm.trans (d.component_support i t ht y hy hout))
  rw [← he j]
  apply d.component_support j t ht y hy
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
  exact Finset.sum_eq_zero (fun j _ => (d.component j).divergence t ht x)

/-- Smoothness of the finite sum supplies its continuous integer-order datum path. -/
theorem assembled_sobolev : ∀ m : ℕ, ∃ G : ℝ → PeriodicSobolev (m : ℝ),
    ContinuousOn G (Ico (0 : ℝ) d.T) ∧ ∀ t ∈ Ico (0 : ℝ) d.T,
      IsPeriodicDatum (m : ℝ) (fun x => d.assembledVelocity (t, x)) (G t) := by
  classical
  intro m
  have hex : ∀ t ∈ Ico (0 : ℝ) d.T, ∃ A : PeriodicSobolev (m : ℝ),
      IsPeriodicDatum (m : ℝ) (fun x => d.assembledVelocity (t, x)) A := by
    intro t ht
    exact NSFormalization.Section3.T11.exists_periodicDatum_smooth (m : ℝ)
      (d.assembled_velocity_smooth.comp_contDiff (contDiff_const.prodMk contDiff_id)
        (fun x => ⟨ht, mem_univ x⟩)) (d.velocity_periodic t ht)
  let G : ℝ → PeriodicSobolev (m : ℝ) := fun t =>
    if ht : t ∈ Ico (0 : ℝ) d.T then (hex t ht).choose else 0
  have hG : ∀ t ∈ Ico (0 : ℝ) d.T,
      IsPeriodicDatum (m : ℝ) (fun x => d.assembledVelocity (t, x)) (G t) := by
    intro t ht
    simpa only [G, dite_eq_left ht] using (hex t ht).choose_spec
  exact ⟨G, NSFormalization.Section3.T11.continuousOn_periodicDatum_path_of_slab
    m d.assembled_velocity_smooth G hG, hG⟩

/-- Compact-torus integrability of the smooth summed pressure gradient. -/
theorem assembled_pressure_gradient : ∀ t ∈ Ico (0 : ℝ) d.T,
    MemLp (torusLift (fun x => pressureGradient d.assembledPressure t x)) 2
      periodicTorusMeasure := by
  intro t ht
  have hs := d.assembled_pressure_smooth.comp_contDiff
    (contDiff_const.prodMk contDiff_id) (fun x => ⟨ht, mem_univ x⟩)
  exact memLp_torusLift_vector
    (NavierStokes.PeriodicUniqueness.pressureGradient_contDiff hs).continuous 2

/-- The Haar integral of the finite pressure sum is the sum of its zero means. -/
theorem assembled_pressure_gauge : PressureGaugeT (Ico (0 : ℝ) d.T) d.assembledPressure := by
  intro t ht
  have hi (j : Fin d.N) : Integrable
      (torusLift (fun x => (d.component j).pressure (t, x))) periodicTorusMeasure := by
    have hs := (d.component j).pressure_smooth.comp_contDiff
      (contDiff_const.prodMk contDiff_id) (fun x => ⟨ht, mem_univ x⟩)
    exact ((NSFormalization.Paper1.memLp_torusLift
      (Complex.continuous_ofReal.comp hs.continuous) 1).integrable le_rfl).re
  change (∫ y, ∑ j : Fin d.N,
    torusLift (fun x => (d.component j).pressure (t, x)) y ∂periodicTorusMeasure) = 0
  rw [integral_finsetSum _ (fun j _ => hi j)]
  exact Finset.sum_eq_zero (fun j _ => (d.component j).pressure_gauge t ht)

/-- Interior time differentiability for each component. -/
theorem component_temporal (j : Fin d.N) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) d.T)
    (x : Space) : DifferentiableAt ℝ (fun s => (d.component j).velocity (s, x)) t := by
  have hs := (d.component j).velocity_smooth.mono
    (show Ioo (0 : ℝ) d.T ×ˢ (univ : Set Space) ⊆ Ico (0 : ℝ) d.T ×ˢ univ from
      fun _ hz => ⟨⟨hz.1.1.le, hz.1.2⟩, hz.2⟩)
  have ha : ContDiffAt ℝ ∞ (d.component j).velocity (t, x) := hs.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨ht, mem_univ x⟩)
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
    ((d.component j).pressure_smooth.comp_contDiff
      (contDiff_const.prodMk contDiff_id) (fun y => ⟨ht, mem_univ y⟩)).differentiable (by simp) x
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
theorem assembled_momentum : ∀ t ∈ Ioo (0 : ℝ) d.T, ∀ x : Space,
    NavierStokesR3.ProblemStatement.navierStokesResidual ν d.assembledVelocity
      d.assembledPressure t x = d.assembledForce (t, x) := by
  intro t ht x
  have hc : t ∈ Ico (0 : ℝ) d.T := ⟨ht.1.le, ht.2⟩
  unfold NavierStokesR3.ProblemStatement.navierStokesResidual
  rw [d.assembled_temporalDerivative ht x, d.assembled_advection hc x,
    d.assembled_spatialLaplacian hc x, d.assembled_pressureGradient hc x]
  simp only [Finset.smul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun j _ => (d.component j).momentum t ht x)

/-- The actual classical solution, with the two prescribed finite-sum fields. -/
def solution : ClassicalSolutionT ν (0 : SpatialField) d.assembledForce d.T where
  velocity := d.assembledVelocity
  pressure := d.assembledPressure
  horizon_pos := d.hT
  velocity_smooth := d.assembled_velocity_smooth
  pressure_smooth := d.assembled_pressure_smooth
  initial := d.rest
  divergence := d.assembled_divergence
  momentum := d.assembled_momentum
  sobolev := d.assembled_sobolev
  pressure_gradient := d.assembled_pressure_gradient
  velocity_periodic := d.velocity_periodic
  pressure_periodic := d.pressure_periodic
  pressure_gauge := d.assembled_pressure_gauge

theorem solution_pin : d.solution.velocity = d.assembledVelocity ∧
    d.solution.pressure = d.assembledPressure := ⟨rfl, rfl⟩

end RegionsData
end NSFormalization.Section3.T24
