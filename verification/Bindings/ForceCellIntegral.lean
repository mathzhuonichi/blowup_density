import Bindings.GridLemmas
import Contracts.V1.InsertionFamily
import NavierStokes.ComparatorBridge
import NSFormalization.Paper3.TimeObservations

/-!
# Cell integrals for the R42 insertion

Velocity is unconditional. The force result isolates exactly one analytic input,
`hcompactMomentumIntegral`: the integrated residual identity with vanishing spatial
flux, before using the momentum equations or zero time-derivative mean. This is the
boundary-free form of `eq:gridforce`; it is not established in this module.
The input is only at interior times; positive-time force support handles zero.
-/
noncomputable section
namespace BlowupDensity.Bindings
open Set MeasureTheory Filter
open scoped Topology ContDiff
open Contracts.V1 Contracts.V1.Data
open NSFormalization.Paper3

variable {ν : ℝ} {P : PacketAPI ν} (A : InsertionFamilyAPI ν P)

/-- Reference regularity restricted to the insertion slab. -/
theorem insertion_reference_smooth :
    ContDiffOn ℝ ∞ A.v (Ico 0 A.T ×ˢ (univ : Set Space)) := by
  rw [InsertionFamilyAPI.v, ← A.reference_velocity]
  apply A.reference.velocity_smooth.mono
  intro z hz
  exact ⟨⟨hz.1.1, lt_of_lt_of_le hz.1.2
    (le_add_of_nonneg_right A.scaling.correction.margin_pos.le)⟩, hz.2⟩

/-- Smooth spatial velocity difference, including the initial slice. -/
theorem velocityDifference_slice_smooth {ε t : ℝ} (hε : ε ∈ Ioc 0 A.ε₀)
    (ht : t ∈ Ico 0 A.T) :
    ContDiff ℝ ∞ (fun x : Space => A.velocity ε (t,x) - A.v (t,x)) := by
  exact ((A.velocity_smooth ε hε).sub (insertion_reference_smooth A)).comp_contDiff
    (contDiff_const.prodMk contDiff_id) (fun x => ⟨ht, mem_univ x⟩)

/-- The closed support is compact because it lies in the fixed bounded ball. -/
theorem velocityDifference_slice_compact {ε t : ℝ} (hε : ε ∈ Ioc 0 A.ε₀)
    (ht : t ∈ Ico 0 A.T) :
    HasCompactSupport (fun x : Space => A.velocity ε (t,x) - A.v (t,x)) := by
  exact (isCompact_closedBall A.scaling.correction.x₀ A.scaling.correction.r).of_isClosed_subset
    (isClosed_tsupport _) ((A.velocityDifference_support ε hε t ht).trans Metric.ball_subset_closedBall)

/-- Component version of the compact-solenoidal zero-mean argument. -/
theorem velocityDifference_cell_integral_zero_component {ε t : ℝ}
    (hε : ε ∈ Ioc 0 A.ε₀) (ht : t ∈ Ico 0 A.T)
    (grid : Grid) (k₀ : Fin 3 → ℤ) (hB : A.ball ⊆ grid.cell k₀) (j : Fin 3) :
    (∫ x in grid.cell k₀, (A.velocity ε (t,x) - A.v (t,x)) j) = 0 := by
  apply setIntegral_component_eq_zero
    ((velocityDifference_slice_smooth A hε ht).of_le (by simp))
    (velocityDifference_slice_compact A hε ht)
  · intro x
    exact (NavierStokes.ComparatorBridge.divergence_eq
      (fun z => A.velocity ε z - A.v z) t x) ▸ A.velocityDifference_divFree ε hε t ht x
  · exact grid.measurableSet_cell k₀
  · exact (subset_tsupport _).trans ((A.velocityDifference_support ε hε t ht).trans hB)

/-- Vector version, suitable for `gridObservation_locality`. -/
theorem velocityDifference_cell_integral_zero {ε t : ℝ}
    (hε : ε ∈ Ioc 0 A.ε₀) (ht : t ∈ Ico 0 A.T)
    (grid : Grid) (k₀ : Fin 3 → ℤ) (hB : A.ball ⊆ grid.cell k₀) :
    (∫ x in grid.cell k₀, (A.velocity ε (t,x) - A.v (t,x))) = 0 := by
  have hi : IntegrableOn (fun x : Space => A.velocity ε (t,x) - A.v (t,x)) (grid.cell k₀) := ((velocityDifference_slice_smooth A hε ht).continuous.integrable_of_hasCompactSupport
    (velocityDifference_slice_compact A hε ht)).integrableOn (s := grid.cell k₀)
  ext j
  change (EuclideanSpace.proj j) (∫ x in grid.cell k₀, _) = 0
  rw [← (EuclideanSpace.proj j).integral_comp_comm hi]
  exact velocityDifference_cell_integral_zero_component A hε ht grid k₀ hB j

/-- Subtract the actual two momentum equations, without assuming that a
nonlinear residual is linear in velocity. -/
theorem insertion_momentum_difference {ε t : ℝ} (hε : ε ∈ Ioc 0 A.ε₀)
    (ht : t ∈ Ioo 0 A.T) (x : Space) :
    NavierStokesR3.ProblemStatement.navierStokesResidual ν (A.velocity ε) (A.pressure ε) t x -
      NavierStokesR3.ProblemStatement.navierStokesResidual ν A.v A.π t x =
        A.force ε (t,x) - A.g (t,x) := by
  have hu : NavierStokesR3.ProblemStatement.navierStokesResidual ν
      (A.velocity ε) (A.pressure ε) t x = A.force ε (t,x) := A.momentum ε hε t ht x
  rw [hu]
  have hr := A.reference.momentum t
    ⟨ht.1, lt_of_lt_of_le ht.2 (le_add_of_nonneg_right A.scaling.correction.margin_pos.le)⟩ x
  rw [A.reference_velocity, A.reference_pressure] at hr
  exact congrArg (fun y => A.force ε (t,x) - y) hr

/-- The force correction vanishes at zero, independently of the interior PDE. -/
theorem forceDifference_initial_zero {ε : ℝ} (hε : ε ∈ Ioc 0 A.ε₀) (x : Space) :
    A.force ε (0,x) - A.g (0,x) = 0 := by
  exact (A.forceDifference_compact ε hε).2.eq_zero_of_nonpos le_rfl x

/-- Differentiating the zero spatial mean on a compact interior time window.
This uses the proved compact differentiation-under-the-integral theorem in
`Paper3.TimeObservations`, with the fixed closed insertion ball as dominator. -/
theorem velocityDifference_timeDerivative_integral_zero {ε t : ℝ}
    (hε : ε ∈ Ioc 0 A.ε₀) (ht : t ∈ Ioo 0 A.T) :
    (∫ x : Space, deriv (fun s => A.velocity ε (s,x) - A.v (s,x)) t) = 0 := by
  let w : ℝ × Space → Space := fun z => A.velocity ε z - A.v z
  let z : Space → Space := fun x => deriv (fun s => w (s,x)) t
  have hw : ContDiffOn ℝ ∞ w (Ico 0 A.T ×ˢ (univ : Set Space)) :=
    (A.velocity_smooth ε hε).sub (insertion_reference_smooth A)
  have hsub : Icc (t / 2) ((t + A.T) / 2) ⊆ Ico 0 A.T := by
    intro s hs
    constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
  have hwindow : ContDiffOn ℝ 1 w
      (Icc (t / 2) ((t + A.T) / 2) ×ˢ (univ : Set Space)) :=
    (hw.of_le (by simp)).mono (prod_mono hsub Subset.rfl)
  have hderiv : ∀ x, HasDerivAt (fun s => w (s,x)) (z x) t := by
    intro x
    have hAt : ContDiffAt ℝ ∞ w (t,x) := hw.contDiffAt
      (prod_mem_nhds (Ico_mem_nhds ht.1 ht.2) univ_mem)
    exact ((hAt.comp t (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt
      (by simp)).hasDerivAt
  have hj (j : Fin 3) : (∫ x : Space, z x j) = 0 := by
    apply integral_timeDerivative_component_eq_zero (t := t)
      (isCompact_closedBall A.scaling.correction.x₀ A.scaling.correction.r)
      hwindow
    · intro s hs x hx
      change (fun y : Space => A.velocity ε (s,y) - A.v (s,y)) x = 0
      apply image_eq_zero_of_notMem_tsupport (f := fun y : Space => A.velocity ε (s,y) - A.v (s,y))
      intro hx'
      exact hx (Metric.ball_subset_closedBall
        (A.velocityDifference_support ε hε s (hsub hs) hx'))
    · intro s hs x
      exact (NavierStokes.ComparatorBridge.divergence_eq w s x) ▸
        A.velocityDifference_divFree ε hε s (hsub hs) x
    · constructor <;> linarith [ht.1, ht.2]
    · exact hderiv
  change (∫ x : Space, z x) = 0
  by_cases hi : Integrable z
  · ext j
    change (EuclideanSpace.proj j) (∫ x : Space, z x) = 0
    rw [← (EuclideanSpace.proj j).integral_comp_comm hi]
    exact hj j
  · exact integral_undef hi

/-- `eq:gridforce`, conditional only on the integrated compact-residual identity.

The named input is the vanishing of all spatial flux integrals, including
the algebraic passage from the two residuals to the difference time derivative. Its intended proof uses `velocity_smooth`,
`reference.velocity_smooth`, `incompressible`, `reference.divergence`, and the
velocity/pressure support fields. It imposes no condition on force divergence
and no two-sided regularity at time zero. -/
theorem forceDifference_cell_integral_zero
    (hcompactMomentumIntegral : ∀ ε ∈ Ioc 0 A.ε₀, ∀ (grid : Grid) (k₀ : Fin 3 → ℤ),
      A.ball ⊆ grid.cell k₀ → ∀ t ∈ Ioo 0 A.T,
      (∫ x in grid.cell k₀,
        (NavierStokesR3.ProblemStatement.navierStokesResidual ν (A.velocity ε) (A.pressure ε) t x -
         NavierStokesR3.ProblemStatement.navierStokesResidual ν A.v A.π t x)) =
      (∫ x : Space, deriv (fun s => A.velocity ε (s,x) - A.v (s,x)) t))
    {ε t : ℝ} (hε : ε ∈ Ioc 0 A.ε₀) (ht : t ∈ Ico 0 A.T)
    (grid : Grid) (k₀ : Fin 3 → ℤ) (hB : A.ball ⊆ grid.cell k₀) :
    (∫ x in grid.cell k₀, (A.force ε (t,x) - A.g (t,x))) = 0 := by
  rcases eq_or_lt_of_le ht.1 with ht0 | ht0
  · subst t
    simp only [forceDifference_initial_zero A hε, integral_zero]
  · have h := hcompactMomentumIntegral ε hε grid k₀ hB t ⟨ht0, ht.2⟩
    simp_rw [insertion_momentum_difference A hε ⟨ht0, ht.2⟩] at h
    exact h.trans (velocityDifference_timeDerivative_integral_zero A hε ⟨ht0, ht.2⟩)

/-- Continuous fields are integrable on the bounded half-open grid cells. -/
theorem continuous_integrableOn_grid_cell (grid : Grid) (k : Fin 3 → ℤ)
    {z : SpatialField} (hz : Continuous z) : IntegrableOn z (grid.cell k) := by
  let K : Set (Fin 3 → ℝ) := {y | ∀ j,
    y j ∈ Icc (grid.offset j + grid.width j * (k j : ℝ))
      (grid.offset j + grid.width j * ((k j : ℝ) + 1))}
  have hK : IsCompact K := isCompact_pi_infinite (fun _ => isCompact_Icc)
  have hc := hK.image (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ))
  apply (hz.continuousOn.integrableOn_compact hc).mono_set
  intro x hx
  exact ⟨WithLp.ofLp x, fun j => ⟨(hx j).1, (hx j).2.le⟩, rfl⟩

/-- The spacetime force support field implies the required slice support. -/
theorem forceDifference_slice_support {ε : ℝ} (hε : ε ∈ Ioc 0 A.ε₀) (t : ℝ) :
    tsupport (fun x : Space => A.force ε (t,x) - A.g (t,x)) ⊆ A.ball := by
  intro x hx
  apply A.forceDifference_ball ε hε (t,x)
  exact tsupport_comp_subset_preimage (fun z => A.force ε z - A.g z)
    (continuous_const.prodMk continuous_id) hx

/-- The registered velocity observations agree for all presingular times. -/
theorem velocity_gridObservation_eq {ε t : ℝ} (hε : ε ∈ Ioc 0 A.ε₀)
    (ht : t ∈ Ico 0 A.T) (grid : Grid) (k₀ : Fin 3 → ℤ)
    (hB : A.ball ⊆ grid.cell k₀) :
    gridObservation grid (fun x => A.velocity ε (t,x)) =
      gridObservation grid (fun x => A.v (t,x)) := by
  have hu : Continuous (fun x : Space => A.velocity ε (t,x)) :=
    ((A.velocity_smooth ε hε).comp_contDiff (contDiff_const.prodMk contDiff_id)
      (fun x => ⟨ht, mem_univ x⟩)).continuous
  have hv : Continuous (fun x : Space => A.v (t,x)) :=
    ((insertion_reference_smooth A).comp_contDiff (contDiff_const.prodMk contDiff_id)
      (fun x => ⟨ht, mem_univ x⟩)).continuous
  exact gridObservation_locality grid _ _ A.ball k₀
    (A.velocityDifference_support ε hε t ht) hB
    (continuous_integrableOn_grid_cell grid k₀ hu)
    (continuous_integrableOn_grid_cell grid k₀ hv)
    (velocityDifference_cell_integral_zero A hε ht grid k₀ hB)

/-- Force observations on the spec's full `[0,T)` time range. `hg` is the
regular reference force assumption of Theorem 4.7; the R42 record itself does
not carry `MemForceR g`. The sole unresolved analytic input is the same
compact-residual integral identity as in `forceDifference_cell_integral_zero`. -/
theorem force_gridObservation_eq
    (hcompactMomentumIntegral : ∀ ε ∈ Ioc 0 A.ε₀, ∀ (grid : Grid) (k₀ : Fin 3 → ℤ),
      A.ball ⊆ grid.cell k₀ → ∀ t ∈ Ioo 0 A.T,
      (∫ x in grid.cell k₀,
        (NavierStokesR3.ProblemStatement.navierStokesResidual ν (A.velocity ε) (A.pressure ε) t x -
         NavierStokesR3.ProblemStatement.navierStokesResidual ν A.v A.π t x)) =
      (∫ x : Space, deriv (fun s => A.velocity ε (s,x) - A.v (s,x)) t))
    (hg : MemForceR A.g) {ε t : ℝ} (hε : ε ∈ Ioc 0 A.ε₀)
    (ht : t ∈ Ico 0 A.T) (grid : Grid) (k₀ : Fin 3 → ℤ)
    (hB : A.ball ⊆ grid.cell k₀) :
    gridObservation grid (fun x => A.force ε (t,x)) =
      gridObservation grid (fun x => A.g (t,x)) := by
  have hg' : Continuous (fun x : Space => A.g (t,x)) :=
    (hg.1.comp_contDiff (contDiff_const.prodMk contDiff_id)
      (fun x => ⟨ht.1, mem_univ x⟩)).continuous
  have hd : Continuous (fun x : Space => A.force ε (t,x) - A.g (t,x)) :=
    ((A.forceDifference_compact ε hε).1.comp
      (contDiff_const.prodMk contDiff_id)).continuous
  have hf : Continuous (fun x : Space => A.force ε (t,x)) := by
    have hh := hd.add hg'
    change Continuous (fun x => (A.force ε (t,x) - A.g (t,x)) + A.g (t,x)) at hh
    simpa only [sub_add_cancel] using hh
  exact gridObservation_locality grid _ _ A.ball k₀
    (forceDifference_slice_support A hε t) hB
    (continuous_integrableOn_grid_cell grid k₀ hf)
    (continuous_integrableOn_grid_cell grid k₀ hg')
    (forceDifference_cell_integral_zero A hcompactMomentumIntegral hε ht grid k₀ hB)

/-- The initial force observations need neither the analytic input nor a cell
containing the ball: the force correction is pointwise zero on this slice. -/
theorem force_gridObservation_initial_eq {ε : ℝ} (hε : ε ∈ Ioc 0 A.ε₀)
    (grid : Grid) :
    gridObservation grid (fun x => A.force ε (0,x)) =
      gridObservation grid (fun x => A.g (0,x)) := by
  have he : (fun x => A.force ε (0,x)) = (fun x => A.g (0,x)) :=
    funext (fun x => sub_eq_zero.mp (forceDifference_initial_zero A hε x))
  rw [he]

end BlowupDensity.Bindings
