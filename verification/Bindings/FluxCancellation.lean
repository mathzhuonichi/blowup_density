import Bindings.ForceCellIntegral
import NSFormalization.Section4.A01.ConvectionDivergence
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Spatial flux cancellation for the R42 insertion

This discharges lane 251's `hcompactMomentumIntegral` with no additional
analytic input. Compact vector flux derivatives are integrable and have zero
whole-space integral by integration by parts against the constant scalar 1.
The nonlinear tensor difference, pressure difference, and derivative of the
velocity difference supply the three fluxes. Neither background velocity nor
background pressure is required to be compactly supported.

The actual momentum equations identify the residual difference with the
compact force correction, giving both integrability and restriction from a
containing cell to the whole space. This uses no force zero-mean premise.
The residual identity then supplies integrability of the temporal term too.
Lane 251's proved temporal zero-mean result finishes `eq:gridforce`.

The current R42 record already chooses a compact pressure representative.
`pressureGradient_sub_timeConstant` also proves gauge invariance directly.
All declarations use the default heartbeat limit (200000); no overrides.
-/
noncomputable section
namespace BlowupDensity.Bindings
open Set MeasureTheory Filter
open scoped Topology ContDiff
open Contracts.V1 (PacketAPI InsertionFamilyAPI Space)
open Contracts.V1.Data
open NavierStokes.ProblemStatement (coordinateVector temporalDerivative advection
  spatialDerivative spatialDivergence spatialLaplacian pressureGradient)
open NSFormalization.Section4.A01

/-- A compact smooth vector field has integrable directional derivatives of zero mean. -/
theorem compact_directional_integral {f : Space → Space}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (e : Space) :
    Integrable (fun x => fderiv ℝ f x e) ∧ (∫ x, fderiv ℝ f x e) = 0 := by
  have hi : Integrable (fun x => fderiv ℝ f x e) := ((hf.continuous_fderiv (by simp)).clm_apply continuous_const).integrable_of_hasCompactSupport
    (hc.fderiv_apply ℝ e)
  refine ⟨hi, ?_⟩
  have h := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
    (μ := volume) (f := fun _ : Space => (1 : ℝ)) (g := f) (v := e)
    (by simp) (by simpa using hi)
    (by simpa using hf.continuous.integrable_of_hasCompactSupport hc)
    (fun _ _ => differentiableAt_const _) (fun _ _ => hf.differentiable (by simp) _)
  simpa using h

/-- Summing finitely many compact flux derivatives preserves integrability and zero mean. -/
theorem compact_flux_integral {F : Fin 3 → Space → Space}
    (hF : ∀ i, ContDiff ℝ ∞ (F i)) (hc : ∀ i, HasCompactSupport (F i)) :
    Integrable (fun x => ∑ i, fderiv ℝ (F i) x (coordinateVector i)) ∧
      (∫ x, ∑ i, fderiv ℝ (F i) x (coordinateVector i)) = 0 := by
  have hi i := compact_directional_integral (hF i) (hc i) (coordinateVector i)
  refine ⟨integrable_finsetSum _ (fun i _ => (hi i).1), ?_⟩
  rw [integral_finsetSum _ (fun i _ => (hi i).1)]
  simp only [(hi _).2, Finset.sum_const_zero]

/-- The nonlinear tensor difference is compact whenever the velocity difference is. -/
theorem tensorDifference_compact {u v : Space → Space}
    (hc : HasCompactSupport (fun x => u x - v x)) (i : Fin 3) :
    HasCompactSupport (fun x => u x i • u x - v x i • v x) := by
  apply hc.mono'
  intro x hx
  by_contra hn
  have he : u x = v x := sub_eq_zero.mp (image_eq_zero_of_notMem_tsupport (f := fun x => u x - v x) hn)
  exact hx (by simp [he])

/-- Conservative form makes the nonlinear difference have zero spatial mean. -/
theorem advectionDifference_integral {u v : NavierStokes.ProblemStatement.VelocityField}
    {t : ℝ} (hu : ContDiff ℝ ∞ (fun x : Space => u (t,x)))
    (hv : ContDiff ℝ ∞ (fun x : Space => v (t,x)))
    (hc : HasCompactSupport (fun x : Space => u (t,x) - v (t,x)))
    (hdu : ∀ x, spatialDivergence u t x = 0)
    (hdv : ∀ x, spatialDivergence v t x = 0) :
    Integrable (fun x => advection u t x - advection v t x) ∧
      (∫ x, advection u t x - advection v t x) = 0 := by
  let F := fun (i : Fin 3) (x : Space) => u (t,x) i • u (t,x) - v (t,x) i • v (t,x)
  have hF i : ContDiff ℝ ∞ (F i) :=
    ((EuclideanSpace.proj i).contDiff.comp hu |>.smul hu).sub
      ((EuclideanSpace.proj i).contDiff.comp hv |>.smul hv)
  have he : (fun x => advection u t x - advection v t x) =
      (fun x => ∑ i, fderiv ℝ (F i) x (coordinateVector i)) := by
    funext x
    rw [← convectionDivergence_eq_advection u t x (hu.differentiable (by simp) x) (hdu x),
      ← convectionDivergence_eq_advection v t x (hv.differentiable (by simp) x) (hdv x)]
    unfold convectionDivergence
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [F]
    have hU : DifferentiableAt ℝ (fun y : Space => u (t,y) i • u (t,y)) x :=
      (((EuclideanSpace.proj i).contDiff.comp hu).smul hu).differentiable (by simp) x
    have hV : DifferentiableAt ℝ (fun y : Space => v (t,y) i • v (t,y)) x :=
      (((EuclideanSpace.proj i).contDiff.comp hv).smul hv).differentiable (by simp) x
    rw [fderiv_fun_sub hU hV]
    rfl
  rw [he]
  exact compact_flux_integral hF (fun i => tensorDifference_compact hc i)

/-- A time-dependent spatial constant does not change the pressure gradient. -/
theorem pressureGradient_sub_timeConstant
    (p : NavierStokes.ProblemStatement.PressureField) (c : ℝ → ℝ) (t : ℝ) (x : Space) :
    pressureGradient (fun z => p z - c z.1) t x = pressureGradient p t x := by
  simp only [pressureGradient, fderiv_sub_const]

/-- The pressure gradient difference is a sum of compact vector flux derivatives. -/
theorem pressureGradientDifference_integral
    {p q : NavierStokes.ProblemStatement.PressureField} {t : ℝ}
    (hp : ContDiff ℝ ∞ (fun x : Space => p (t,x)))
    (hq : ContDiff ℝ ∞ (fun x : Space => q (t,x)))
    (hc : HasCompactSupport (fun x : Space => p (t,x) - q (t,x))) :
    Integrable (fun x => pressureGradient p t x - pressureGradient q t x) ∧
      (∫ x, pressureGradient p t x - pressureGradient q t x) = 0 := by
  let F := fun (i : Fin 3) (x : Space) => (p (t,x) - q (t,x)) • coordinateVector i
  have hF i : ContDiff ℝ ∞ (F i) := (hp.sub hq).smul contDiff_const
  have hFc i : HasCompactSupport (F i) := hc.smul_right
  have he : (fun x => pressureGradient p t x - pressureGradient q t x) =
      (fun x => ∑ i, fderiv ℝ (F i) x (coordinateVector i)) := by
    funext x
    unfold pressureGradient
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [F]
    rw [fderiv_smul_const ((hp.sub hq).differentiable (by simp) x),
      fderiv_fun_sub (hp.differentiable (by simp) x) (hq.differentiable (by simp) x)]
    simp only [ContinuousLinearMap.smulRight_apply, sub_apply, sub_smul]
  rw [he]
  exact compact_flux_integral hF hFc

/-- The Laplacian difference is the divergence of the compact derivative difference. -/
theorem laplacianDifference_integral
    {u v : NavierStokes.ProblemStatement.VelocityField} {t : ℝ}
    (hu : ContDiff ℝ ∞ (fun x : Space => u (t,x)))
    (hv : ContDiff ℝ ∞ (fun x : Space => v (t,x)))
    (hc : HasCompactSupport (fun x : Space => u (t,x) - v (t,x))) :
    Integrable (fun x => spatialLaplacian u t x - spatialLaplacian v t x) ∧
      (∫ x, spatialLaplacian u t x - spatialLaplacian v t x) = 0 := by
  let F := fun (i : Fin 3) (x : Space) =>
    fderiv ℝ (fun y => u (t,y) - v (t,y)) x (coordinateVector i)
  have hF i : ContDiff ℝ ∞ (F i) :=
    ((hu.sub hv).fderiv_right (by simp)).clm_apply contDiff_const
  have hFc i : HasCompactSupport (F i) := hc.fderiv_apply ℝ _
  have hFu i : ContDiff ℝ ∞ (fun x : Space => spatialDerivative u t x (coordinateVector i)) :=
    (hu.fderiv_right (by simp)).clm_apply contDiff_const
  have hFv i : ContDiff ℝ ∞ (fun x : Space => spatialDerivative v t x (coordinateVector i)) :=
    (hv.fderiv_right (by simp)).clm_apply contDiff_const
  have hFe i : F i = fun x => spatialDerivative u t x (coordinateVector i) -
      spatialDerivative v t x (coordinateVector i) := by
    funext x
    dsimp [F, spatialDerivative]
    rw [fderiv_fun_sub (hu.differentiable (by simp) x) (hv.differentiable (by simp) x)]
    rfl
  have he : (fun x => spatialLaplacian u t x - spatialLaplacian v t x) =
      (fun x => ∑ i, fderiv ℝ (F i) x (coordinateVector i)) := by
    funext x
    unfold spatialLaplacian
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [hFe, fderiv_fun_sub ((hFu i).differentiable (by simp) x)
      ((hFv i).differentiable (by simp) x)]
    rfl
  rw [he]
  exact compact_flux_integral hF hFc

/-- Whole-space integrated residual identity. The nonlinear term is treated in
conservative form; only differences, not the individual backgrounds, are integrated. -/
theorem residualDifference_integral {ν t : ℝ}
    {u v : NavierStokes.ProblemStatement.VelocityField}
    {p q : NavierStokes.ProblemStatement.PressureField}
    (hu : ContDiff ℝ ∞ (fun x : Space => u (t,x)))
    (hv : ContDiff ℝ ∞ (fun x : Space => v (t,x)))
    (hp : ContDiff ℝ ∞ (fun x : Space => p (t,x)))
    (hq : ContDiff ℝ ∞ (fun x : Space => q (t,x)))
    (hc : HasCompactSupport (fun x : Space => u (t,x) - v (t,x)))
    (hpc : HasCompactSupport (fun x : Space => p (t,x) - q (t,x)))
    (hdu : ∀ x, spatialDivergence u t x = 0)
    (hdv : ∀ x, spatialDivergence v t x = 0)
    (htu : ∀ x, DifferentiableAt ℝ (fun s => u (s,x)) t)
    (htv : ∀ x, DifferentiableAt ℝ (fun s => v (s,x)) t)
    (hi : Integrable (fun x =>
      NavierStokesR3.ProblemStatement.navierStokesResidual ν u p t x -
      NavierStokesR3.ProblemStatement.navierStokesResidual ν v q t x)) :
    (∫ x, NavierStokesR3.ProblemStatement.navierStokesResidual ν u p t x -
      NavierStokesR3.ProblemStatement.navierStokesResidual ν v q t x) =
      ∫ x : Space, deriv (fun s => u (s,x) - v (s,x)) t := by
  have ha := advectionDifference_integral hu hv hc hdu hdv
  have hl := laplacianDifference_integral hu hv hc
  have hg := pressureGradientDifference_integral hp hq hpc
  have he x :
      NavierStokesR3.ProblemStatement.navierStokesResidual ν u p t x -
      NavierStokesR3.ProblemStatement.navierStokesResidual ν v q t x =
      deriv (fun s => u (s,x) - v (s,x)) t +
      (advection u t x - advection v t x) -
      ν • (spatialLaplacian u t x - spatialLaplacian v t x) +
      (pressureGradient p t x - pressureGradient q t x) := by
    rw [deriv_fun_sub (htu x) (htv x)]
    change _ = (temporalDerivative u t x - temporalDerivative v t x) + _ - _ + _
    unfold NavierStokesR3.ProblemStatement.navierStokesResidual
    rw [smul_sub]
    abel
  have hz : Integrable (fun x : Space => deriv (fun s => u (s,x) - v (s,x)) t) := by
    have hzi := ((hi.sub ha.1).add (hl.1.smul ν)).sub hg.1
    apply hzi.congr
    exact Filter.Eventually.of_forall (fun x => by dsimp; rw [he]; abel)
  simp_rw [he]
  erw [integral_add ((hz.add ha.1).sub (hl.1.smul ν)) hg.1,
    integral_sub (hz.add ha.1) (hl.1.smul ν), integral_add hz ha.1]
  simp only [Pi.smul_apply]
  rw [integral_smul, ha.2, hl.2, hg.2]
  simp

variable {ν : ℝ} {P : PacketAPI ν} (A : InsertionFamilyAPI ν P)

/-- Reference pressure regularity on the insertion slab, in the chosen compact gauge. -/
theorem insertion_reference_pressure_smooth :
    ContDiffOn ℝ ∞ A.π (Ico 0 A.T ×ˢ (univ : Set Space)) := by
  rw [InsertionFamilyAPI.π, ← A.reference_pressure]
  apply A.reference.pressure_smooth.mono
  intro z hz
  exact ⟨⟨hz.1.1, lt_of_lt_of_le hz.1.2
    (le_add_of_nonneg_right A.scaling.correction.margin_pos.le)⟩, hz.2⟩

/-- Lane 251's exact named input, discharged for every actual R42 record.
The residual difference has the force difference's support, so its cell integral
is its whole-space integral. All three spatial flux integrals then vanish. -/
theorem compactMomentumIntegral : ∀ ε ∈ Ioc 0 A.ε₀,
    ∀ (grid : Grid) (k₀ : Fin 3 → ℤ), A.ball ⊆ grid.cell k₀ →
    ∀ t ∈ Ioo 0 A.T,
    (∫ x in grid.cell k₀,
      (NavierStokesR3.ProblemStatement.navierStokesResidual ν (A.velocity ε) (A.pressure ε) t x -
       NavierStokesR3.ProblemStatement.navierStokesResidual ν A.v A.π t x)) =
    (∫ x : Space, deriv (fun s => A.velocity ε (s,x) - A.v (s,x)) t) := by
  intro ε hε grid k₀ hB t ht
  have ht' : t ∈ Ico 0 A.T := ⟨ht.1.le, ht.2⟩
  have hu := (A.velocity_smooth ε hε).comp_contDiff
    (contDiff_const.prodMk contDiff_id) (fun x => ⟨ht', mem_univ x⟩)
  have hv := (insertion_reference_smooth A).comp_contDiff
    (contDiff_const.prodMk contDiff_id) (fun x => ⟨ht', mem_univ x⟩)
  have hp := (A.pressure_smooth ε hε).comp_contDiff
    (contDiff_const.prodMk contDiff_id) (fun x => ⟨ht', mem_univ x⟩)
  have hq := (insertion_reference_pressure_smooth A).comp_contDiff
    (contDiff_const.prodMk contDiff_id) (fun x => ⟨ht', mem_univ x⟩)
  have hpc : HasCompactSupport (fun x : Space => A.pressure ε (t,x) - A.π (t,x)) :=
    (isCompact_closedBall A.scaling.correction.x₀ A.scaling.correction.r).of_isClosed_subset
      (isClosed_tsupport _) ((A.pressureDifference_support ε hε t ht').trans
        Metric.ball_subset_closedBall)
  have hfc : HasCompactSupport (fun x : Space => A.force ε (t,x) - A.g (t,x)) :=
    (isCompact_closedBall A.scaling.correction.x₀ A.scaling.correction.r).of_isClosed_subset
      (isClosed_tsupport _) ((forceDifference_slice_support A hε t).trans
        Metric.ball_subset_closedBall)
  have hfi : Integrable (fun x : Space => A.force ε (t,x) - A.g (t,x)) :=
    (((A.forceDifference_compact ε hε).1.comp
      (contDiff_const.prodMk contDiff_id)).continuous).integrable_of_hasCompactSupport hfc
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · apply residualDifference_integral hu hv hp hq
      (velocityDifference_slice_compact A hε ht') hpc
    · exact A.incompressible ε hε t ht'
    · intro x
      have hd := A.reference.divergence t
        ⟨ht.1.le, lt_of_lt_of_le ht.2
          (le_add_of_nonneg_right A.scaling.correction.margin_pos.le)⟩ x
      rw [A.reference_velocity] at hd
      exact hd
    · intro x
      exact (((A.velocity_smooth ε hε).contDiffAt
        (prod_mem_nhds (Ico_mem_nhds ht.1 ht.2) univ_mem)).comp t
        (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
    · intro x
      exact (((insertion_reference_smooth A).contDiffAt
        (prod_mem_nhds (Ico_mem_nhds ht.1 ht.2) univ_mem)).comp t
        (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
    · simpa only [insertion_momentum_difference A hε ht] using hfi
  · intro x hx
    rw [insertion_momentum_difference A hε ht]
    apply image_eq_zero_of_notMem_tsupport (f := fun x => A.force ε (t,x) - A.g (t,x))
    exact fun hs => hx (hB (forceDifference_slice_support A hε t hs))

/-- The force correction has zero mean on a cell containing the insertion ball. -/
theorem forceDifference_cell_integral_zero' {ε t : ℝ}
    (hε : ε ∈ Ioc 0 A.ε₀) (ht : t ∈ Ico 0 A.T)
    (grid : Grid) (k₀ : Fin 3 → ℤ) (hB : A.ball ⊆ grid.cell k₀) :
    (∫ x in grid.cell k₀, (A.force ε (t,x) - A.g (t,x))) = 0 :=
  forceDifference_cell_integral_zero A (compactMomentumIntegral A) hε ht grid k₀ hB

/-- The registered force observations agree throughout the presingular slab. -/
theorem force_gridObservation_eq' (hg : MemForceR A.g) {ε t : ℝ}
    (hε : ε ∈ Ioc 0 A.ε₀) (ht : t ∈ Ico 0 A.T)
    (grid : Grid) (k₀ : Fin 3 → ℤ) (hB : A.ball ⊆ grid.cell k₀) :
    gridObservation grid (fun x => A.force ε (t,x)) =
      gridObservation grid (fun x => A.g (t,x)) :=
  force_gridObservation_eq A (compactMomentumIntegral A) hg hε ht grid k₀ hB

end BlowupDensity.Bindings
