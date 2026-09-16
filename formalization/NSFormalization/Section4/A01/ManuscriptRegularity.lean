import NSFormalization.Section4.A01.ConstructorAssembly
import NSFormalization.Section4.A01.PressureGauge
import NSFormalization.Section4.C01.EnstrophyIdentityRaw

/-! # Manuscript regularity on the constructor horizon -/

noncomputable section
namespace NSFormalization.Section4.A01

open Set MeasureTheory Filter Topology
open NavierStokes.ProblemStatement
open NSFormalization.Paper3 (RealVectorSobolev)
open NSFormalization.Section4.D01
open NSFormalization.Section4.A02
  (ClassicalSolutionR SpatialField SpaceTimeField PressureGaugeEquivOn IsSolenoidal)
open RadialPotential (HasSymmetricJacobian pressurePotential)
open scoped ContDiff

/-- The manuscript's Helmholtz characterization, copied from the draft specification. -/
def IsLerayComplement (w G : SpatialField) : Prop :=
  MemLp G 2 (volume : Measure Space) ∧
    HasSymmetricJacobian G ∧
    IsSolenoidal (fun x : Space => w x - G x)

structure ManuscriptLocalRegularity (ν : ℝ) (a : SpatialField) (f : SpaceTimeField)
    (T : ℝ) (u : ClassicalSolutionR ν a f T) : Prop where
  /-- `appendix-a-local-theory.tex:71-76`: "repeated time differentiation gives
  `C^j_tH^k_x` regularity for all `j,k`, including one-sided derivatives at the
  initial time".  For every integer order `m` the velocity has an order-`m`
  angular datum at every time of `[0,T)`, and that datum path is `C^∞` in time
  on `[0,T)`.  `Ico 0 T` is `UniqueDiffOn`, so the derivative at `t = 0` is the
  one-sided one and no negative-time extension is differentiated — the same
  convention `MemForceR` uses on `futureTimes` (`Data.lean:537`).

  This strictly strengthens `ClassicalSolutionR.sobolev`, which asks only for
  `ContinuousOn`; the datum is unique (`research/D01/RECONCILIATION.md` unit
  L1), so the two paths coincide wherever both exist. -/
  sobolev_smooth : ∀ m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
    (∀ t ∈ Ico (0 : ℝ) T,
        IsSobolevDatum (m : ℝ) (fun x : Space => u.velocity (t, x)) (G t)) ∧
      ContDiffOn ℝ ∞ G (Ico (0 : ℝ) T)
  /-- `02-preliminaries.tex:90` eq:Rpressure,
  `∇p = (I−P)(f − ∇·(u⊗u)) =: G`: the pressure gradient of the solution *is*
  the Helmholtz gradient part of the forced convection residual, at every time
  of `[0,T)` including `t = 0`.

  Stated at `t = 0` as well as at interior times, because
  `02-preliminaries.tex:90` prescribes the pressure of a classical solution
  everywhere on its interval, while `ClassicalSolutionR.momentum` is imposed on
  `Ioo 0 T` only.  On `Ioo 0 T` this clause is D01 unit **L9(c)**
  (`research/D01/RECONCILIATION.md:160`, "eq:Rpressure ⟺ `momentum` given
  `divergence` and `∇p ∈ L²`"), so the genuine increment of this field is the
  `t = 0` endpoint; the redundancy is kept so that the manuscript's own
  prescription is readable in one place. -/
  pressure_recovery : ∀ t ∈ Ico (0 : ℝ) T,
    IsLerayComplement
      (fun x : Space => f (t, x) - convectionDivergence u.velocity t x)
      (fun x : Space => pressureGradient u.pressure t x)
  /-- `02-preliminaries.tex:81` eq:projected,
  `∂_tu − νΔu = −P∇·(u⊗u) + P f`, with the force `P f` of
  `appendix-a-local-theory.tex:76-77`.

  Written as `P(f − ∇·(u⊗u)) = (f − ∇·(u⊗u)) − ∇p`, which is what the previous
  clause makes it: by `pressure_recovery` the subtracted field is exactly the
  Leray complement of `f − ∇·(u⊗u)`, so this line and that one together are
  eq:projected, with no Leray operator appearing as data.

  Imposed at interior times, matching `ClassicalSolutionR.momentum`: the
  upstream `temporalDerivative` is a two-sided `fderiv` in time and need not
  exist at `t = 0` for a field smooth only on `[0,T) × R³`
  (`research/D01/RECONCILIATION.md` §1.6). -/
  projected : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : Space,
    temporalDerivative u.velocity t x - ν • spatialLaplacian u.velocity t x =
      (f (t, x) - convectionDivergence u.velocity t x) -
        pressureGradient u.pressure t x
  /-- `02-preliminaries.tex:96-100`: the scalar pressure may be taken to be the
  explicit radial potential `p(x,t) = ∫₀¹G(rx,t)·x dr` of its own gradient,
  the manuscript's chosen representative inside the gauge class.

  The solution's `pressure` is required to differ from that potential by a
  function of time only, which is exactly `02-preliminaries.tex:31` "the scalar
  pressure is determined up to a function of time".  Together with
  `pressure_recovery` this is the manuscript's full pressure prescription:
  the gradient is fixed by eq:Rpressure and the potential fixes the gauge. -/
  pressure_potential : PressureGaugeEquivOn (Ico (0 : ℝ) T)
    (pressurePotential (fun z : SpaceTime => pressureGradient u.pressure z.1 z.2))
    u.pressure


/-- All finite time orders refer to the same datum, by uniqueness. -/
theorem sobolev_smooth_of_pipeline {S : ℝ}
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (velocity : SpaceTimeField)
    (hslice : ∀ t : Icc (0 : ℝ) S,
      (fun x : Space => velocity (t.1, x)) =ᵐ[volume] ⇑(U t))
    (hpaths : ∀ j m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
      ContDiffOn ℝ j G (Icc (0 : ℝ) S) ∧
      ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (⇑(U t)) (G t.1)) :
    ∀ m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
      (∀ t ∈ Ico (0 : ℝ) S,
        IsSobolevDatum (m : ℝ) (fun x : Space => velocity (t, x)) (G t)) ∧
      ContDiffOn ℝ ∞ G (Ico (0 : ℝ) S) := by
  intro m
  obtain ⟨G, _, hG⟩ := hpaths 0 m
  refine ⟨G, ?_, ?_⟩
  · intro t ht
    exact IsSobolevDatum.congr_field (hG ⟨t, ht.1, ht.2.le⟩)
      (hslice ⟨t, ht.1, ht.2.le⟩).symm
  · apply ContDiffOn.mono (s := Icc (0 : ℝ) S) _ Ico_subset_Icc_self
    rw [contDiffOn_infty]
    intro j
    obtain ⟨H, hH, hdatum⟩ := hpaths j m
    apply hH.congr
    intro t ht
    exact isSobolevDatum_unique (hG ⟨t, ht⟩) (hdatum ⟨t, ht⟩)

/-- The momentum equation in the manuscript's tensor-divergence notation. -/
theorem projected_of_classicalSolution {ν S : ℝ} {a : SpatialField}
    {f : SpaceTimeField} (w : ClassicalSolutionR ν a f S) :
    ∀ t ∈ Ioo (0 : ℝ) S, ∀ x : Space,
      temporalDerivative w.velocity t x - ν • spatialLaplacian w.velocity t x =
        (f (t, x) - convectionDivergence w.velocity t x) -
          pressureGradient w.pressure t x := by
  intro t ht x
  exact (navierStokesResidual_eq_iff_projected ν w.velocity w.pressure t x (f (t, x))
    ((D01.contDiff_slice w.velocity_smooth ⟨ht.1.le, ht.2⟩).differentiable (by simp) x)
    (w.divergence t ⟨ht.1.le, ht.2⟩ x)).mp (w.momentum t ht x)

/-- Spatial differentiation preserves smoothness on a slab, including its time boundary. -/
theorem contDiffOn_spatial_fderiv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {s : Set ℝ} {F : SpaceTime → E}
    (hF : ContDiffOn ℝ ∞ F (s ×ˢ (univ : Set Space))) :
    ContDiffOn ℝ ∞ (fun z : SpaceTime => fderiv ℝ (fun x => F (z.1, x)) z.2)
      (s ×ˢ (univ : Set Space)) := by
  intro z hz
  have h : ContDiffOn ℝ ∞
      (fun p : SpaceTime × Space => F (p.1.1, p.2))
      ((s ×ˢ (univ : Set Space)) ×ˢ (univ : Set Space)) :=
    hF.comp (contDiffOn_fst.fst.prodMk contDiffOn_snd)
      (fun p hp => ⟨hp.1.1, mem_univ _⟩)
  simpa only [fderivWithin_univ] using
    (h (z, z.2) ⟨hz, mem_univ _⟩).fderivWithin
      contDiffWithinAt_snd uniqueDiffOn_univ (by simp) hz (fun _ _ => mem_univ _)

/-- Divergence is smooth up to the time boundary; only spatial derivatives occur. -/
theorem contDiffOn_spatialDivergence {s : Set ℝ} {F : SpaceTimeField}
    (hF : ContDiffOn ℝ ∞ F (s ×ˢ (univ : Set Space))) :
    ContDiffOn ℝ ∞ (fun z : SpaceTime => spatialDivergence F z.1 z.2)
      (s ×ˢ (univ : Set Space)) := by
  unfold spatialDivergence spatialDerivative
  apply ContDiffOn.sum
  intro i _
  exact (EuclideanSpace.proj i).contDiff.comp_contDiffOn
    ((contDiffOn_spatial_fderiv hF).clm_apply contDiffOn_const)

/-- Viscosity does not contribute to the gradient part: `div Δu = 0`. -/
theorem spatialLaplacian_solenoidal {ν S : ℝ} {a : SpatialField}
    {f : SpaceTimeField} (w : ClassicalSolutionR ν a f S)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) S) :
    IsSolenoidal (fun x => spatialLaplacian w.velocity t x) := by
  intro x
  have h := C01.laplacianField_divergence_zero (C01.velocitySliceField w ht)
    (C01.velocitySliceField_divergence w ht) x
  rw [EulerSmoothLimit.divergence_eq_coordinate_sum] at h
  have he : (NSFormalization.Source.OrdinaryViscousStability.laplacianField
      (C01.velocitySliceField w ht)).field =
      (fun y => spatialLaplacian w.velocity t y) :=
    funext (C01.laplacianField_velocitySlice_field w ht)
  rw [he] at h
  exact h

-- The spatial operator and endpoint continuity assembly needs additional elaboration budget.
set_option maxHeartbeats 400000 in
/-- Helmholtz recovery holds also at zero, by continuity of the spatial divergence.
No two-sided time derivative at zero is used. -/
theorem pressure_recovery_of_classicalSolution {ν S : ℝ} {a : SpatialField}
    {f : SpaceTimeField} (w : ClassicalSolutionR ν a f S) (hf : D01.MemForceR f) :
    ∀ t ∈ Ico (0 : ℝ) S,
      IsLerayComplement
        (fun x : Space => f (t, x) - convectionDivergence w.velocity t x)
        (fun x : Space => pressureGradient w.pressure t x) := by
  let H : SpaceTimeField := fun z =>
    (f z - advection w.velocity z.1 z.2) - pressureGradient w.pressure z.1 z.2
  have hgrad : ContDiffOn ℝ ∞
      (fun z : SpaceTime => pressureGradient w.pressure z.1 z.2)
      (Ico (0 : ℝ) S ×ˢ (univ : Set Space)) := by
    unfold pressureGradient
    exact ContDiffOn.sum (fun i _ =>
      ((contDiffOn_spatial_fderiv w.pressure_smooth).clm_apply contDiffOn_const).smul
        contDiffOn_const)
  have hH : ContDiffOn ℝ ∞ H (Ico (0 : ℝ) S ×ˢ (univ : Set Space)) :=
    ((hf.1.mono (fun z hz => ⟨hz.1.1, hz.2⟩)).sub
      ((contDiffOn_spatial_fderiv w.velocity_smooth).clm_apply w.velocity_smooth)).sub hgrad
  have hconv (t : ℝ) (ht : t ∈ Ico (0 : ℝ) S) (x : Space) :
      convectionDivergence w.velocity t x = advection w.velocity t x :=
    convectionDivergence_eq_advection w.velocity t x
      ((D01.contDiff_slice w.velocity_smooth ht).differentiable (by simp) x)
      (w.divergence t ht x)
  have hzero (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) S) (x : Space) :
      spatialDivergence H t x = 0 := by
    have heq : (fun y : Space => H (t, y)) =
        fun y => temporalDerivative w.velocity t y - ν • spatialLaplacian w.velocity t y := by
      funext y
      simpa only [H, hconv t ⟨ht.1.le, ht.2⟩ y] using
        (projected_of_classicalSolution w t ht y).symm
    have hd := D01.DivergenceTime.spatialDivergence_temporalDerivative_eq_zero w ht x
    have hl := spatialLaplacian_solenoidal w ⟨ht.1.le, ht.2⟩ x
    have hdt := (D01.contDiff_temporalDerivative_slice w hf ht).differentiable (by simp) x
    have hdl : DifferentiableAt ℝ (fun y => spatialLaplacian w.velocity t y) x := by
      have he : (fun y => spatialLaplacian w.velocity t y) =
          (NSFormalization.Source.OrdinaryViscousStability.laplacianField
            (C01.velocitySliceField w ⟨ht.1.le, ht.2⟩)).field := by
        funext y
        exact (C01.laplacianField_velocitySlice_field w ⟨ht.1.le, ht.2⟩ y).symm
      rw [he]
      exact (NSFormalization.Source.OrdinaryViscousStability.laplacianField
        (C01.velocitySliceField w ⟨ht.1.le, ht.2⟩)).smooth.differentiable (by simp) x
    simp only [spatialDivergence, spatialDerivative] at hd hl ⊢
    rw [heq]
    have hsub := fderiv_fun_sub hdt (hdl.const_smul ν)
    simp only [Pi.smul_apply] at hsub
    rw [hsub, fderiv_const_smul hdl]
    simp only [sub_apply, smul_apply,
      PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, Finset.sum_sub_distrib,
      ← Finset.mul_sum, hd, hl, mul_zero, sub_self]
  have hclosed (x : Space) : ∀ t ∈ Ico (0 : ℝ) S, spatialDivergence H t x = 0 := by
    have hc : ContinuousOn (fun t => spatialDivergence H t x) (Ico (0 : ℝ) S) :=
      (contDiffOn_spatialDivergence hH).continuousOn.comp
        (f := fun t : ℝ => (t, x))
        (continuous_id.prodMk continuous_const).continuousOn
        (fun _ ht => ⟨ht, mem_univ _⟩)
    apply Set.EqOn.of_subset_closure (fun t ht => hzero t ht x) hc continuousOn_const
      Ioo_subset_Ico_self
    rw [closure_Ioo w.horizon_pos.ne]
    exact Ico_subset_Icc_self
  intro t ht
  refine ⟨w.pressure_gradient t ht,
    PressureGauge.hasSymmetricJacobian_pressureGradient w.pressure_smooth ht, ?_⟩
  intro x
  simpa only [spatialDivergence, spatialDerivative, H, hconv t ht] using hclosed x t ht

/-- The complete manuscript regularity of any solution exported by the carrier
constructor. The only extra data are lane 192's all-order paths and the
constructor's exported slice identity. Pressure recovery and the gauge hold
for every classical solution with admissible force, so no pressure witness
needs to be exposed by the constructor or by the chosen local solution. -/
theorem manuscriptLocalRegularity_of_pipeline {ν S : ℝ} {a : SpatialField}
    {f : SpaceTimeField} (w : ClassicalSolutionR ν a f S) (hf : D01.MemForceR f)
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hslice : ∀ t : Icc (0 : ℝ) S,
      (fun x : Space => w.velocity (t.1, x)) =ᵐ[volume] ⇑(U t))
    (hpaths : ∀ j m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
      ContDiffOn ℝ j G (Icc (0 : ℝ) S) ∧
      ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (⇑(U t)) (G t.1)) :
    ManuscriptLocalRegularity ν a f S w where
  sobolev_smooth := sobolev_smooth_of_pipeline U w.velocity hslice hpaths
  pressure_recovery := pressure_recovery_of_classicalSolution w hf
  projected := projected_of_classicalSolution w
  pressure_potential := PressureGauge.pressure_potential_of_classicalSolution w

end NSFormalization.Section4.A01
