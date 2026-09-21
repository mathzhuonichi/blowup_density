import NSFormalization.Paper1.PeriodicLifespan
import NavierStokes.PeriodicIntegration
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Pressure normalization on a periodic time slab

Subtracting the spatial cube mean from pressure leaves the velocity and the
Navier--Stokes residual unchanged.  This module proves the concrete integral,
derivative, periodicity, and pressure-gradient identities available from the
existing periodic integration library.  The endpoint `t = 0` smoothness of
the mean is recorded separately: the source differentiation theorem applies
on the open interval, while `ContDiffOn` up to the closed endpoint requires an
additional one-sided extension argument.
-/
noncomputable section
namespace NSFormalization.Paper1.PeriodicPressureNormalization

open Set MeasureTheory
open NavierStokes NavierStokes.ProblemStatement
open NavierStokes.PeriodicIntegration
open NavierStokes.PeriodicUniqueness
open NSFormalization.Source
open scoped ContDiff Topology

/-- The spatial mean of a pressure slice on the unit fundamental cube. -/
def pressureMean (p : PressureField) (t : ℝ) : ℝ :=
  cubeIntegral (fun x : Space => p (t, x))

/-- Subtract the spatial pressure mean, pointwise in time. -/
def normalizedPressure (p : PressureField) : PressureField :=
  fun z => p z - pressureMean p z.1

/-- Joint continuity on a half-open time slab passes to the cube integral,
including the initial endpoint. Compact time subintervals give local bounds. -/
theorem cubeIntegral_continuousOn_Ico {F : PressureField} {S : ℝ}
    (hF : ContinuousOn F (Ico (0 : ℝ) S ×ˢ (univ : Set Space))) :
    ContinuousOn (fun t => cubeIntegral (fun x => F (t, x))) (Ico (0 : ℝ) S) := by
  intro t ht
  let b : ℝ := (t + S) / 2
  have htb : t < b := by dsimp [b]; linarith [ht.2]
  have hbS : b < S := by dsimp [b]; linarith [ht.2]
  have hc := cubeIntegral_continuousOn_Icc
    (hF.mono (fun z hz => ⟨⟨hz.1.1, hz.1.2.trans_lt hbS⟩, hz.2⟩))
  apply (hc t ⟨ht.1, htb.le⟩).mono_of_mem_nhdsWithin
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds htb).filter_mono nhdsWithin_le_nhds] with u hu hub
  exact ⟨hu.1, hub.le⟩

/-- Differentiation under the cube integral on the original half-open slab.
At zero the derivative is relative to the physical time domain. -/
theorem hasDerivWithinAt_cubeIntegral_Ico {F G : PressureField} {S : ℝ}
    (hF : ContinuousOn F (Ico (0 : ℝ) S ×ˢ (univ : Set Space)))
    (hG : ContinuousOn G (Ico (0 : ℝ) S ×ˢ (univ : Set Space)))
    (hd : ∀ t ∈ Ico (0 : ℝ) S, ∀ x,
      HasDerivWithinAt (fun r => F (r, x)) (G (t, x)) (Ico (0 : ℝ) S) t)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) S) :
    HasDerivWithinAt (fun r => cubeIntegral (fun x => F (r, x)))
      (cubeIntegral (fun x => G (t, x))) (Ico (0 : ℝ) S) t := by
  have hdAt (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) S) :
      HasDerivAt (fun s => cubeIntegral (fun x => F (s, x)))
        (cubeIntegral (fun x => G (r, x))) r := by
    apply hasDerivAt_cubeIntegral_of_hasDerivAt isOpen_Ioo
      (hF.mono (Set.prod_mono Ioo_subset_Ico_self Subset.rfl))
      (hG.mono (Set.prod_mono Ioo_subset_Ico_self Subset.rfl)) ?_ hr
    intro s hs x
    exact (hd s ⟨hs.1.le, hs.2⟩ x).hasDerivAt (Ico_mem_nhds hs.1 hs.2)
  rcases eq_or_lt_of_le ht.1 with hzero | hpos
  · subst t
    have hS : 0 < S := ht.2
    have hnear : Ioo (0 : ℝ) S ∈ nhdsWithin 0 (Ioi 0) := by
      apply mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
      exact ⟨Iio S, Iio_mem_nhds hS, fun y hy => ⟨hy.2, hy.1⟩⟩
    have hGlim : ContinuousWithinAt
        (fun r => cubeIntegral (fun x => G (r, x))) (Ioi 0) 0 :=
      (cubeIntegral_continuousOn_Ico hG 0 ht).mono_of_mem_nhdsWithin
        (Filter.mem_of_superset hnear Ioo_subset_Ico_self)
    have hlim : Filter.Tendsto
        (fun r => deriv (fun s => cubeIntegral (fun x => F (s, x))) r)
        (nhdsWithin 0 (Ioi 0)) (nhds (cubeIntegral (fun x => G (0, x)))) := by
      apply hGlim.congr'
      filter_upwards [hnear] with r hr
      exact (hdAt r hr).deriv.symm
    exact (hasDerivWithinAt_Ici_of_tendsto_deriv
      (fun r hr => (hdAt r hr).differentiableAt.differentiableWithinAt)
      ((cubeIntegral_continuousOn_Ico hF 0 ht).mono Ioo_subset_Ico_self)
      hnear hlim).mono Ico_subset_Ici_self
  · exact (hdAt t ⟨hpos, ht.2⟩).hasDerivWithinAt

/-- Every finite differentiability order passes to the spatial cube mean on
its original half-open time domain. The derivative used at zero is the relative
Fréchet derivative, so no extension to negative time is assumed. -/
theorem cubeIntegral_contDiffOn_Ico (n : ℕ) {F : PressureField} {S : ℝ}
    (hF : ContDiffOn ℝ n F (Ico (0 : ℝ) S ×ˢ (univ : Set Space))) :
    ContDiffOn ℝ n (fun t => cubeIntegral (fun x => F (t, x))) (Ico (0 : ℝ) S) := by
  induction n generalizing F with
  | zero =>
      exact contDiffOn_zero.mpr (cubeIntegral_continuousOn_Ico hF.continuousOn)
  | succ n ih =>
      let D : Set SpaceTime := Ico (0 : ℝ) S ×ˢ (univ : Set Space)
      let G : PressureField := fun z => fderivWithin ℝ F D z (1, 0)
      have hUD : UniqueDiffOn ℝ D := (uniqueDiffOn_Ico 0 S).prod uniqueDiffOn_univ
      have hG : ContDiffOn ℝ n G D := by
        exact (hF.fderivWithin hUD (by simp)).clm_apply contDiffOn_const
      have hd (t : ℝ) (ht : t ∈ Ico (0 : ℝ) S) (x : Space) :
          HasDerivWithinAt (fun r => F (r, x)) (G (t, x)) (Ico (0 : ℝ) S) t := by
        have hfd := (hF.differentiableOn (by simp) (t, x) ⟨ht, mem_univ x⟩).hasFDerivWithinAt
        exact hfd.comp_hasDerivWithinAt t
          (((hasDerivAt_id t).prodMk (hasDerivAt_const t x)).hasDerivWithinAt)
          (show ∀ r, r ∈ Ico (0 : ℝ) S → (r, x) ∈ D from
            fun r hr => ⟨hr, mem_univ x⟩)
      have hm (t : ℝ) (ht : t ∈ Ico (0 : ℝ) S) :
          HasDerivWithinAt (fun r => cubeIntegral (fun x => F (r, x)))
            (cubeIntegral (fun x => G (t, x))) (Ico (0 : ℝ) S) t :=
        hasDerivWithinAt_cubeIntegral_Ico hF.continuousOn hG.continuousOn hd ht
      rw [show ((n + 1 : ℕ) : ℕ∞ω) = (n : ℕ∞ω) + 1 by simp]
      apply (contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Ico 0 S)).mpr
      refine ⟨fun t ht => (hm t ht).differentiableWithinAt, by simp, ?_⟩
      exact (ih hG).congr (fun t ht => (hm t ht).derivWithin ((uniqueDiffOn_Ico 0 S) t ht))

/-- Smooth pressure has a smooth cube mean up to and including time zero,
under exactly the same physical-slab hypothesis. -/
theorem pressureMean_contDiffOn {p : PressureField} {S : ℝ}
    (hp : ContDiffOn ℝ ∞ p (Ico (0 : ℝ) S ×ˢ (univ : Set Space))) :
    ContDiffOn ℝ ∞ (pressureMean p) (Ico (0 : ℝ) S) := by
  apply contDiffOn_infty.mpr
  intro n
  exact cubeIntegral_contDiffOn_Ico n (contDiffOn_infty.mp hp n)

/-- Removing the time-dependent spatial mean preserves the original smooth
pressure class on the physical half-open slab. -/
theorem normalizedPressure_contDiffOn {p : PressureField} {S : ℝ}
    (hp : ContDiffOn ℝ ∞ p (Ico (0 : ℝ) S ×ˢ (univ : Set Space))) :
    ContDiffOn ℝ ∞ (normalizedPressure p) (Ico (0 : ℝ) S ×ˢ (univ : Set Space)) := by
  exact hp.sub ((pressureMean_contDiffOn hp).comp contDiffOn_fst (fun z hz => hz.1))

theorem pressureMean_continuousOn_Icc {p : PressureField} {S b : ℝ}
    (hbS : b < S)
    (hp : ContDiffOn ℝ ∞ p (Ico (0 : ℝ) S ×ˢ (univ : Set Space))) :
    ContinuousOn (pressureMean p) (Icc (0 : ℝ) b) := by
  apply cubeIntegral_continuousOn_Icc
  intro z hz
  have hzS : z.1 ∈ Ico (0 : ℝ) S :=
    ⟨hz.1.1, hz.1.2.trans_lt hbS⟩
  exact (hp.continuousOn z ⟨hzS, hz.2⟩).mono (by
    intro y hy
    exact ⟨⟨hy.1.1, hy.1.2.trans_lt hbS⟩, hy.2⟩)

theorem pressureMean_hasDerivAt_interior {p : PressureField} {S t : ℝ}
    (hp : ContDiffOn ℝ ∞ p (Ico (0 : ℝ) S ×ˢ (univ : Set Space)))
    (ht : t ∈ Ioo (0 : ℝ) S) :
    HasDerivAt (pressureMean p)
      (cubeIntegral (fun x : Space =>
        deriv (fun s : ℝ => p (s, x)) t)) t := by
  have hp1 : ContDiffOn ℝ 1 p (Ioo (0 : ℝ) S ×ˢ (univ : Set Space)) :=
    (hp.of_le (by norm_num)).mono (fun z hz =>
      ⟨⟨hz.1.1.le, hz.1.2⟩, hz.2⟩)
  exact hasDerivAt_cubeIntegral_of_contDiffOn isOpen_Ioo hp1 ht

/-!
At the initial endpoint, the hypotheses on the physical slab only give a
relative (right-hand) statement.  An ordinary derivative at `0` is available
once the pressure has a genuine smooth extension to a two-sided time
neighbourhood.  This theorem records that minimal bridge explicitly; it does
not silently manufacture an extension from one-sided data.
-/
theorem pressureMean_hasDerivAt_zero_of_twoSided_extension
    {p : PressureField} {δ S : ℝ} (hδ : 0 < δ) (hS : 0 < S)
    (hp : ContDiffOn ℝ ∞ p (Ioo (-δ) S ×ˢ (univ : Set Space))) :
    HasDerivAt (pressureMean p)
      (cubeIntegral (fun x : Space =>
        deriv (fun s : ℝ => p (s, x)) 0)) 0 := by
  have hp1 : ContDiffOn ℝ 1 p (Ioo (-δ) S ×ˢ (univ : Set Space)) :=
    hp.of_le (by norm_num)
  have h0 : (0 : ℝ) ∈ Ioo (-δ) S :=
    ⟨neg_lt_zero.mpr hδ, hS⟩
  exact hasDerivAt_cubeIntegral_of_contDiffOn isOpen_Ioo hp1 h0

theorem pressureMean_zero_normalized_slice {p : PressureField} {S t : ℝ}
    (hp : ContDiffOn ℝ ∞ p (Ico (0 : ℝ) S ×ˢ (univ : Set Space)))
    (ht : t ∈ Ico (0 : ℝ) S) :
    cubeIntegral (fun x : Space => normalizedPressure p (t, x)) = 0 := by
  have hpslice : ContDiff ℝ ∞ (fun x : Space => p (t, x)) :=
    hp.comp_contDiff (contDiff_const.prodMk contDiff_id)
      (fun x => ⟨ht, mem_univ x⟩)
  have hpc : Continuous (fun x : Space => p (t, x)) := hpslice.continuous
  have hc : Continuous (fun _ : Space => pressureMean p t) := continuous_const
  rw [show (fun x : Space => normalizedPressure p (t, x)) =
      (fun x : Space => p (t, x) - pressureMean p t) by rfl,
    cubeIntegral_sub hpc hc]
  simp [pressureMean, cubeIntegral, cubeMeasure, cube, Measure.real]

theorem normalizedPressure_gradient_eq {p : PressureField} {S t : ℝ} {x : Space}
    (hp : ContDiffOn ℝ ∞ p (Ico (0 : ℝ) S ×ˢ (univ : Set Space)))
    (ht : t ∈ Ico (0 : ℝ) S) :
    pressureGradient (normalizedPressure p) t x = pressureGradient p t x := by
  have hps : ContDiff ℝ ∞ (fun y : Space => p (t, y)) :=
    hp.comp_contDiff (contDiff_const.prodMk contDiff_id)
      (fun y => ⟨ht, mem_univ y⟩)
  have hqs : ContDiff ℝ ∞ (fun y : Space => pressureMean p t) := contDiff_const
  have hsub := pressureGradient_sub (p := p)
    (q := fun z => pressureMean p z.1) hps hqs x
  change pressureGradient (p - fun z => pressureMean p z.1) t x =
    pressureGradient p t x
  rw [hsub]
  simp [pressureGradient]

theorem normalizedPressure_periodic {p : PressureField} {S : ℝ}
    (hp : UnitSpatialPeriodsOn (Ico (0 : ℝ) S) p) :
    UnitSpatialPeriodsOn (Ico (0 : ℝ) S) (normalizedPressure p) := by
  intro t ht x i
  simp only [normalizedPressure, pressureMean]
  rw [hp t ht x i]

/-! Normalization is idempotent: once the spatial mean has been removed,
    applying the gauge projection again leaves the pressure unchanged. -/
theorem normalizedPressure_idempotent {p : PressureField} {S : ℝ}
    (hp : ContDiffOn ℝ ∞ p (Ico (0 : ℝ) S ×ˢ (univ : Set Space)))
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) S) (x : Space) :
    normalizedPressure (normalizedPressure p) (t, x) = normalizedPressure p (t, x) := by
  have hzero := pressureMean_zero_normalized_slice hp ht
  simp only [normalizedPressure]
  rw [show pressureMean (normalizedPressure p) t = 0 by
    exact hzero]
  ring

theorem normalizedPressure_residual_eq {ν : ℝ} {u : VelocityField}
    {p : PressureField} {S t : ℝ} {x : Space}
    (hp : ContDiffOn ℝ ∞ p (Ico (0 : ℝ) S ×ˢ (univ : Set Space)))
    (ht : t ∈ Ico (0 : ℝ) S) :
    residual ν u (normalizedPressure p) t x = residual ν u p t x := by
  unfold NSFormalization.Source.residual
  rw [normalizedPressure_gradient_eq hp ht]

/-- Pressure normalization preserves an actual periodic flow witness, while
adding the zero-spatial-mean condition required by the manuscript class. -/
def normalizedFlow {ν S : ℝ} {a : Space → Space} {f : VelocityField}
    (W : NSFormalization.Paper1.PeriodicLifespan.Flow ν a f S) :
    NSFormalization.Paper1.PeriodicLifespan.Flow ν a f S where
  velocity := W.velocity
  pressure := normalizedPressure W.pressure
  horizon_pos := W.horizon_pos
  velocity_smooth := W.velocity_smooth
  pressure_smooth := normalizedPressure_contDiffOn W.pressure_smooth
  velocity_periodic := W.velocity_periodic
  pressure_periodic := normalizedPressure_periodic W.pressure_periodic
  initial := W.initial
  divergence := W.divergence
  equation := by
    intro t ht x
    rw [normalizedPressure_residual_eq W.pressure_smooth ⟨ht.1.le, ht.2⟩]
    exact W.equation t ht x

theorem normalizedFlow_mean_zero {ν S : ℝ} {a : Space → Space} {f : VelocityField}
    (W : NSFormalization.Paper1.PeriodicLifespan.Flow ν a f S)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) S) :
    cubeIntegral (fun x : Space => (normalizedFlow W).pressure (t, x)) = 0 :=
  pressureMean_zero_normalized_slice W.pressure_smooth ht

def HasMeanZeroFlow {ν S : ℝ} (a : Space → Space) (f : VelocityField) : Prop :=
  ∃ W : NSFormalization.Paper1.PeriodicLifespan.Flow ν a f S,
    ∀ t ∈ Ico (0 : ℝ) S,
      cubeIntegral (fun x : Space => (normalizedFlow W).pressure (t, x)) = 0

theorem exists_meanZeroFlow_iff {ν S : ℝ} {a : Space → Space} {f : VelocityField} :
    Nonempty (NSFormalization.Paper1.PeriodicLifespan.Flow ν a f S) ↔
      HasMeanZeroFlow (ν := ν) (S := S) a f := by
  constructor
  · rintro ⟨W⟩
    exact ⟨W, fun t ht => normalizedFlow_mean_zero W ht⟩
  · rintro ⟨W, hW⟩
    exact ⟨W⟩

end NSFormalization.Paper1.PeriodicPressureNormalization
