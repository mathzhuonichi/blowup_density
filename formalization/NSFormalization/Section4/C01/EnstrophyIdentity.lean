import NSFormalization.Section4.C01.EnergyBounds
import NSFormalization.Section4.C01.Trilinear

/-! The ordinary enstrophy identity: first spatial derivatives in physical L²,
integration by parts, and cancellation of the pressure gradient. -/

noncomputable section

open Set MeasureTheory Filter Topology
open EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev
open EulerMeanSolenoidal
open NSFormalization.Source.OrdinaryViscousStability
open NavierStokes.ProblemStatement
open scoped RealInnerProductSpace ContDiff

namespace NSFormalization.Section4.C01

open A02 (ClassicalSolutionR MemForceR)

theorem gradient_pairing_laplacian (U V : SmoothL2Field Space) :
    (∑ i : Fin 3, ⟪(U.directionalField (axis i)).toLp,
      (V.directionalField (axis i)).toLp⟫) =
      -⟪(laplacianField U).toLp, V.toLp⟫ := by
  simp only [laplacianField, toLp_sumField, sum_inner]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have h := field_directional_inner (U.directionalField (axis i)) V (axis i)
  linarith

/-- Each pressure/velocity derivative pairing vanishes by Helmholtz orthogonality;
the physical integration-by-parts identity then transfers this to the Laplacian. -/
theorem pressure_laplacian_pairing_zero (P U : SmoothL2Field Space)
    (hP : P.toLp ∈ gradientSpace) (hU : U.toLp ∈ solenoidalSpace) :
    ⟪(laplacianField U).toLp, P.toLp⟫ = 0 := by
  have hzero : (∑ i : Fin 3, ⟪(U.directionalField (axis i)).toLp,
      (P.directionalField (axis i)).toLp⟫) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have h := word_pressure_pairing_zero P U hP hU (fun _ : Fin 1 => i)
    simpa only [wordField, real_inner_comm] using h
  rw [gradient_pairing_laplacian] at hzero
  exact neg_eq_zero.mp hzero

/-- Strong time differentiation of the three first derivative fields, followed
by integration by parts. All hypotheses are supplied by the classical solution
paths below; no Sobolev path assumption is added to the solution. -/
theorem gradientEnergy_hasDerivWithinAt (S : ℝ) (hS : 0 ≤ S)
    (A B : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hA : ∀ n, Continuous (fun t => (A t).jetLp n))
    (hB : ∀ n, Continuous (fun t => (B t).jetLp n))
    (hd : ∀ t (ht : t ∈ Ioo 0 S) x,
      HasDerivAt (fun r => (A (projIcc 0 S hS r)).field x)
        ((B ⟨t, ht.1.le, ht.2.le⟩).field x) t)
    (t : Icc (0 : ℝ) S) :
    HasDerivWithinAt (fun r => gradientSq (A (projIcc 0 S hS r)).field)
      (-2 * ⟪(laplacianField (A t)).toLp, (B t).toLp⟫) (Icc (0 : ℝ) S) t := by
  have hw (i : Fin 3) :=
    (ordinaryWord_hasDerivWithinAt S hS A B hA hB hd (fun _ : Fin 1 => i) t).norm_sq
  simp only [wordField, projIcc_of_mem hS t.property] at hw
  have hh := HasDerivWithinAt.fun_sum (u := Finset.univ) (fun i _ => hw i)
  simp only [← Finset.mul_sum, gradient_pairing_laplacian, mul_neg] at hh
  have he (r : ℝ) : (∑ i : Fin 3,
      ‖((A (projIcc 0 S hS r)).directionalField (axis i)).toLp‖ ^ 2) =
      gradientSq (A (projIcc 0 S hS r)).field := gradientSq_eq_sum _
  simp_rw [he] at hh
  simpa only [neg_mul] using hh

variable {ν : ℝ} {a : A02.SpatialField} {f : A02.SpaceTimeField} {c S T : ℝ}

/-- The unclamped gradient energy on a translated interior window. -/
theorem enstrophyDerivative_shift
    (w : ClassicalSolutionR ν a f T) (hf : MemForceR f)
    (hc : 0 < c) (hcS : c ≤ S) (hST : S < T)
    {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) (S - c)) :
    HasDerivAt (fun ρ => gradientSq (slice w.velocity (ρ + c)))
      (-2 * ⟪(laplacianField (velocitySliceField w
        (show r + c ∈ Ico (0 : ℝ) T from
          ⟨by linarith [hr.1], by linarith [hr.2]⟩))).toLp,
        (temporalSliceField w hf (show r + c ∈ Ioo (0 : ℝ) T from
          ⟨by linarith [hr.1], by linarith [hr.2]⟩)).toLp⟫) r := by
  have hT' : (0 : ℝ) ≤ S - c := sub_nonneg.mpr hcS
  let ιvel : Icc (0 : ℝ) (S - c) → Icc (0 : ℝ) S := fun ρ =>
    ⟨ρ.1 + c, ⟨by have := ρ.2.1; linarith, by have := ρ.2.2; linarith⟩⟩
  have hιvel : Continuous ιvel :=
    (continuous_subtype_val.add continuous_const).subtype_mk _
  let σ : Icc (0 : ℝ) (S - c) → Icc c S := fun ρ =>
    ⟨ρ.1 + c, ⟨by have := ρ.2.1; linarith, by have := ρ.2.2; linarith⟩⟩
  have hσ : Continuous σ :=
    (continuous_subtype_val.add continuous_const).subtype_mk _
  let A : Icc (0 : ℝ) (S - c) → SmoothL2Field Space := fun ρ => velocityField w hST (ιvel ρ)
  let B : Icc (0 : ℝ) (S - c) → SmoothL2Field Space := fun ρ =>
    temporalSliceField w hf (mem_Ioo_of_mem_Icc hc hST (σ ρ).2)
  have hA : ∀ n, Continuous (fun ρ => (A ρ).jetLp n) :=
    fun n => (velocityField_jetLp_continuous w hST n).comp hιvel
  have hB : ∀ n, Continuous (fun ρ => (B ρ).jetLp n) :=
    fun n => (temporalSlicePath_jetLp_continuous w hf hc hST n).comp hσ
  have hd : ∀ t (ht : t ∈ Ioo 0 (S - c)) x,
      HasDerivAt (fun ρ => (A (projIcc 0 (S - c) hT' ρ)).field x)
        ((B ⟨t, ht.1.le, ht.2.le⟩).field x) t := by
    intro t ht x
    have htc : t + c ∈ Ioo (0 : ℝ) T :=
      ⟨by linarith [ht.1, hc], by linarith [ht.2, hST]⟩
    have hbase := velocity_hasDerivAt_time w htc x
    have hshift : HasDerivAt (fun ρ : ℝ => ρ + c) 1 t := (hasDerivAt_id t).add_const c
    have hcomp := hbase.scomp t hshift
    rw [one_smul] at hcomp
    exact hcomp.congr_of_eventuallyEq (Filter.eventually_of_mem
      (isOpen_Ioo.mem_nhds ht) (fun ρ hρ => by
        change w.velocity ((projIcc (0 : ℝ) (S - c) hT' ρ).1 + c, x) = w.velocity (ρ + c, x)
        rw [projIcc_of_mem hT' (Ioo_subset_Icc_self hρ)]))
  have hg := (gradientEnergy_hasDerivWithinAt (S - c) hT' A B hA hB hd
    ⟨r, hr.1.le, hr.2.le⟩).hasDerivAt (Icc_mem_nhds hr.1 hr.2)
  refine hg.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioo.mem_nhds hr] with ρ hρ
  rw [projIcc_of_mem hT' (Ioo_subset_Icc_self hρ)]
  rfl

/-- The carrier Laplacian uses exactly the coordinate definition of the spec. -/
theorem laplacianField_eq_lap (U : SmoothL2Field Space) :
    (laplacianField U).field = A05.lap U.field := by
  funext x
  simp only [laplacianField, sumField_field, directionalField_field,
    A05.lap, A05.dirDeriv]
  rfl

/-- The classical gradient energy derivative in physical L², before inserting
the momentum equation. -/
theorem enstrophyDerivative (w : ClassicalSolutionR ν a f T) (hf : MemForceR f)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt (fun s => gradientSq (slice w.velocity s))
      (-2 * ⟪(laplacianField (velocitySliceField w (Ioo_subset_Ico_self ht))).toLp,
        (temporalSliceField w hf ht).toLp⟫) t := by
  have hc : 0 < t / 2 := by linarith [ht.1]
  have hcS : t / 2 ≤ (t + T) / 2 := by linarith [ht.2]
  have hST : (t + T) / 2 < T := by linarith [ht.2]
  have hr : t - t / 2 ∈ Ioo (0 : ℝ) ((t + T) / 2 - t / 2) := by
    constructor <;> [linarith [ht.1]; linarith [ht.2]]
  have hg := enstrophyDerivative_shift w hf hc hcS hST hr
  have hunshift : HasDerivAt (fun s : ℝ => s - t / 2) 1 t :=
    (hasDerivAt_id t).sub_const (t / 2)
  have hcomp := hg.comp t hunshift
  simpa only [Function.comp_def, sub_add_cancel, mul_one] using hcomp

/-- The full ordinary enstrophy identity, with the nonlinear work retained and
with the exact signs and coefficients of the C01 specification. -/
theorem enstrophyIdentity (w : ClassicalSolutionR ν a f T) (hf : MemForceR f)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt (fun s => gradientSq (slice w.velocity s))
      (2 * advectionWork (slice w.velocity t) -
        2 * ν * laplacianSq (slice w.velocity t) -
        2 * pairing (slice f t) (A05.lap (slice w.velocity t))) t := by
  let U := velocitySliceField w (Ioo_subset_Ico_self ht)
  let P := pressureGradientField w hf ht
  let F := forceSliceField hf ht.1.le
  have hU : U.toLp ∈ solenoidalSpace :=
    smooth_mem_solenoidal U.field U.smooth U.memLp
      (velocitySliceField_divergence w (Ioo_subset_Ico_self ht))
  have hP : P.toLp ∈ gradientSpace :=
    gradient_mem P (fun x => w.pressure (t, x)) (contDiff_pressureSlice w ht)
      (pressureGradientField_eq_gradient w hf ht)
  have hp := pressure_laplacian_pairing_zero P U hP hU
  have h := enstrophyDerivative w hf ht
  rw [momentum_split_toLp w hf ht] at h
  change HasDerivAt _ (-2 * ⟪(laplacianField U).toLp,
    ν • (laplacianField U).toLp - (advectionField U U).toLp - P.toLp + F.toLp⟫) t at h
  rw [inner_add_right, inner_sub_right, inner_sub_right, real_inner_smul_right,
    hp, real_inner_self_eq_norm_sq] at h
  have hl : ‖(laplacianField U).toLp‖ ^ 2 = laplacianSq (slice w.velocity t) := by
    rw [norm_toLp_sq_eq_l2Sq, laplacianField_eq_lap]
    rfl
  have hn : ⟪(laplacianField U).toLp, (advectionField U U).toLp⟫ =
      advectionWork (slice w.velocity t) := by
    rw [real_inner_comm, field_inner, laplacianField_eq_lap]
    simp only [advectionField_field]
    rfl
  have hf' : ⟪(laplacianField U).toLp, F.toLp⟫ =
      pairing (slice f t) (A05.lap (slice w.velocity t)) := by
    rw [real_inner_comm, field_inner, laplacianField_eq_lap]
    rfl
  rw [hl, hn, hf'] at h
  convert h using 1
  ring

end NSFormalization.Section4.C01
