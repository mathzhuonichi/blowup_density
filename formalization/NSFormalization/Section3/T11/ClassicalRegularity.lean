import NSFormalization.Section3.T11.EnergyIdentity
import NSFormalization.Section3.T11.Transport
import NSFormalization.Section3.T11.ClassicalAssembly
import NSFormalization.Section3.T11.CriterionBridge
import NSFormalization.Section3.T11.GalileanClasses
import NSFormalization.Section3.T11.Rescaling
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Calculus.FDeriv.Extend

/-!
# T11 unit U6b — every classical periodic solution has the manuscript regularity

`paper/sections/02-preliminaries.tex:28-36,75-115` (prop:local) and
`research/T11/probes/api_on_canonical.lean`.  This module proves, with no named
input, that **every** `ClassicalSolutionT` satisfies
`PeriodicLocalRegularity` (`Section3/T11/LocalTheory.lean`), and therefore
discharges the residual hypothesis recorded by lanes 331 and 321.

## The three clauses

1. `sobolev_smooth` — for every integer order `m` the Fourier datum path
   `t ↦ datumPathT m u t` of the velocity is `C^∞` from `[0,T)` into the
   `ℓ²`-carrier `PeriodicSobolev m`.  The `ClassicalSolutionT.sobolev` field only
   supplies a *continuous* datum path, so this is genuinely new analysis.  The
   route is:

   * a **Bernstein bound** (`weight_pow_mul_norm_coeff_le`): for a smooth
     periodic complex field `g`,
     `(1+4π²|k|²)^N ‖ĝ(k)‖ ≤ 2^N (sup_cube |g| + sup_cube |Δ^N g|)`, obtained by
     iterating the Laplacian symbol (`periodicFourierCoeff_laplacian`) and
     comparing `(1+A)^N` with `2^N(1+A^N)`;
   * the **slab derivative fields** `stPartial` (frozen-time spatial derivative)
     and `stTime` (`fderivWithin` in the time direction on `Ico 0 T ×ˢ univ`,
     hence defined and smooth **up to `t = 0`**), both preserving joint
     smoothness and unit spatial periods;
   * one uniform weighted bound `W(k)^{m+2}‖û(s,k)‖ ≤ D` on every compact time
     window (`SlabSmooth.exists_coeff_bound`), by compactness of
     `J ×ˢ cube` applied to the field and its `(m+2)`-nd iterated Laplacian;
   * a **Tannery argument** (`tendsto_norm_zero_of_entries`) turning
     coefficientwise convergence plus that uniform bound into convergence in
     the `ℓ²` carrier — the weight `W(k)^{-2}` is summable
     (`summable_inverse_periodicFrequencyWeight`);
   * lane 335's differentiation under the integral sign for the interior
     derivative, the mean value inequality for the uniform slope bound, and
     `hasDerivWithinAt_Ici_of_tendsto_deriv` for the one-sided derivative at
     `t = 0`;
   * induction on the order of differentiation through
     `contDiffOn_succ_iff_derivWithin`, with the `j`-th derivative of the datum
     path being the datum path of `stTime^[j] u`.

2. `pressure_poisson` — the divergence of the projected equation
   (`ClassicalAssembly.classicalSolutionT_projected`).  `div ∂ₜu = ∂ₜ div u = 0`
   uses symmetry of the second derivative on the open slab
   (`ContDiffAt.isSymmSndFDerivAt`); `div Δu = 0` iterates lane 331's
   `Transport.spatialDivergence_directional_eq_zero`; `div ∇p` is the scalar
   Laplacian.  The identity is asserted on `Ico 0 T` but the momentum equation
   only holds on `Ioo 0 T`, so the initial time is reached by continuity of all
   three terms in `t` on the closed-at-zero slab.

3. `projected` — `ClassicalAssembly.classicalSolutionT_projected` verbatim.

## Consequences

`to_unit`, `from_unit` (lane 331's `Transport` rescalings) and
`transformed_solution` (its Galilean instance) become **unconditional**, and
`regularity_of_solution` supplies `PeriodicLocalTheoryAPI.regularity` for an
arbitrary selected solution family.
-/

noncomputable section

namespace NSFormalization.Section3.T11

open Set MeasureTheory Filter
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField SpaceTimeScalar)
open NavierStokes.PeriodicIntegration (spatialPartial cubeIntegral Coords toSpace)
open NSFormalization.Section3.T10
open scoped ContDiff ENNReal BigOperators Topology

local instance classicalRegularityNormedGroup (s : ℝ) :
    NormedAddCommGroup (PeriodicSobolev s) :=
  realPeriodicSubmodule.normedAddCommGroup

local instance classicalRegularityNormedSpace (s : ℝ) : NormedSpace ℝ (PeriodicSobolev s) :=
  realPeriodicSubmodule.normedSpace

/-- The scalar spatial Laplacian of a complex field on the torus. -/
def scalarLaplace (g : Space → ℂ) : Space → ℂ :=
  fun x ↦ ∑ j : Fin 3, spatialPartial j (spatialPartial j g) x

theorem contDiff_spatialPartial {g : Space → ℂ} (hs : ContDiff ℝ ∞ g) (j : Fin 3) :
    ContDiff ℝ ∞ (spatialPartial j g) :=
  (hs.fderiv_right (by simp)).clm_apply contDiff_const

theorem contDiff_scalarLaplace {g : Space → ℂ} (hs : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (scalarLaplace g) :=
  ContDiff.sum (fun j _ ↦ contDiff_spatialPartial (contDiff_spatialPartial hs j) j)

theorem isPeriodicSpatial_spatialPartial {g : Space → ℂ} (hp : IsPeriodicSpatial g) (j : Fin 3) :
    IsPeriodicSpatial (spatialPartial j g) :=
  NavierStokes.PeriodicUniqueness.spatial_partial_periodic hp j

theorem isPeriodicSpatial_scalarLaplace {g : Space → ℂ} (hp : IsPeriodicSpatial g) :
    IsPeriodicSpatial (scalarLaplace g) := by
  intro x i
  show ∑ j : Fin 3, spatialPartial j (spatialPartial j g) (x + coordinateVector i) =
    ∑ j : Fin 3, spatialPartial j (spatialPartial j g) x
  exact Finset.sum_congr rfl fun j _ ↦
    isPeriodicSpatial_spatialPartial (isPeriodicSpatial_spatialPartial hp j) j x i

/-- The Fourier symbol of the iterated scalar Laplacian. -/
theorem periodicFourierCoeff_scalarLaplace_iterate (N : ℕ) :
    ∀ {g : Space → ℂ}, IsPeriodicSpatial g → ContDiff ℝ ∞ g →
      ∀ k : PeriodicFrequency,
        periodicFourierCoeff (scalarLaplace^[N] g) k =
          (-(4 * (Real.pi : ℂ) ^ 2 * ∑ j : Fin 3, ((k j : ℝ) : ℂ) ^ 2)) ^ N *
            periodicFourierCoeff g k := by
  induction N with
  | zero => intro g _ _ k; simp
  | succ N ih =>
    intro g hp hs k
    rw [Function.iterate_succ_apply]
    rw [ih (isPeriodicSpatial_scalarLaplace hp) (contDiff_scalarLaplace hs) k]
    have hL : periodicFourierCoeff (scalarLaplace g) k =
        (-(4 * Real.pi ^ 2 * ∑ j : Fin 3, (k j : ℝ) ^ 2) : ℂ) * periodicFourierCoeff g k :=
      periodicFourierCoeff_laplacian hp (hs.of_le (by simp)) k
    rw [hL]
    push_cast
    ring


theorem contDiff_scalarLaplace_iterate (N : ℕ) :
    ∀ {g : Space → ℂ}, ContDiff ℝ ∞ g → ContDiff ℝ ∞ (scalarLaplace^[N] g) := by
  induction N with
  | zero => intro g hg; simpa using hg
  | succ N ih =>
    intro g hg
    rw [Function.iterate_succ_apply]
    exact ih (contDiff_scalarLaplace hg)

theorem isPeriodicSpatial_scalarLaplace_iterate (N : ℕ) :
    ∀ {g : Space → ℂ}, IsPeriodicSpatial g → IsPeriodicSpatial (scalarLaplace^[N] g) := by
  induction N with
  | zero => intro g hg; simpa using hg
  | succ N ih =>
    intro g hg
    rw [Function.iterate_succ_apply]
    exact ih (isPeriodicSpatial_scalarLaplace hg)

/-- **Bernstein-type bound.** The weighted Fourier coefficients of a smooth
periodic field are controlled by the field and its `N`-th iterated Laplacian on the
closed unit cube. -/
theorem weight_pow_mul_norm_coeff_le (N : ℕ) {g : Space → ℂ} (hp : IsPeriodicSpatial g)
    (hs : ContDiff ℝ ∞ g) {C₀ C₁ : ℝ}
    (h0 : ∀ y ∈ Icc (0 : Coords) 1, ‖g (toSpace y)‖ ≤ C₀)
    (h1 : ∀ y ∈ Icc (0 : Coords) 1, ‖(scalarLaplace^[N] g) (toSpace y)‖ ≤ C₁)
    (k : PeriodicFrequency) :
    periodicFrequencyWeight k ^ N * ‖periodicFourierCoeff g k‖ ≤ 2 ^ N * (C₀ + C₁) := by
  set A : ℝ := 4 * Real.pi ^ 2 * ∑ j : Fin 3, (k j : ℝ) ^ 2 with hA
  have hA0 : 0 ≤ A := by positivity
  have hW : periodicFrequencyWeight k = 1 + A := rfl
  have hb0 : ‖periodicFourierCoeff g k‖ ≤ C₀ :=
    norm_periodicFourierCoeff_le_of_cube_bound hs.continuous h0 k
  have hb1 : ‖periodicFourierCoeff (scalarLaplace^[N] g) k‖ ≤ C₁ :=
    norm_periodicFourierCoeff_le_of_cube_bound
      (contDiff_scalarLaplace_iterate N hs).continuous h1 k
  have hsym := periodicFourierCoeff_scalarLaplace_iterate N hp hs k
  have hcast : (-(4 * (Real.pi : ℂ) ^ 2 * ∑ j : Fin 3, ((k j : ℝ) : ℂ) ^ 2)) =
      ((-A : ℝ) : ℂ) := by rw [hA]; push_cast; ring
  rw [hcast] at hsym
  have hnorm : A ^ N * ‖periodicFourierCoeff g k‖ ≤ C₁ := by
    have : ‖((-A : ℝ) : ℂ) ^ N * periodicFourierCoeff g k‖ ≤ C₁ := by rw [← hsym]; exact hb1
    rwa [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_neg,
      abs_of_nonneg hA0] at this
  have hmax : (max 1 A) ^ N ≤ 1 + A ^ N := by
    rcases le_total A 1 with h | h
    · rw [max_eq_left h, one_pow]
      have : 0 ≤ A ^ N := pow_nonneg hA0 N
      linarith
    · rw [max_eq_right h]
      linarith
  have hpow : (1 + A) ^ N ≤ 2 ^ N * (1 + A ^ N) := by
    have h1' : (1 : ℝ) + A ≤ 2 * max 1 A := by
      rcases le_total A 1 with h | h
      · rw [max_eq_left h]; linarith
      · rw [max_eq_right h]; linarith
    calc (1 + A) ^ N ≤ (2 * max 1 A) ^ N := by
          exact pow_le_pow_left₀ (by linarith) h1' N
      _ = 2 ^ N * (max 1 A) ^ N := by rw [mul_pow]
      _ ≤ 2 ^ N * (1 + A ^ N) := by
          exact mul_le_mul_of_nonneg_left hmax (by positivity)
  have hng : 0 ≤ ‖periodicFourierCoeff g k‖ := norm_nonneg _
  calc periodicFrequencyWeight k ^ N * ‖periodicFourierCoeff g k‖
      = (1 + A) ^ N * ‖periodicFourierCoeff g k‖ := by rw [hW]
    _ ≤ (2 ^ N * (1 + A ^ N)) * ‖periodicFourierCoeff g k‖ := by
        exact mul_le_mul_of_nonneg_right hpow hng
    _ = 2 ^ N * (‖periodicFourierCoeff g k‖ + A ^ N * ‖periodicFourierCoeff g k‖) := by ring
    _ ≤ 2 ^ N * (C₀ + C₁) := by
        have : ‖periodicFourierCoeff g k‖ + A ^ N * ‖periodicFourierCoeff g k‖ ≤ C₀ + C₁ := by
          linarith
        exact mul_le_mul_of_nonneg_left this (by positivity)


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The space-time slab of a classical solution on `[0,T)`. -/
def slabT (T : ℝ) : Set SpaceTime := Ico (0 : ℝ) T ×ˢ (univ : Set Space)

theorem uniqueDiffOn_slabT (T : ℝ) : UniqueDiffOn ℝ (slabT T) :=
  UniqueDiffOn.prod (uniqueDiffOn_Ico 0 T) uniqueDiffOn_univ

theorem mem_slabT {T t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) (x : Space) :
    ((t, x) : SpaceTime) ∈ slabT T := ⟨ht, mem_univ x⟩

/-- Spatial partial derivative of a space-time field, with time frozen. -/
def stPartial (j : Fin 3) (F : SpaceTime → E) : SpaceTime → E :=
  fun z ↦ fderiv ℝ (fun y : Space ↦ F (z.1, y)) z.2 (coordinateVector j)

theorem stPartial_slice (j : Fin 3) (F : SpaceTime → E) (t : ℝ) :
    (fun x : Space ↦ stPartial j F (t, x)) = spatialPartial j (fun y : Space ↦ F (t, y)) := rfl

/-- Every time slice of a field smooth on the slab is smooth on all of space. -/
theorem slice_contDiff_of_slab {T : ℝ} {F : SpaceTime → E} (hF : ContDiffOn ℝ ∞ F (slabT T))
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) : ContDiff ℝ ∞ (fun y : Space ↦ F (t, y)) :=
  hF.comp_contDiff (contDiff_const.prodMk contDiff_id) (fun x ↦ mem_slabT ht x)

/-- The frozen-time spatial derivative is the slab derivative in a spatial direction. -/
theorem stPartial_eq_fderivWithin {T : ℝ} {F : SpaceTime → E}
    (hF : ContDiffOn ℝ ∞ F (slabT T)) (j : Fin 3) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) (x : Space) :
    stPartial j F (t, x) =
      fderivWithin ℝ F (slabT T) (t, x) ((0 : ℝ), coordinateVector j) := by
  set D := fderivWithin ℝ F (slabT T) (t, x) with hD
  have hz : ((t, x) : SpaceTime) ∈ slabT T := mem_slabT ht x
  have hFd : HasFDerivWithinAt F D (slabT T) (t, x) :=
    ((hF.differentiableOn (by simp)) (t, x) hz).hasFDerivWithinAt
  have hg : HasFDerivWithinAt (fun y : Space ↦ ((t, y) : SpaceTime))
      (ContinuousLinearMap.inr ℝ ℝ Space) univ x := by
    have := (hasFDerivAt_const (𝕜 := ℝ) t x).prodMk (hasFDerivAt_id x)
    exact this.hasFDerivWithinAt
  have hcomp : HasFDerivWithinAt (fun y : Space ↦ F (t, y))
      (D.comp (ContinuousLinearMap.inr ℝ ℝ Space)) univ x :=
    HasFDerivWithinAt.comp x hFd hg (fun y _ ↦ mem_slabT ht y)
  rw [hasFDerivWithinAt_univ] at hcomp
  change fderiv ℝ (fun y : Space ↦ F (t, y)) x (coordinateVector j) = _
  rw [hcomp.fderiv]
  rfl

theorem contDiffOn_stPartial {T : ℝ} {F : SpaceTime → E}
    (hF : ContDiffOn ℝ ∞ F (slabT T)) (j : Fin 3) :
    ContDiffOn ℝ ∞ (stPartial j F) (slabT T) := by
  have hfd : ContDiffOn ℝ ∞ (fun z ↦ fderivWithin ℝ F (slabT T) z) (slabT T) :=
    hF.fderivWithin (uniqueDiffOn_slabT T) (by simp)
  have happ : ContDiffOn ℝ ∞
      (fun z ↦ fderivWithin ℝ F (slabT T) z ((0 : ℝ), coordinateVector j)) (slabT T) :=
    hfd.clm_apply contDiffOn_const
  refine happ.congr ?_
  intro z hz
  have h := stPartial_eq_fderivWithin (T := T) (F := F) hF j (t := z.1) hz.1 z.2
  simpa using h

/-- The slab derivative is invariant under unit spatial shifts. -/
theorem fderivWithin_slabT_periodic {T : ℝ} {F : SpaceTime → E}
    (hF : ContDiffOn ℝ ∞ F (slabT T)) (hFp : IsPeriodicOn (Ico (0 : ℝ) T) F)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) (x : Space) (i : Fin 3) :
    fderivWithin ℝ F (slabT T) (t, x + coordinateVector i) =
      fderivWithin ℝ F (slabT T) (t, x) := by
  set c : SpaceTime := ((0 : ℝ), coordinateVector i) with hc
  have hadd : ∀ (s : ℝ) (y : Space), ((s, y) : SpaceTime) + c = (s, y + coordinateVector i) := by
    intro s y
    simp [hc]
  have hmaps : ∀ z ∈ slabT T, z + c ∈ slabT T := by
    rintro ⟨s, y⟩ ⟨hs, -⟩
    rw [hadd]
    exact ⟨hs, mem_univ _⟩
  have hshift : ∀ z ∈ slabT T, F (z + c) = F z := by
    rintro ⟨s, y⟩ ⟨hs, -⟩
    rw [hadd]
    exact hFp s hs y i
  have hz : ((t, x) : SpaceTime) ∈ slabT T := mem_slabT ht x
  have hzc : ((t, x) : SpaceTime) + c ∈ slabT T := hmaps _ hz
  have hFd : HasFDerivWithinAt F (fderivWithin ℝ F (slabT T) ((t, x) + c)) (slabT T)
      ((t, x) + c) := ((hF.differentiableOn (by simp)) _ hzc).hasFDerivWithinAt
  have hg : HasFDerivWithinAt (fun z : SpaceTime ↦ z + c)
      (ContinuousLinearMap.id ℝ SpaceTime) (slabT T) (t, x) :=
    ((hasFDerivAt_id ((t, x) : SpaceTime)).add_const c).hasFDerivWithinAt
  have hcomp : HasFDerivWithinAt (fun z : SpaceTime ↦ F (z + c))
      ((fderivWithin ℝ F (slabT T) ((t, x) + c)).comp (ContinuousLinearMap.id ℝ SpaceTime))
      (slabT T) (t, x) := HasFDerivWithinAt.comp (t, x) hFd hg hmaps
  rw [ContinuousLinearMap.comp_id] at hcomp
  have hcongr : HasFDerivWithinAt F (fderivWithin ℝ F (slabT T) ((t, x) + c)) (slabT T) (t, x) :=
    hcomp.congr (fun y hy ↦ (hshift y hy).symm) (hshift _ hz).symm
  have huniq : UniqueDiffWithinAt ℝ (slabT T) (t, x) := uniqueDiffOn_slabT T _ hz
  have hfin := hcongr.fderivWithin huniq
  rw [← hadd t x, ← hfin]


theorem stPartial_periodic {T : ℝ} {F : SpaceTime → E} (hF : ContDiffOn ℝ ∞ F (slabT T))
    (hFp : IsPeriodicOn (Ico (0 : ℝ) T) F) (j : Fin 3) :
    IsPeriodicOn (Ico (0 : ℝ) T) (stPartial j F) := by
  intro t ht x i
  rw [stPartial_eq_fderivWithin hF j ht (x + coordinateVector i),
    stPartial_eq_fderivWithin hF j ht x, fderivWithin_slabT_periodic hF hFp ht x i]

/-- The time derivative of a space-time field, taken within the slab so that it is
defined and smooth up to the initial time. -/
def stTime (T : ℝ) (F : SpaceTime → E) : SpaceTime → E :=
  fun z ↦ fderivWithin ℝ F (slabT T) z ((1 : ℝ), (0 : Space))

theorem contDiffOn_stTime {T : ℝ} {F : SpaceTime → E} (hF : ContDiffOn ℝ ∞ F (slabT T)) :
    ContDiffOn ℝ ∞ (stTime T F) (slabT T) :=
  (hF.fderivWithin (uniqueDiffOn_slabT T) (by simp)).clm_apply contDiffOn_const

theorem stTime_periodic {T : ℝ} {F : SpaceTime → E} (hF : ContDiffOn ℝ ∞ F (slabT T))
    (hFp : IsPeriodicOn (Ico (0 : ℝ) T) F) : IsPeriodicOn (Ico (0 : ℝ) T) (stTime T F) := by
  intro t ht x i
  show fderivWithin ℝ F (slabT T) (t, x + coordinateVector i) ((1 : ℝ), (0 : Space)) =
    fderivWithin ℝ F (slabT T) (t, x) ((1 : ℝ), (0 : Space))
  rw [fderivWithin_slabT_periodic hF hFp ht x i]

/-- The slab time derivative differentiates each time line, one-sidedly at `t = 0`. -/
theorem hasDerivWithinAt_stTime {T : ℝ} {F : SpaceTime → E} (hF : ContDiffOn ℝ ∞ F (slabT T))
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) (x : Space) :
    HasDerivWithinAt (fun s : ℝ ↦ F (s, x)) (stTime T F (t, x)) (Ico (0 : ℝ) T) t := by
  have hFd : HasFDerivWithinAt F (fderivWithin ℝ F (slabT T) (t, x)) (slabT T) (t, x) :=
    ((hF.differentiableOn (by simp)) (t, x) (mem_slabT ht x)).hasFDerivWithinAt
  have hg : HasDerivWithinAt (fun s : ℝ ↦ ((s, x) : SpaceTime)) ((1 : ℝ), (0 : Space))
      (Ico (0 : ℝ) T) t :=
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x)).hasDerivWithinAt
  exact HasFDerivWithinAt.comp_hasDerivWithinAt t hFd hg (fun s hs ↦ mem_slabT hs x)

theorem temporalDerivative_eq_stTime {T : ℝ} {F : SpaceTimeField}
    (hF : ContDiffOn ℝ ∞ F (slabT T)) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) (x : Space) :
    temporalDerivative F t x = stTime T F (t, x) := by
  have hnhds : Ico (0 : ℝ) T ∈ 𝓝 t :=
    mem_nhds_iff.mpr ⟨Ioo (0 : ℝ) T, Ioo_subset_Ico_self, isOpen_Ioo, ht⟩
  have h := (hasDerivWithinAt_stTime hF (Ioo_subset_Ico_self ht) x).hasDerivAt hnhds
  exact h.deriv.symm ▸ rfl

/-- The spatial Laplacian of a complex space-time field, time frozen. -/
def stLaplace (F : SpaceTime → ℂ) : SpaceTime → ℂ :=
  fun z ↦ ∑ j : Fin 3, stPartial j (stPartial j F) z

theorem stLaplace_slice (F : SpaceTime → ℂ) (t : ℝ) :
    (fun x : Space ↦ stLaplace F (t, x)) = scalarLaplace (fun y : Space ↦ F (t, y)) := rfl

theorem contDiffOn_stLaplace {T : ℝ} {F : SpaceTime → ℂ} (hF : ContDiffOn ℝ ∞ F (slabT T)) :
    ContDiffOn ℝ ∞ (stLaplace F) (slabT T) :=
  ContDiffOn.sum (fun j _ ↦ contDiffOn_stPartial (contDiffOn_stPartial hF j) j)

theorem stLaplace_periodic {T : ℝ} {F : SpaceTime → ℂ} (hF : ContDiffOn ℝ ∞ F (slabT T))
    (hFp : IsPeriodicOn (Ico (0 : ℝ) T) F) : IsPeriodicOn (Ico (0 : ℝ) T) (stLaplace F) := by
  intro t ht x i
  change ∑ j : Fin 3, stPartial j (stPartial j F) (t, x + coordinateVector i) = _
  exact Finset.sum_congr rfl fun j _ ↦
    stPartial_periodic (contDiffOn_stPartial hF j)
      (stPartial_periodic hF hFp j) j t ht x i

theorem contDiffOn_stLaplace_iterate {T : ℝ} (N : ℕ) :
    ∀ {F : SpaceTime → ℂ}, ContDiffOn ℝ ∞ F (slabT T) →
      ContDiffOn ℝ ∞ (stLaplace^[N] F) (slabT T) := by
  induction N with
  | zero => intro F hF; simpa using hF
  | succ N ih =>
    intro F hF
    rw [Function.iterate_succ_apply]
    exact ih (contDiffOn_stLaplace hF)

theorem stLaplace_iterate_periodic {T : ℝ} (N : ℕ) :
    ∀ {F : SpaceTime → ℂ}, ContDiffOn ℝ ∞ F (slabT T) → IsPeriodicOn (Ico (0 : ℝ) T) F →
      IsPeriodicOn (Ico (0 : ℝ) T) (stLaplace^[N] F) := by
  induction N with
  | zero => intro F _ hFp; simpa using hFp
  | succ N ih =>
    intro F hF hFp
    rw [Function.iterate_succ_apply]
    exact ih (contDiffOn_stLaplace hF) (stLaplace_periodic hF hFp)

theorem stLaplace_iterate_slice (N : ℕ) :
    ∀ (F : SpaceTime → ℂ) (t : ℝ),
      (fun x : Space ↦ (stLaplace^[N] F) (t, x)) =
        scalarLaplace^[N] (fun y : Space ↦ F (t, y)) := by
  induction N with
  | zero => intro F t; simp
  | succ N ih =>
    intro F t
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    rw [ih (stLaplace F) t, stLaplace_slice F t]


theorem norm_sq_eq_sum_tsum {s : ℝ} (A : PeriodicSobolev s) :
    ‖A‖ ^ 2 = ∑ i : Fin 3, ∑' k : PeriodicFrequency, ‖A.1 i k‖ ^ 2 := by
  have hcomp : ∀ i : Fin 3, HasSum (fun k ↦ ‖A.1 i k‖ ^ 2) (‖A.1 i‖ ^ 2) := by
    intro i
    have h := lp.hasSum_norm (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) (A.1 i)
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h
  have hnorm : ‖A‖ ^ 2 = ∑ i : Fin 3, ‖A.1 i‖ ^ 2 := by
    change ‖A.1‖ ^ 2 = _
    exact PiLp.norm_sq_eq_of_L2 _ _
  rw [hnorm]
  exact Finset.sum_congr rfl fun i _ ↦ ((hcomp i).tsum_eq).symm

/-- Tannery for the datum carrier: entrywise convergence plus one uniform weighted
bound forces convergence of the norms. -/
theorem tendsto_norm_zero_of_entries {ι : Type*} {l : Filter ι} {s : ℝ}
    (E : ι → PeriodicSobolev s) {D : ℝ}
    (hb : ∀ᶠ n in l, ∀ (i : Fin 3) (k : PeriodicFrequency),
      periodicFrequencyWeight k * ‖(E n).1 i k‖ ≤ D)
    (hpt : ∀ (i : Fin 3) (k : PeriodicFrequency),
      Tendsto (fun n ↦ (E n).1 i k) l (𝓝 0)) :
    Tendsto (fun n ↦ ‖E n‖) l (𝓝 0) := by
  have hsummable : Summable (fun k : PeriodicFrequency ↦
      D ^ 2 * (periodicFrequencyWeight k ^ 2)⁻¹) :=
    summable_inverse_periodicFrequencyWeight.mul_left _
  have hstep : ∀ i : Fin 3,
      Tendsto (fun n ↦ ∑' k : PeriodicFrequency, ‖(E n).1 i k‖ ^ 2) l (𝓝 0) := by
    intro i
    have h := tendsto_tsum_of_dominated_convergence (𝓕 := l)
      (f := fun n k ↦ ‖(E n).1 i k‖ ^ 2) (g := fun _ : PeriodicFrequency ↦ (0 : ℝ))
      (bound := fun k ↦ D ^ 2 * (periodicFrequencyWeight k ^ 2)⁻¹) hsummable
      (fun k ↦ by
        have := (hpt i k).norm
        simpa using this.pow 2)
      (by
        filter_upwards [hb] with n hn
        intro k
        have hw := periodicFrequencyWeight_pos k
        have hk := hn i k
        have hnn : 0 ≤ periodicFrequencyWeight k * ‖(E n).1 i k‖ :=
          mul_nonneg hw.le (norm_nonneg _)
        have hsq : (periodicFrequencyWeight k * ‖(E n).1 i k‖) ^ 2 ≤ D ^ 2 := by
          nlinarith
        have hpos : (0 : ℝ) < periodicFrequencyWeight k ^ 2 := pow_pos hw 2
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), ← div_eq_mul_inv,
          le_div_iff₀ hpos]
        rw [mul_pow] at hsq
        linarith [hsq])
    simpa using h
  have hsq : Tendsto (fun n ↦ ‖E n‖ ^ 2) l (𝓝 0) := by
    have h2 := tendsto_finsetSum (Finset.univ : Finset (Fin 3)) (fun i _ ↦ hstep i)
    simp only [Finset.sum_const_zero] at h2
    exact h2.congr fun n ↦ (norm_sq_eq_sum_tsum (E n)).symm
  have := (Real.continuous_sqrt.tendsto 0).comp hsq
  simp only [Function.comp_def, Real.sqrt_zero] at this
  refine this.congr fun n ↦ ?_
  rw [Real.sqrt_sq (norm_nonneg _)]


/-! ## Uniform weighted coefficient bounds on a compact time window -/

theorem exists_weighted_coeff_bound {T : ℝ} {Φ : SpaceTime → ℂ}
    (hΦ : ContDiffOn ℝ ∞ Φ (slabT T)) (hΦp : IsPeriodicOn (Ico (0 : ℝ) T) Φ) (N : ℕ)
    {J : Set ℝ} (hJ : IsCompact J) (hJI : J ⊆ Ico (0 : ℝ) T) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ s ∈ J, ∀ k : PeriodicFrequency,
      periodicFrequencyWeight k ^ N *
        ‖periodicFourierCoeff (fun x : Space ↦ Φ (s, x)) k‖ ≤ D := by
  have hcompactK : IsCompact (J ×ˢ (toSpace '' (Icc (0 : Coords) 1))) :=
    hJ.prod (isCompact_Icc.image toSpace.continuous)
  have hsub : J ×ˢ (toSpace '' (Icc (0 : Coords) 1)) ⊆ slabT T :=
    fun z hz ↦ ⟨hJI hz.1, mem_univ _⟩
  obtain ⟨C₀, hC₀⟩ := hcompactK.exists_bound_of_continuousOn (hΦ.continuousOn.mono hsub)
  obtain ⟨C₁, hC₁⟩ := hcompactK.exists_bound_of_continuousOn
    ((contDiffOn_stLaplace_iterate N hΦ).continuousOn.mono hsub)
  refine ⟨max (2 ^ N * (C₀ + C₁)) 0, le_max_right _ _, ?_⟩
  intro s hs k
  refine le_trans ?_ (le_max_left _ _)
  have hsm : ContDiff ℝ ∞ (fun y : Space ↦ Φ (s, y)) := slice_contDiff_of_slab hΦ (hJI hs)
  have hsp : IsPeriodicSpatial (fun y : Space ↦ Φ (s, y)) := fun x i ↦ hΦp s (hJI hs) x i
  refine weight_pow_mul_norm_coeff_le N hsp hsm (fun y hy ↦ hC₀ (s, toSpace y) ⟨hs, ⟨y, hy, rfl⟩⟩)
    (fun y hy ↦ ?_) k
  rw [← congrFun (stLaplace_iterate_slice N Φ s) (toSpace y)]
  exact hC₁ (s, toSpace y) ⟨hs, ⟨y, hy, rfl⟩⟩

/-! ## Space-time fields that are smooth and periodic on the slab -/

/-- The standing hypothesis of this section: smooth on the closed-at-zero slab and
spatially periodic there. -/
structure SlabSmooth (T : ℝ) (V : SpaceTimeField) : Prop where
  smooth : ContDiffOn ℝ ∞ V (slabT T)
  periodic : IsPeriodicOn (Ico (0 : ℝ) T) V

theorem SlabSmooth.time {T : ℝ} {V : SpaceTimeField} (h : SlabSmooth T V) :
    SlabSmooth T (stTime T V) :=
  ⟨contDiffOn_stTime h.smooth, stTime_periodic h.smooth h.periodic⟩

theorem SlabSmooth.slice_smooth {T : ℝ} {V : SpaceTimeField} (h : SlabSmooth T V) {t : ℝ}
    (ht : t ∈ Ico (0 : ℝ) T) : ContDiff ℝ ∞ (fun x : Space ↦ V (t, x)) :=
  slice_contDiff_of_slab h.smooth ht

theorem SlabSmooth.slice_periodic {T : ℝ} {V : SpaceTimeField} (h : SlabSmooth T V) {t : ℝ}
    (ht : t ∈ Ico (0 : ℝ) T) : IsPeriodicSpatial (fun x : Space ↦ V (t, x)) :=
  fun x i ↦ h.periodic t ht x i

theorem SlabSmooth.datum_exists {T : ℝ} {V : SpaceTimeField} (h : SlabSmooth T V) (m : ℕ)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    ∃ A : PeriodicSobolev (m : ℝ), IsPeriodicDatum (m : ℝ) (fun x : Space ↦ V (t, x)) A :=
  exists_periodicDatum_smooth _ (h.slice_smooth ht) (h.slice_periodic ht)

theorem SlabSmooth.component {T : ℝ} {V : SpaceTimeField} (h : SlabSmooth T V) (i : Fin 3) :
    ContDiffOn ℝ ∞ (fun z : SpaceTime ↦ ((V z i : ℝ) : ℂ)) (slabT T) :=
  (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) i)).contDiff.comp_contDiffOn h.smooth

theorem SlabSmooth.component_periodic {T : ℝ} {V : SpaceTimeField} (h : SlabSmooth T V)
    (i : Fin 3) : IsPeriodicOn (Ico (0 : ℝ) T) (fun z : SpaceTime ↦ ((V z i : ℝ) : ℂ)) := by
  intro t ht x j
  simp only
  rw [h.periodic t ht x j]

/-- One constant bounds every weighted velocity coefficient on a compact time window. -/
theorem SlabSmooth.exists_coeff_bound {T : ℝ} {V : SpaceTimeField} (h : SlabSmooth T V) (N : ℕ)
    {J : Set ℝ} (hJ : IsCompact J) (hJI : J ⊆ Ico (0 : ℝ) T) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ s ∈ J, ∀ (i : Fin 3) (k : PeriodicFrequency),
      periodicFrequencyWeight k ^ N * ‖velocityCoeffT V i k s‖ ≤ D := by
  choose D hD0 hD using fun i : Fin 3 ↦
    exists_weighted_coeff_bound (h.component i) (h.component_periodic i) N hJ hJI
  refine ⟨∑ i : Fin 3, D i, Finset.sum_nonneg fun i _ ↦ hD0 i, ?_⟩
  intro s hs i k
  refine le_trans (hD i s hs k) ?_
  exact Finset.single_le_sum (f := D) (fun j _ ↦ hD0 j) (Finset.mem_univ i)

/-! ## The datum path of a slab-smooth field -/

open Classical in
/-- The order-`m` Fourier datum of the time slice, chosen wherever it exists. -/
def datumPathT (m : ℕ) (V : SpaceTimeField) (t : ℝ) : PeriodicSobolev (m : ℝ) :=
  if h : ∃ A : PeriodicSobolev (m : ℝ), IsPeriodicDatum (m : ℝ) (fun x : Space ↦ V (t, x)) A then
    h.choose else 0

theorem datumPathT_spec {m : ℕ} {V : SpaceTimeField} {t : ℝ}
    (h : ∃ A : PeriodicSobolev (m : ℝ), IsPeriodicDatum (m : ℝ) (fun x : Space ↦ V (t, x)) A) :
    IsPeriodicDatum (m : ℝ) (fun x : Space ↦ V (t, x)) (datumPathT m V t) := by
  classical
  unfold datumPathT
  split_ifs with hh
  · exact hh.choose_spec
  · exact absurd h hh

theorem datumPathT_entry {T : ℝ} {V : SpaceTimeField} (h : SlabSmooth T V) (m : ℕ) {t : ℝ}
    (ht : t ∈ Ico (0 : ℝ) T) (i : Fin 3) (k : PeriodicFrequency) :
    (datumPathT m V t).1 i k =
      (periodicFrequencyWeight k ^ ((m : ℕ) / 2 : ℝ) : ℝ) • velocityCoeffT V i k t :=
  (datumPathT_spec (h.datum_exists m ht)).2.2 i k


theorem tendsto_of_entries {ι : Type*} {l : Filter ι} {s : ℝ} (A : ι → PeriodicSobolev s)
    (B : PeriodicSobolev s) {D : ℝ}
    (hb : ∀ᶠ n in l, ∀ (i : Fin 3) (k : PeriodicFrequency),
      periodicFrequencyWeight k * ‖(A n).1 i k - B.1 i k‖ ≤ D)
    (hpt : ∀ (i : Fin 3) (k : PeriodicFrequency),
      Tendsto (fun n ↦ (A n).1 i k) l (𝓝 (B.1 i k))) :
    Tendsto A l (𝓝 B) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine tendsto_norm_zero_of_entries (D := D) (fun n ↦ A n - B) ?_ (fun i k ↦ ?_)
  · filter_upwards [hb] with n hn
    intro i k
    exact hn i k
  · have := (hpt i k).sub (tendsto_const_nhds (x := B.1 i k) (f := l))
    simpa using this

theorem one_le_periodicFrequencyWeight (k : PeriodicFrequency) :
    (1 : ℝ) ≤ periodicFrequencyWeight k := by
  have h : (0 : ℝ) ≤ 4 * Real.pi ^ 2 * ∑ i : Fin 3, (k i : ℝ) ^ 2 := by positivity
  unfold periodicFrequencyWeight
  linarith

/-- One weight is absorbed by the `m+2` reserve of the Bernstein bound. -/
theorem weight_entry_le (m : ℕ) (k : PeriodicFrequency) (d : ℂ) :
    periodicFrequencyWeight k *
        ‖(periodicFrequencyWeight k ^ ((m : ℝ) / 2) : ℝ) • d‖ ≤
      periodicFrequencyWeight k ^ (m + 2) * ‖d‖ := by
  have hw := periodicFrequencyWeight_pos k
  have hw1 := one_le_periodicFrequencyWeight k
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hw.le _), ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg d)
  have h1 : periodicFrequencyWeight k * periodicFrequencyWeight k ^ ((m : ℝ) / 2) =
      periodicFrequencyWeight k ^ (1 + (m : ℝ) / 2) := by
    rw [Real.rpow_add hw, Real.rpow_one]
  rw [h1, ← Real.rpow_natCast (periodicFrequencyWeight k) (m + 2)]
  refine Real.rpow_le_rpow_of_exponent_le hw1 ?_
  push_cast
  linarith

/-- The Fourier coefficient path is continuous up to the initial time. -/
theorem continuousOn_velocityCoeffT {T : ℝ} {V : SpaceTimeField} (h : SlabSmooth T V)
    {b : ℝ} (hb : Icc (0 : ℝ) b ⊆ Ico (0 : ℝ) T) (i : Fin 3) (k : PeriodicFrequency) :
    ContinuousOn (velocityCoeffT V i k) (Icc (0 : ℝ) b) := by
  have hchar : Continuous (fun z : SpaceTime ↦
      NSFormalization.Paper1.periodicCharacter (-k) z.2) :=
    (NSFormalization.Paper1.periodicCharacter_smooth (-k)).continuous.comp continuous_snd
  have hcomp : ContinuousOn (fun z : SpaceTime ↦ ((V z i : ℝ) : ℂ))
      (Icc (0 : ℝ) b ×ˢ (univ : Set Space)) :=
    (h.component i).continuousOn.mono (fun z hz ↦ ⟨hb hz.1, mem_univ _⟩)
  have hF : ContinuousOn (fun z : SpaceTime ↦
      NSFormalization.Paper1.periodicCharacter (-k) z.2 * ((V z i : ℝ) : ℂ))
      (Icc (0 : ℝ) b ×ˢ (univ : Set Space)) := hchar.continuousOn.mul hcomp
  have hcube := NavierStokes.PeriodicIntegration.cubeIntegral_continuousOn_Icc hF
  exact hcube.congr fun s _ ↦ NSFormalization.Paper1.periodicFourierCoeff_eq_cube _ k

/-- The datum path is continuous on the closed-at-zero time interval. -/
theorem continuousWithinAt_datumPathT {T : ℝ} {V : SpaceTimeField} (h : SlabSmooth T V)
    (m : ℕ) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    ContinuousWithinAt (datumPathT m V) (Ico (0 : ℝ) T) t := by
  obtain ⟨b, htb, hbT⟩ : ∃ b : ℝ, t < b ∧ b < T :=
    ⟨(t + T) / 2, by linarith [ht.2], by linarith [ht.1, ht.2]⟩
  have hbI : Icc (0 : ℝ) b ⊆ Ico (0 : ℝ) T := fun s hs ↦ ⟨hs.1, lt_of_le_of_lt hs.2 hbT⟩
  have htb' : t ∈ Icc (0 : ℝ) b := ⟨ht.1, htb.le⟩
  obtain ⟨D, hD0, hD⟩ := h.exists_coeff_bound (m + 2) isCompact_Icc hbI
  have hJnhds : Icc (0 : ℝ) b ∈ 𝓝[Ico (0 : ℝ) T] t := by
    refine mem_of_superset (inter_mem_nhdsWithin (Ico (0 : ℝ) T) (Iio_mem_nhds htb)) ?_
    exact fun s hs ↦ ⟨hs.1.1, le_of_lt hs.2⟩
  have hle : 𝓝[Ico (0 : ℝ) T] t ≤ 𝓝[Icc (0 : ℝ) b] t := nhdsWithin_le_iff.mpr hJnhds
  refine tendsto_of_entries (D := 2 * D) _ _ ?_ ?_
  · filter_upwards [hJnhds, self_mem_nhdsWithin] with y hy hyI
    intro i k
    rw [datumPathT_entry h m hyI i k, datumPathT_entry h m ht i k, ← smul_sub]
    refine le_trans (weight_entry_le m k _) ?_
    have h1 := hD y hy i k
    have h2 := hD t htb' i k
    have h3 : ‖velocityCoeffT V i k y - velocityCoeffT V i k t‖ ≤
        ‖velocityCoeffT V i k y‖ + ‖velocityCoeffT V i k t‖ := norm_sub_le _ _
    have hwpos : (0 : ℝ) < periodicFrequencyWeight k ^ (m + 2) :=
      pow_pos (periodicFrequencyWeight_pos k) _
    nlinarith [hwpos]
  · intro i k
    have hc : Tendsto (velocityCoeffT V i k) (𝓝[Ico (0 : ℝ) T] t)
        (𝓝 (velocityCoeffT V i k t)) :=
      ((continuousOn_velocityCoeffT h hbI i k).continuousWithinAt htb').mono_left hle
    have hs : Tendsto
        (fun y ↦ (periodicFrequencyWeight k ^ ((m : ℝ) / 2) : ℝ) • velocityCoeffT V i k y)
        (𝓝[Ico (0 : ℝ) T] t)
        (𝓝 ((periodicFrequencyWeight k ^ ((m : ℝ) / 2) : ℝ) • velocityCoeffT V i k t)) :=
      hc.const_smul _
    rw [datumPathT_entry h m ht i k]
    refine hs.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (datumPathT_entry h m hy i k).symm


theorem slope_entry {s : ℝ} (P : ℝ → PeriodicSobolev s) (t y : ℝ) (i : Fin 3)
    (k : PeriodicFrequency) :
    (slope P t y).1 i k = (y - t)⁻¹ • ((P y).1 i k - (P t).1 i k) := rfl

/-- Lane 335's differentiation under the integral sign, restated with the slab time
derivative so that it iterates. -/
theorem hasDerivAt_velocityCoeffT_slab {T : ℝ} {V : SpaceTimeField} (h : SlabSmooth T V)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) (i : Fin 3) (k : PeriodicFrequency) :
    HasDerivAt (velocityCoeffT V i k) (velocityCoeffT (stTime T V) i k t) t := by
  have hopen : ContDiffOn ℝ ∞ V (Ioo (0 : ℝ) T ×ˢ (univ : Set Space)) :=
    h.smooth.mono (fun z hz ↦ ⟨Ioo_subset_Ico_self hz.1, mem_univ _⟩)
  have hd := hasDerivAt_velocityCoeffT isOpen_Ioo hopen ht i k
  have heq : velocityDerivCoeffT V i k t = velocityCoeffT (stTime T V) i k t := by
    unfold velocityDerivCoeffT velocityCoeffT
    congr 1
    funext x
    rw [temporalDerivative_eq_stTime h.smooth ht x]
  rwa [heq] at hd

/-- **The datum path is differentiable at every interior time**, with the datum of the
time-derivative field as derivative. -/
theorem hasDerivAt_datumPathT {T : ℝ} {V : SpaceTimeField} (h : SlabSmooth T V) (m : ℕ)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt (datumPathT m V) (datumPathT m (stTime T V) t) t := by
  have ht0 : 0 < t := ht.1
  have htT : t < T := ht.2
  have htIco : t ∈ Ico (0 : ℝ) T := Ioo_subset_Ico_self ht
  set ε : ℝ := min t (T - t) / 2 with hεdef
  have hε : 0 < ε := by
    have hmin : 0 < min t (T - t) := lt_min ht0 (by linarith)
    simpa [hεdef] using half_pos hmin
  have hεt : ε ≤ t / 2 := by
    have hmin : min t (T - t) ≤ t := min_le_left _ _
    rw [hεdef]
    linarith
  have hεT : ε ≤ (T - t) / 2 := by
    have hmin : min t (T - t) ≤ T - t := min_le_right _ _
    rw [hεdef]
    linarith
  have hJI : Icc (t - ε) (t + ε) ⊆ Ioo (0 : ℝ) T := fun y hy ↦
    ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hJI' : Icc (t - ε) (t + ε) ⊆ Ico (0 : ℝ) T := fun y hy ↦ Ioo_subset_Ico_self (hJI hy)
  have htJ : t ∈ Icc (t - ε) (t + ε) := ⟨by linarith, by linarith⟩
  obtain ⟨D, hD0, hD⟩ := h.time.exists_coeff_bound (m + 2) isCompact_Icc hJI'
  have hJnhds : Icc (t - ε) (t + ε) ∈ 𝓝 t := Icc_mem_nhds (by linarith) (by linarith)
  rw [hasDerivAt_iff_tendsto_slope]
  refine tendsto_of_entries (D := 2 * D) _ _ ?_ ?_
  · filter_upwards [nhdsWithin_le_nhds hJnhds, self_mem_nhdsWithin] with y hy hyne
    intro i k
    have hyI : y ∈ Ico (0 : ℝ) T := hJI' hy
    have hwpos : (0 : ℝ) < periodicFrequencyWeight k ^ (m + 2) :=
      pow_pos (periodicFrequencyWeight_pos k) _
    set c : ℝ → ℂ := velocityCoeffT V i k with hc
    set c' : ℝ → ℂ := velocityCoeffT (stTime T V) i k with hc'
    have hbound : ∀ s ∈ Icc (t - ε) (t + ε),
        ‖c' s‖ ≤ D * (periodicFrequencyWeight k ^ (m + 2))⁻¹ := by
      intro s hs
      have hs' := hD s hs i k
      rw [← div_eq_mul_inv, le_div_iff₀ hwpos, mul_comm]
      exact hs'
    have hmvt : ‖c y - c t‖ ≤ (D * (periodicFrequencyWeight k ^ (m + 2))⁻¹) * ‖y - t‖ :=
      Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (f := c) (f' := c') (s := Icc (t - ε) (t + ε))
        (fun s hs ↦ (hasDerivAt_velocityCoeffT_slab h (hJI hs) i k).hasDerivWithinAt)
        hbound (convex_Icc _ _) htJ hy
    have hne : y - t ≠ 0 := sub_ne_zero.mpr hyne
    have habs : (0 : ℝ) < |y - t| := abs_pos.mpr hne
    have hslope : ‖(y - t)⁻¹ • (c y - c t)‖ ≤
        D * (periodicFrequencyWeight k ^ (m + 2))⁻¹ := by
      rw [norm_smul, norm_inv]
      simp only [Real.norm_eq_abs] at hmvt ⊢
      calc |y - t|⁻¹ * ‖c y - c t‖
          ≤ |y - t|⁻¹ * ((D * (periodicFrequencyWeight k ^ (m + 2))⁻¹) * |y - t|) :=
            mul_le_mul_of_nonneg_left hmvt (by positivity)
        _ = D * (periodicFrequencyWeight k ^ (m + 2))⁻¹ := by field_simp
    have hdiff : ‖(y - t)⁻¹ • (c y - c t) - c' t‖ ≤
        2 * (D * (periodicFrequencyWeight k ^ (m + 2))⁻¹) := by
      refine le_trans (norm_sub_le _ _) ?_
      have h2 := hbound t htJ
      linarith
    rw [slope_entry, datumPathT_entry h m hyI i k, datumPathT_entry h m htIco i k,
      datumPathT_entry h.time m htIco i k, ← smul_sub, smul_comm, ← smul_sub]
    refine le_trans (weight_entry_le m k _) ?_
    calc periodicFrequencyWeight k ^ (m + 2) * ‖(y - t)⁻¹ • (c y - c t) - c' t‖
        ≤ periodicFrequencyWeight k ^ (m + 2) *
            (2 * (D * (periodicFrequencyWeight k ^ (m + 2))⁻¹)) :=
          mul_le_mul_of_nonneg_left hdiff hwpos.le
      _ = 2 * D := by field_simp
  · intro i k
    have hd := hasDerivAt_velocityCoeffT_slab h ht i k
    rw [hasDerivAt_iff_tendsto_slope] at hd
    have hs := hd.const_smul (periodicFrequencyWeight k ^ ((m : ℝ) / 2) : ℝ)
    rw [datumPathT_entry h.time m htIco i k]
    refine hs.congr' ?_
    filter_upwards [nhdsWithin_le_nhds hJnhds] with y hy
    have hyI : y ∈ Ico (0 : ℝ) T := hJI' hy
    rw [slope_def_module, slope_entry, datumPathT_entry h m hyI i k,
      datumPathT_entry h m htIco i k, ← smul_sub]
    exact smul_comm _ _ _


/-- **The datum path is one-sidedly differentiable at the initial time as well.** -/
theorem hasDerivWithinAt_datumPathT {T : ℝ} {V : SpaceTimeField} (h : SlabSmooth T V) (m : ℕ)
    (hT : 0 < T) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    HasDerivWithinAt (datumPathT m V) (datumPathT m (stTime T V) t) (Ico (0 : ℝ) T) t := by
  rcases eq_or_lt_of_le ht.1 with h0 | h0
  · subst h0
    have hIoo : Ioo (0 : ℝ) T ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT hT
    have hdiffOn : DifferentiableOn ℝ (datumPathT m V) (Ioo (0 : ℝ) T) := fun y hy ↦
      (hasDerivAt_datumPathT h m hy).differentiableAt.differentiableWithinAt
    have hcont : ContinuousWithinAt (datumPathT m V) (Ioo (0 : ℝ) T) 0 :=
      (continuousWithinAt_datumPathT h m ht).mono Ioo_subset_Ico_self
    have hIcoMem : Ico (0 : ℝ) T ∈ 𝓝[>] (0 : ℝ) :=
      mem_of_superset hIoo Ioo_subset_Ico_self
    have hle : 𝓝[>] (0 : ℝ) ≤ 𝓝[Ico (0 : ℝ) T] (0 : ℝ) := nhdsWithin_le_iff.mpr hIcoMem
    have hlim : Tendsto (datumPathT m (stTime T V)) (𝓝[>] (0 : ℝ))
        (𝓝 (datumPathT m (stTime T V) 0)) :=
      (continuousWithinAt_datumPathT h.time m ht).mono_left hle
    have hderiv : Tendsto (fun x ↦ deriv (datumPathT m V) x) (𝓝[>] (0 : ℝ))
        (𝓝 (datumPathT m (stTime T V) 0)) := by
      refine hlim.congr' ?_
      filter_upwards [hIoo] with y hy
      exact ((hasDerivAt_datumPathT h m hy).deriv).symm
    exact (hasDerivWithinAt_Ici_of_tendsto_deriv hdiffOn hcont hIoo hderiv).mono
      (fun y hy ↦ hy.1)
  · exact (hasDerivAt_datumPathT h m ⟨h0, ht.2⟩).hasDerivWithinAt

theorem contDiffOn_datumPathT_nat {T : ℝ} (hT : 0 < T) (m : ℕ) (n : ℕ) :
    ∀ {V : SpaceTimeField}, SlabSmooth T V →
      ContDiffOn ℝ (n : ℕ∞ω) (datumPathT m V) (Ico (0 : ℝ) T) := by
  have hU : UniqueDiffOn ℝ (Ico (0 : ℝ) T) := uniqueDiffOn_Ico 0 T
  induction n with
  | zero =>
    intro V h
    rw [Nat.cast_zero, contDiffOn_zero]
    exact fun t ht ↦ continuousWithinAt_datumPathT h m ht
  | succ n ih =>
    intro V h
    rw [Nat.cast_succ, contDiffOn_succ_iff_derivWithin hU]
    refine ⟨fun t ht ↦ (hasDerivWithinAt_datumPathT h m hT ht).differentiableWithinAt, by simp,
      ?_⟩
    refine (ih h.time).congr ?_
    intro t ht
    exact (hasDerivWithinAt_datumPathT h m hT ht).derivWithin (hU t ht)

/-- **The order-`m` datum path of a slab-smooth periodic field is `C^∞` on `[0,T)`.** -/
theorem contDiffOn_datumPathT {T : ℝ} (hT : 0 < T) (m : ℕ) {V : SpaceTimeField}
    (h : SlabSmooth T V) : ContDiffOn ℝ ∞ (datumPathT m V) (Ico (0 : ℝ) T) :=
  contDiffOn_infty.mpr fun n ↦ contDiffOn_datumPathT_nat hT m n h


/-! ## The pressure Poisson equation -/

/-- Divergence of a purely spatial field. -/
def divSpatial (g : Space → Space) (x : Space) : ℝ :=
  ∑ i : Fin 3, (fderiv ℝ g x (coordinateVector i)) i

theorem spatialDivergence_eq_divSpatial (F : SpaceTimeField) (t : ℝ) (x : Space) :
    spatialDivergence F t x = divSpatial (fun y : Space ↦ F (t, y)) x := rfl

theorem divSpatial_sub {g h : Space → Space} {x : Space}
    (hg : DifferentiableAt ℝ g x) (hh : DifferentiableAt ℝ h x) :
    divSpatial (fun y ↦ g y - h y) x = divSpatial g x - divSpatial h x := by
  unfold divSpatial
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hd : HasFDerivAt (fun y ↦ g y - h y) (fderiv ℝ g x - fderiv ℝ h x) x :=
    hg.hasFDerivAt.sub hh.hasFDerivAt
  rw [hd.fderiv]
  rfl

theorem divSpatial_smul (c : ℝ) {g : Space → Space} {x : Space}
    (hg : DifferentiableAt ℝ g x) :
    divSpatial (fun y ↦ c • g y) x = c * divSpatial g x := by
  unfold divSpatial
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hd : HasFDerivAt (fun y ↦ c • g y) (c • fderiv ℝ g x) x :=
    hg.hasFDerivAt.const_smul c
  rw [hd.fderiv]
  rfl

theorem divSpatial_sum {ι : Type*} (s : Finset ι) {g : ι → Space → Space} {x : Space}
    (hg : ∀ i ∈ s, DifferentiableAt ℝ (g i) x) :
    divSpatial (fun y ↦ ∑ i ∈ s, g i y) x = ∑ i ∈ s, divSpatial (g i) x := by
  unfold divSpatial
  have hd : ∀ i : Fin 3, fderiv ℝ (fun y ↦ ∑ j ∈ s, g j y) x (coordinateVector i) =
      ∑ j ∈ s, fderiv ℝ (g j) x (coordinateVector i) := by
    intro i
    have hd : HasFDerivAt (fun y ↦ ∑ j ∈ s, g j y) (∑ j ∈ s, fderiv ℝ (g j) x) x :=
      HasFDerivAt.fun_sum (fun j hj ↦ (hg j hj).hasFDerivAt)
    rw [hd.fderiv]
    simp
  simp_rw [hd, euclidean_sum_apply]
  exact Finset.sum_comm

/-- The divergence of the pressure gradient is the scalar Laplacian. -/
theorem divSpatial_pressureGradient {p : SpaceTimeScalar} {t : ℝ}
    (hp : ContDiff ℝ ∞ (fun y : Space ↦ p (t, y))) (x : Space) :
    divSpatial (fun y : Space ↦ pressureGradient p t y) x = scalarSpatialLaplacianT p t x := by
  have hsm : ContDiff ℝ ∞ (fun y : Space ↦ pressureGradient p t y) := by
    unfold pressureGradient
    refine ContDiff.sum fun i _ ↦ ?_
    exact ((NavierStokes.PeriodicUniqueness.spatial_partial_contDiff hp i)).smul contDiff_const
  have hsum := spatialDivergence_eq_sum (w := fun z : SpaceTime ↦ pressureGradient p z.1 z.2)
    (t := t) hsm x
  rw [spatialDivergence_eq_divSpatial] at hsum
  rw [hsum]
  unfold scalarSpatialLaplacianT
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have heq : (fun y : Space ↦ pressureGradient p t y i) =
      fun y : Space ↦ fderiv ℝ (fun z : Space ↦ p (t, z)) y (coordinateVector i) :=
    funext fun y ↦ pressureGradient_component p t y i
  unfold spatialPartial
  rw [heq]

/-- The divergence of the spatial Laplacian of a divergence-free slice vanishes. -/
theorem divSpatial_spatialLaplacian_eq_zero {u : SpaceTimeField} {t : ℝ}
    (hu : ContDiff ℝ ∞ (fun y : Space ↦ u (t, y)))
    (hdiv : ∀ y : Space, spatialDivergence u t y = 0) (x : Space) :
    divSpatial (fun y : Space ↦ spatialLaplacian u t y) x = 0 := by
  have hstep1 : ∀ (i : Fin 3) (y : Space),
      spatialDivergence (fun z : SpaceTime ↦ spatialDerivative u z.1 z.2 (coordinateVector i))
        t y = 0 := fun i y ↦
    Transport.spatialDivergence_directional_eq_zero hu hdiv (coordinateVector i) y
  have hsmooth : ∀ i : Fin 3, ContDiff ℝ ∞
      (fun y : Space ↦ spatialDerivative u t y (coordinateVector i)) :=
    fun i ↦ (hu.fderiv_right (by simp)).clm_apply contDiff_const
  have hstep2 : ∀ (i : Fin 3) (y : Space),
      spatialDivergence (fun z : SpaceTime ↦
        spatialDerivative (fun z' : SpaceTime ↦
          spatialDerivative u z'.1 z'.2 (coordinateVector i)) z.1 z.2
            (coordinateVector i)) t y = 0 := by
    intro i y
    exact Transport.spatialDivergence_directional_eq_zero (hsmooth i) (hstep1 i)
      (coordinateVector i) y
  have hlap : (fun y : Space ↦ spatialLaplacian u t y) = fun y : Space ↦
      ∑ i : Fin 3, spatialDerivative (fun z' : SpaceTime ↦
        spatialDerivative u z'.1 z'.2 (coordinateVector i)) t y (coordinateVector i) := rfl
  rw [hlap, divSpatial_sum]
  · refine Finset.sum_eq_zero fun i _ ↦ ?_
    have := hstep2 i x
    rw [spatialDivergence_eq_divSpatial] at this
    exact this
  · intro i _
    have h2 : ContDiff ℝ ∞ (fun y : Space ↦ spatialDerivative
        (fun z' : SpaceTime ↦ spatialDerivative u z'.1 z'.2 (coordinateVector i)) t y
          (coordinateVector i)) :=
      ((hsmooth i).fderiv_right (by simp)).clm_apply contDiff_const
    exact h2.differentiable (by simp) x


/-- **The divergence of the time derivative of a divergence-free solution vanishes**:
symmetry of the second derivative on the open slab. -/
theorem divSpatial_temporalDerivative_eq_zero {T : ℝ} {u : SpaceTimeField}
    (hu : ContDiffOn ℝ ∞ u (Ioo (0 : ℝ) T ×ˢ (univ : Set Space)))
    (hdiv : ∀ s ∈ Ioo (0 : ℝ) T, ∀ y : Space, spatialDivergence u s y = 0)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) (x : Space) :
    divSpatial (fun y : Space ↦ temporalDerivative u t y) x = 0 := by
  set S : Set SpaceTime := Ioo (0 : ℝ) T ×ˢ (univ : Set Space) with hSdef
  have hSopen : IsOpen S := isOpen_Ioo.prod isOpen_univ
  have hmem : ∀ y : Space, ((t, y) : SpaceTime) ∈ S := fun y ↦ ⟨ht, mem_univ y⟩
  set F' : SpaceTime → (SpaceTime →L[ℝ] Space) := fderiv ℝ u with hF'def
  have hud : ∀ z ∈ S, HasFDerivAt u (F' z) z := fun z hz ↦
    ((hu.contDiffAt (hSopen.mem_nhds hz)).differentiableAt (by simp)).hasFDerivAt
  have hF'smooth : ContDiffOn ℝ ∞ F' S := hu.fderiv_of_isOpen hSopen (by simp)
  set F'' : SpaceTime →L[ℝ] SpaceTime →L[ℝ] Space := fderiv ℝ F' (t, x) with hF''def
  have hF''d : HasFDerivAt F' F'' (t, x) :=
    ((hF'smooth.contDiffAt (hSopen.mem_nhds (hmem x))).differentiableAt (by simp)).hasFDerivAt
  have hsymm : ∀ v w : SpaceTime, F'' v w = F'' w v :=
    (hu.contDiffAt (hSopen.mem_nhds (hmem x))).isSymmSndFDerivAt (by simp)
  have hspat : ∀ z ∈ S, ∀ v : Space, spatialDerivative u z.1 z.2 v = F' z ((0 : ℝ), v) := by
    intro z hz v
    have hg := (hasFDerivAt_const (𝕜 := ℝ) z.1 z.2).prodMk (hasFDerivAt_id z.2)
    have hcomp : HasFDerivAt (fun w : Space ↦ u (z.1, w)) _ z.2 := (hud z hz).comp z.2 hg
    change fderiv ℝ (fun w : Space ↦ u (z.1, w)) z.2 v = _
    rw [hcomp.fderiv]
    simp
  have htime : ∀ y : Space, temporalDerivative u t y = F' (t, y) ((1 : ℝ), (0 : Space)) := by
    intro y
    have hg : HasDerivAt (fun s : ℝ ↦ ((s, y) : SpaceTime)) ((1 : ℝ), (0 : Space)) t :=
      (hasDerivAt_id t).prodMk (hasDerivAt_const t y)
    have hcomp : HasDerivAt (fun s : ℝ ↦ u (s, y)) (F' (t, y) ((1 : ℝ), (0 : Space))) t := by
      have := (hud _ (hmem y)).comp_hasDerivAt t hg
      simpa [Function.comp_def] using this
    change fderiv ℝ (fun s : ℝ ↦ u (s, y)) t 1 = _
    exact hcomp.deriv
  set g : SpaceTime → ℝ := fun z ↦ ∑ i : Fin 3, (F' z ((0 : ℝ), coordinateVector i)) i with hgdef
  have hgzero : ∀ z ∈ S, g z = 0 := by
    intro z hz
    have h0 := hdiv z.1 hz.1 z.2
    rw [← h0]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [hspat z hz]
  have hgd : HasFDerivAt g
      (∑ i : Fin 3, (EuclideanSpace.proj (𝕜 := ℝ) i).comp
        (F''.flip ((0 : ℝ), coordinateVector i))) (t, x) := by
    refine HasFDerivAt.fun_sum fun i _ ↦ ?_
    have hi := hF''d.clm_apply (hasFDerivAt_const ((0 : ℝ), coordinateVector i) ((t, x) : SpaceTime))
    have h2 := (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp ((t, x) : SpaceTime) hi
    simpa [Function.comp_def] using h2
  have hgz : HasFDerivAt g (0 : SpaceTime →L[ℝ] ℝ) ((t, x) : SpaceTime) := by
    have heq : g =ᶠ[𝓝 ((t, x) : SpaceTime)] fun _ ↦ (0 : ℝ) := by
      filter_upwards [hSopen.mem_nhds (hmem x)] with z hz
      exact hgzero z hz
    exact (hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) ((t, x) : SpaceTime)).congr_of_eventuallyEq heq
  have huniq := hgd.unique hgz
  have happ := congrArg (fun L : SpaceTime →L[ℝ] ℝ ↦ L ((1 : ℝ), (0 : Space))) huniq
  simp only [sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, zero_apply] at happ
  have hg2 := (hasFDerivAt_const (𝕜 := ℝ) t x).prodMk (hasFDerivAt_id x)
  have hG : HasFDerivAt (fun y : Space ↦ F' (t, y)) _ x := hF''d.comp x hg2
  have hdir : ∀ e : Space,
      fderiv ℝ (fun y : Space ↦ F' (t, y) ((1 : ℝ), (0 : Space))) x e =
        F'' ((0 : ℝ), e) ((1 : ℝ), (0 : Space)) := by
    intro e
    have h := (hG.clm_apply (hasFDerivAt_const ((1 : ℝ), (0 : Space)) x)).fderiv
    rw [h]
    simp
  have hfun : (fun y : Space ↦ temporalDerivative u t y) =
      fun y : Space ↦ F' (t, y) ((1 : ℝ), (0 : Space)) := funext htime
  unfold divSpatial
  rw [hfun]
  simp only [hdir]
  calc ∑ i : Fin 3, (F'' ((0 : ℝ), coordinateVector i) ((1 : ℝ), (0 : Space))) i
      = ∑ i : Fin 3, (F'' ((1 : ℝ), (0 : Space)) ((0 : ℝ), coordinateVector i)) i :=
        Finset.sum_congr rfl fun i _ ↦ by rw [hsymm]
    _ = 0 := happ


theorem contDiff_spatialLaplacian {u : SpaceTimeField} {t : ℝ}
    (hu : ContDiff ℝ ∞ (fun y : Space ↦ u (t, y))) :
    ContDiff ℝ ∞ (fun y : Space ↦ spatialLaplacian u t y) := by
  have he : (fun y : Space ↦ spatialLaplacian u t y) = fun y : Space ↦
      ∑ i : Fin 3, fderiv ℝ (fun y' : Space ↦ spatialDerivative u t y' (coordinateVector i))
        y (coordinateVector i) := rfl
  rw [he]
  refine ContDiff.sum fun i _ ↦ ?_
  have h1 : ContDiff ℝ ∞ (fun y' : Space ↦ spatialDerivative u t y' (coordinateVector i)) :=
    (hu.fderiv_right (by simp)).clm_apply contDiff_const
  exact (h1.fderiv_right (by simp)).clm_apply contDiff_const

theorem contDiff_pressureGradient {p : SpaceTimeScalar} {t : ℝ}
    (hp : ContDiff ℝ ∞ (fun y : Space ↦ p (t, y))) :
    ContDiff ℝ ∞ (fun y : Space ↦ pressureGradient p t y) := by
  unfold pressureGradient
  refine ContDiff.sum fun i _ ↦ ?_
  exact ((NavierStokes.PeriodicUniqueness.spatial_partial_contDiff hp i)).smul contDiff_const

/-- The Poisson equation at interior times: the divergence of the projected equation. -/
theorem pressure_poisson_interior {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (hf : ContDiff ℝ ∞ f) (w : ClassicalSolutionT ν a f T) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T)
    (x : Space) :
    scalarSpatialLaplacianT w.pressure t x =
      spatialDivergence f t x -
        spatialDivergence (fun z : SpaceTime ↦
          convectionDivergenceT w.velocity z.1 z.2) t x := by
  have htIco : t ∈ Ico (0 : ℝ) T := Ioo_subset_Ico_self ht
  have hus : ContDiff ℝ ∞ (fun y : Space ↦ w.velocity (t, y)) :=
    slice_contDiff_of_slab w.velocity_smooth htIco
  have hps : ContDiff ℝ ∞ (fun y : Space ↦ w.pressure (t, y)) :=
    slice_contDiff_of_slab w.pressure_smooth htIco
  have hopen : ContDiffOn ℝ ∞ w.velocity (Ioo (0 : ℝ) T ×ˢ (univ : Set Space)) :=
    w.velocity_smooth.mono (fun z hz ↦ ⟨Ioo_subset_Ico_self hz.1, mem_univ _⟩)
  have hA : ContDiff ℝ ∞ (fun y : Space ↦ temporalDerivative w.velocity t y) :=
    (NavierStokes.ResidualRegularity.contDiffOn_temporalDerivative
      (isOpen_Ioo.prod isOpen_univ) hopen).comp_contDiff
      (contDiff_const.prodMk contDiff_id) (fun y ↦ ⟨ht, mem_univ y⟩)
  have hB : ContDiff ℝ ∞ (fun y : Space ↦ spatialLaplacian w.velocity t y) :=
    contDiff_spatialLaplacian hus
  have hC : ContDiff ℝ ∞ (fun y : Space ↦ f (t, y)) :=
    hf.comp (contDiff_const.prodMk contDiff_id)
  have hDn : ContDiff ℝ ∞ (fun y : Space ↦ convectionDivergenceT w.velocity t y) :=
    convectionDivergenceT_spatial_contDiff hus
  have hEe : ContDiff ℝ ∞ (fun y : Space ↦ pressureGradient w.pressure t y) :=
    contDiff_pressureGradient hps
  have heq : (fun y : Space ↦
        temporalDerivative w.velocity t y - ν • spatialLaplacian w.velocity t y) =
      fun y : Space ↦ (f (t, y) - convectionDivergenceT w.velocity t y) -
        pressureGradient w.pressure t y :=
    funext fun y ↦ classicalSolutionT_projected w t ht y
  have hdA : DifferentiableAt ℝ (fun y : Space ↦ temporalDerivative w.velocity t y) x :=
    hA.differentiable (by simp) x
  have hdB : DifferentiableAt ℝ (fun y : Space ↦ spatialLaplacian w.velocity t y) x :=
    hB.differentiable (by simp) x
  have hdC : DifferentiableAt ℝ (fun y : Space ↦ f (t, y)) x := hC.differentiable (by simp) x
  have hdDn : DifferentiableAt ℝ (fun y : Space ↦ convectionDivergenceT w.velocity t y) x :=
    hDn.differentiable (by simp) x
  have hdEe : DifferentiableAt ℝ (fun y : Space ↦ pressureGradient w.pressure t y) x :=
    hEe.differentiable (by simp) x
  have hdnuB : DifferentiableAt ℝ (fun y : Space ↦ ν • spatialLaplacian w.velocity t y) x :=
    hdB.const_smul ν
  have hdCD : DifferentiableAt ℝ
      (fun y : Space ↦ f (t, y) - convectionDivergenceT w.velocity t y) x := hdC.sub hdDn
  have hcong := congrArg (fun g : Space → Space ↦ divSpatial g x) heq
  rw [divSpatial_sub hdA hdnuB, divSpatial_smul ν hdB,
    divSpatial_sub hdCD hdEe, divSpatial_sub hdC hdDn,
    divSpatial_pressureGradient hps,
    divSpatial_temporalDerivative_eq_zero hopen
      (fun s hs y ↦ w.divergence s (Ioo_subset_Ico_self hs) y) ht x,
    divSpatial_spatialLaplacian_eq_zero hus (fun y ↦ w.divergence t htIco y) x] at hcong
  show scalarSpatialLaplacianT w.pressure t x =
    divSpatial (fun y : Space ↦ f (t, y)) x -
      divSpatial (fun y : Space ↦ convectionDivergenceT w.velocity t y) x
  linarith [hcong]

/-! ## Joint continuity in time of the Poisson terms -/

omit [NormedSpace ℝ E] in
theorem continuousOn_slice_of_slab {T : ℝ} {G : SpaceTime → E}
    (hG : ContinuousOn G (slabT T)) (x : Space) :
    ContinuousOn (fun t : ℝ ↦ G (t, x)) (Ico (0 : ℝ) T) :=
  hG.comp (continuous_id.prodMk continuous_const).continuousOn (fun _t ht ↦ mem_slabT ht x)

theorem continuousOn_scalarSpatialLaplacianT {T : ℝ} {p : SpaceTimeScalar}
    (hp : ContDiffOn ℝ ∞ p (slabT T)) (x : Space) :
    ContinuousOn (fun t : ℝ ↦ scalarSpatialLaplacianT p t x) (Ico (0 : ℝ) T) := by
  have hsum : ContinuousOn (fun z : SpaceTime ↦ ∑ i : Fin 3, stPartial i (stPartial i p) z)
      (slabT T) :=
    continuousOn_finsetSum _ fun i _ ↦
      (contDiffOn_stPartial (contDiffOn_stPartial hp i) i).continuousOn
  exact continuousOn_slice_of_slab hsum x

theorem continuousOn_spatialDivergence {T : ℝ} {F : SpaceTimeField}
    (hF : ContDiffOn ℝ ∞ F (slabT T)) (x : Space) :
    ContinuousOn (fun t : ℝ ↦ spatialDivergence F t x) (Ico (0 : ℝ) T) := by
  have hsum : ContinuousOn (fun z : SpaceTime ↦ ∑ i : Fin 3, (stPartial i F z) i) (slabT T) := by
    refine continuousOn_finsetSum _ fun i _ ↦ ?_
    exact (PiLp.continuous_apply 2 (fun _ : Fin 3 ↦ ℝ) i).comp_continuousOn
      (contDiffOn_stPartial hF i).continuousOn
  exact continuousOn_slice_of_slab hsum x

theorem contDiffOn_convectionDivergence {T : ℝ} {u : SpaceTimeField}
    (hu : ContDiffOn ℝ ∞ u (slabT T)) :
    ContDiffOn ℝ ∞ (fun z : SpaceTime ↦ convectionDivergenceT u z.1 z.2) (slabT T) := by
  have he : (fun z : SpaceTime ↦ convectionDivergenceT u z.1 z.2) =
      fun z : SpaceTime ↦ ∑ j : Fin 3,
        stPartial j (fun z' : SpaceTime ↦ (u z' j) • u z') z := rfl
  rw [he]
  refine ContDiffOn.sum fun j _ ↦ contDiffOn_stPartial ?_ j
  exact ContDiffOn.smul
    ((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp_contDiffOn hu) hu


/-! ## The Poisson equation up to the initial time -/

theorem pressure_poisson_of_classical {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (hf : ContDiff ℝ ∞ f) (w : ClassicalSolutionT ν a f T) :
    ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space,
      scalarSpatialLaplacianT w.pressure t x =
        spatialDivergence f t x -
          spatialDivergence (fun z : SpaceTime ↦
            convectionDivergenceT w.velocity z.1 z.2) t x := by
  intro t ht x
  rcases eq_or_lt_of_le ht.1 with h0 | h0
  · subst h0
    set CD : SpaceTimeField := fun z : SpaceTime ↦ convectionDivergenceT w.velocity z.1 z.2
      with hCDdef
    set G : ℝ → ℝ := fun s ↦ scalarSpatialLaplacianT w.pressure s x -
      (spatialDivergence f s x - spatialDivergence CD s x) with hGdef
    have hcontG : ContinuousWithinAt G (Ico (0 : ℝ) T) 0 := by
      refine ContinuousWithinAt.sub ?_ (ContinuousWithinAt.sub ?_ ?_)
      · exact continuousOn_scalarSpatialLaplacianT w.pressure_smooth x 0 ht
      · exact continuousOn_spatialDivergence (hf.contDiffOn (s := slabT T)) x 0 ht
      · exact continuousOn_spatialDivergence
          (contDiffOn_convectionDivergence w.velocity_smooth) x 0 ht
    have hIoo : Ioo (0 : ℝ) T ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT w.horizon_pos
    have hle : 𝓝[>] (0 : ℝ) ≤ 𝓝[Ico (0 : ℝ) T] (0 : ℝ) :=
      nhdsWithin_le_iff.mpr (mem_of_superset hIoo Ioo_subset_Ico_self)
    have h1 : Tendsto G (𝓝[>] (0 : ℝ)) (𝓝 (G 0)) := hcontG.mono_left hle
    have h2 : Tendsto G (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [hIoo] with s hs
      have hps := pressure_poisson_interior hf w hs x
      show (0 : ℝ) = G s
      rw [hGdef]
      simp only
      rw [hps]
      ring
    have hzero : G 0 = 0 := tendsto_nhds_unique h1 h2
    rw [hGdef] at hzero
    simp only at hzero
    linarith [hzero]
  · exact pressure_poisson_interior hf w ⟨h0, ht.2⟩ x

/-! ## The main theorem and its unconditional corollaries -/

theorem slabSmooth_of_classical {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionT ν a f T) : SlabSmooth T w.velocity :=
  ⟨w.velocity_smooth, w.velocity_periodic⟩

/-- **Smooth datum paths at every integer order**, for any classical periodic solution. -/
theorem sobolev_smooth_of_classical {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionT ν a f T) (m : ℕ) :
    ∃ G : ℝ → PeriodicSobolev (m : ℝ),
      IsPeriodicSobolevPathOn (m : ℝ) (Ico (0 : ℝ) T) w.velocity G ∧
        ContDiffOn ℝ ∞ G (Ico (0 : ℝ) T) :=
  ⟨datumPathT m w.velocity,
    fun _t ht ↦ datumPathT_spec ((slabSmooth_of_classical w).datum_exists m ht),
    contDiffOn_datumPathT w.horizon_pos m (slabSmooth_of_classical w)⟩

/-- **Every classical periodic solution has the manuscript local regularity.** -/
theorem periodicLocalRegularity_of_classical' {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (hf : ContDiff ℝ ∞ f) (w : ClassicalSolutionT ν a f T) :
    PeriodicLocalRegularity ν a f T w where
  sobolev_smooth := sobolev_smooth_of_classical w
  pressure_poisson := pressure_poisson_of_classical hf w
  projected := classicalSolutionT_projected w

/-- U6b in the binder shape of the four public APIs. -/
theorem periodicLocalRegularity_of_classical : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T), PeriodicLocalRegularity ν a f T w :=
  fun _ν _hν _a _ha _f hf _T w ↦ periodicLocalRegularity_of_classical' hf.1 w

/-- `PeriodicViscosityRescalingAPI.to_unit`, unconditionally. -/
theorem to_unit : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T),
          ∃ v : ClassicalSolutionT 1 (unitViscosityInitialT ν a)
              (unitViscosityForceT ν f) (ν * T),
            v.velocity = unitViscosityVelocityT ν w.velocity ∧
            v.pressure = unitViscosityPressureT ν w.pressure ∧
            PeriodicLocalRegularity 1 (unitViscosityInitialT ν a)
              (unitViscosityForceT ν f) (ν * T) v :=
  fun ν hν a ha f hf T w ↦ Transport.to_unit_of_regularity ν hν a ha f hf T w
    (periodicLocalRegularity_of_classical ν hν a ha f hf T w)

/-- `PeriodicViscosityRescalingAPI.from_unit`, unconditionally. -/
theorem from_unit : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ),
          ∀ v : ClassicalSolutionT 1 (unitViscosityInitialT ν a)
              (unitViscosityForceT ν f) (ν * T),
            ∃ w : ClassicalSolutionT ν a f T,
              w.velocity = restoreViscosityVelocityT ν v.velocity ∧
              w.pressure = restoreViscosityPressureT ν v.pressure ∧
              PeriodicLocalRegularity ν a f T w := by
  intro ν hν a ha f hf T v
  have hg : unitViscosityForceT ν f ∈ forceClassT := (scaled_classes ν hν a ha f hf).2
  exact Transport.from_unit_of_regularity ν hν a ha f hf T v
    (periodicLocalRegularity_of_classical' hg.1 v)

/-- `PeriodicMeanReductionAPI.transformed_solution`, unconditionally. -/
theorem transformed_solution : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T),
          ∃ v : ClassicalSolutionT ν (meanZeroPartT a) (galileanForceT a f) T,
            v.velocity = galileanVelocityT a f w.velocity ∧
            v.pressure = galileanPressureT a f w.pressure ∧
            PeriodicLocalRegularity ν (meanZeroPartT a) (galileanForceT a f) T v := by
  intro ν hν a ha f hf T w
  obtain ⟨v, hv1, hv2, -⟩ := Transport.transformed_solution_fields ν hν a ha f hf T w
  have hg : galileanForceT a f ∈ forceClassT := (transformed_classes ν hν a ha f hf T w).2
  exact ⟨v, hv1, hv2, periodicLocalRegularity_of_classical' hg.1 v⟩

/-- `PeriodicLocalTheoryAPI.regularity`: whatever local solution family the API
selects, its regularity is automatic. -/
theorem regularity_of_solution
    (horizon : ℝ → SpatialField → SpaceTimeField → ℝ)
    (solution : ∀ (ν : ℝ), 0 < ν →
      ∀ (a : SpatialField), a ∈ initialClassT →
        ∀ (f : SpaceTimeField), f ∈ forceClassT →
          ClassicalSolutionT ν a f (horizon ν a f)) :
    ∀ (ν : ℝ) (hν : 0 < ν) (a : SpatialField) (ha : a ∈ initialClassT)
      (f : SpaceTimeField) (hf : f ∈ forceClassT),
        PeriodicLocalRegularity ν a f (horizon ν a f) (solution ν hν a ha f hf) :=
  fun ν hν a ha f hf ↦
    periodicLocalRegularity_of_classical ν hν a ha f hf _ (solution ν hν a ha f hf)

end NSFormalization.Section3.T11
