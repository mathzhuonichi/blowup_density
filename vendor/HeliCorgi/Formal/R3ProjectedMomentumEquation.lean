import Formal.R3ProjectedMomentumDuhamelInfrastructure
import Formal.R3EndpointSafeProjectedLocalExistence

/-!
# The projected momentum equation along a mild solution
(Clay semantic-promotion edge 2b-ii.a-assembly)

This file closes the assembly left open by the infrastructure pass
(`Formal/R3ProjectedMomentumDuhamelInfrastructure.lean`): along an endpoint-safe projected
mild solution (`IsR3EndpointSafeProjectedMildSolutionOn`), the decoded physical velocity
`U t = r3H3ToL2Operator (u t)` satisfies

* the **fundamental integral identity** (`r3MildDecodedVelocity_eq_integral`):
  `U t = U 0 + ∫₀ᵗ (ν • Δ(u σ) − P((U·∇)U)(σ)) dσ` for every `t ∈ [0, T]`, and
* the **projected momentum equation** (`r3EndpointSafeProjectedMild_momentum`): at every
  interior time the strong `L²`-valued derivative exists and equals

  `∂ₜU = νΔU − P((U·∇)U)`,

  with `Δ` the decoded Laplacian (the genuine distributional Laplacian by the
  infrastructure pass's `r3L2ToTempered_r3H3LaplacianL2Operator`) and the nonlinear term
  the Leray projection of the edge-2b-i identified literal convection of the decoded
  representatives (`r3DecodedConvectionL2`).

The proof is the five-stage decomposition of the commissioned plan, each stage a small
standalone theorem, and it **consumes** the infrastructure:

1. continuity/integrability of the projected momentum source (Stage 1);
2. the scalar pairing integral identity against an arbitrary `L²` test vector
   (`inner_r3MildDecodedVelocity_eq_integral`, Stage 2), built from the decoded mild
   identity `r3MildDecodedVelocity_duhamel`, the flowed FTC
   `integral_inner_r3StokesL2Path` (once for the linear part, once per convection slice),
   the ν-free Laplacian recombination of the coordinate mild identity, and the
   Duhamel-triangle Fubini swap `integral_triangle_swap`;
3. the `L²`-valued integral identity by pairing separation (`ext_inner_left`, Stage 3);
4. the interior strong derivative by the Banach-valued FTC-2 (Stage 4);
5. the capstone with the edge-2b-i identified nonlinearity (Stage 5).

NOT claimed in this pass (per commission): the pressure term and the unprojected equation
(edge 2b-ii.b), any classical pointwise time derivative beyond the `L²`-valued one, and
edges 3/4/5.  No phantom Sobolev inclusion is used; no rapid decay is claimed.
-/

namespace MNS2

open MeasureTheory FourierTransform Real LineDeriv intervalIntegral
open scoped FourierTransform SchwartzMap ContDiff NNReal

noncomputable section

variable {ν T : ℝ} {u₀ : R3HsVelocity 3} {u : ℝ → R3HsVelocity 3}

/-- The momentum integrand `νΔU − P((U·∇)U)` along the trajectory. -/
def r3MildMomentumIntegrand (ν : ℝ) (u : ℝ → R3HsVelocity 3) (σ : ℝ) : R3L2Velocity :=
  ν • r3H3LaplacianL2Operator (u σ) - r3MildConvectionSource u σ

/-! ## Stage 1: continuity and integrability of the projected momentum source -/

set_option maxHeartbeats 1000000 in
/-- The projected convection coordinate is continuous along a mild trajectory. -/
theorem continuousOn_r3MildCoordConvection (hnu : 0 < ν)
    (hu : IsR3EndpointSafeProjectedMildSolutionOn hnu T u₀ u) :
    ContinuousOn (fun σ : ℝ => r3ProjectedConvectionH3ToH2 (u σ) (u σ))
      (Set.Icc (0 : ℝ) T) := by
  have hcont : ContinuousOn u (Set.Icc (0 : ℝ) T) := hu.2.1
  have happly : Continuous
      fun p : (R3HsVelocity 3 →L[ℂ] R3HsVelocity 2) × R3HsVelocity 3 => p.1 p.2 :=
    isBoundedBilinearMap_apply.continuous
  have hop : ContinuousOn (fun σ : ℝ => r3ProjectedConvectionH3ToH2 (u σ))
      (Set.Icc (0 : ℝ) T) :=
    r3ProjectedConvectionH3ToH2.continuous.comp_continuousOn hcont
  exact happly.comp_continuousOn (hop.prodMk hcont)

set_option maxHeartbeats 1000000 in
/-- The decoded projected convection source is continuous along a mild trajectory. -/
theorem continuousOn_r3MildConvectionSource (hnu : 0 < ν)
    (hu : IsR3EndpointSafeProjectedMildSolutionOn hnu T u₀ u) :
    ContinuousOn (r3MildConvectionSource u) (Set.Icc (0 : ℝ) T) :=
  r3H2ToL2Operator.continuous.comp_continuousOn
    (continuousOn_r3MildCoordConvection hnu hu)

set_option maxHeartbeats 1000000 in
/-- The decoded order-two Laplacian of the convection coordinate is continuous along a
mild trajectory. -/
theorem continuousOn_r3MildConvectionLaplacian (hnu : 0 < ν)
    (hu : IsR3EndpointSafeProjectedMildSolutionOn hnu T u₀ u) :
    ContinuousOn
      (fun s : ℝ => ν • r3H2LaplacianL2Operator (r3ProjectedConvectionH3ToH2 (u s) (u s)))
      (Set.Icc (0 : ℝ) T) :=
  (r3H2LaplacianL2Operator.continuous.comp_continuousOn
    (continuousOn_r3MildCoordConvection hnu hu)).const_smul ν

set_option maxHeartbeats 1000000 in
/-- The scaled decoded Laplacian is continuous along a mild trajectory. -/
theorem continuousOn_r3MildLaplacian (hnu : 0 < ν)
    (hu : IsR3EndpointSafeProjectedMildSolutionOn hnu T u₀ u) :
    ContinuousOn (fun σ : ℝ => ν • r3H3LaplacianL2Operator (u σ))
      (Set.Icc (0 : ℝ) T) :=
  (r3H3LaplacianL2Operator.continuous.comp_continuousOn hu.2.1).const_smul ν

set_option maxHeartbeats 1000000 in
/-- **Stage 1**: the projected momentum source is continuous along a mild trajectory. -/
theorem continuousOn_r3MildMomentumIntegrand (hnu : 0 < ν)
    (hu : IsR3EndpointSafeProjectedMildSolutionOn hnu T u₀ u) :
    ContinuousOn (r3MildMomentumIntegrand ν u) (Set.Icc (0 : ℝ) T) :=
  (continuousOn_r3MildLaplacian hnu hu).sub (continuousOn_r3MildConvectionSource hnu hu)

set_option maxHeartbeats 4000000 in
/-- The heat-flowed convection source is continuous in the slice variable. -/
theorem continuousOn_r3StokesL2Path_convection (hnu : 0 < ν)
    (hu : IsR3EndpointSafeProjectedMildSolutionOn hnu T u₀ u) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ContinuousOn
      (fun s : ℝ => r3StokesL2Path hnu.le (r3MildConvectionSource u s) (t - s))
      (Set.Icc (0 : ℝ) t) := by
  have hIcc : Set.Icc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T := Set.Icc_subset_Icc le_rfl ht.2
  have hNcont : ContinuousOn (r3MildConvectionSource u) (Set.Icc (0 : ℝ) t) :=
    (continuousOn_r3MildConvectionSource hnu hu).mono hIcc
  have h : ContinuousOn ((fun p : ℝ × R3L2Velocity => r3StokesL2Path hnu.le p.2 p.1) ∘
      fun s : ℝ => (t - s, r3MildConvectionSource u s)) (Set.Icc (0 : ℝ) t) :=
    (continuous_r3StokesL2Path_action hnu.le).comp_continuousOn
      ((continuous_const.sub continuous_id).continuousOn.prodMk hNcont)
  exact h

set_option maxHeartbeats 1000000 in
/-- The momentum source is interval integrable on every certified horizon. -/
theorem intervalIntegrable_r3MildMomentumIntegrand (hnu : 0 < ν)
    (hu : IsR3EndpointSafeProjectedMildSolutionOn hnu T u₀ u) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) :
    IntervalIntegrable (r3MildMomentumIntegrand ν u) volume 0 t :=
  ((continuousOn_r3MildMomentumIntegrand hnu hu).mono
    (Set.Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1

/-! ## Stage 2: the scalar pairing integral identity -/

/-- The heat path commutes with real scaling of the datum. -/
theorem r3StokesL2Path_real_smul {ν' : ℝ} (hν : 0 ≤ ν') (r : ℝ) (X : R3L2Velocity)
    (τ : ℝ) :
    r3StokesL2Path hν (r • X) τ = r • r3StokesL2Path hν X τ := by
  unfold r3StokesL2Path
  rw [r3L2_real_smul, map_smul, ← r3L2_real_smul]

/-- Real scalars move out of the second pairing slot. -/
theorem r3L2_inner_real_smul_right (r : ℝ) (x y : R3L2Velocity) :
    inner ℂ x (r • y) = r • inner ℂ x y := by
  rw [r3L2_real_smul, inner_smul_right, Complex.real_smul]

set_option maxHeartbeats 1000000 in
/-- The decoded mild identity, paired against a test vector. -/
theorem inner_r3MildDecodedVelocity_duhamel (hnu : 0 < ν)
    (hu : IsR3EndpointSafeProjectedMildSolutionOn hnu T u₀ u) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) (ψ : R3L2Velocity) :
    inner ℂ ψ (r3MildDecodedVelocity u t) =
      inner ℂ ψ (r3StokesL2Path hnu.le (r3MildDecodedVelocity u 0) t) -
        ∫ s in (0 : ℝ)..t,
          inner ℂ ψ (r3StokesL2Path hnu.le (r3MildConvectionSource u s) (t - s)) := by
  have hpathint : IntervalIntegrable
      (fun s : ℝ => r3StokesL2Path hnu.le (r3MildConvectionSource u s) (t - s))
      volume 0 t :=
    (continuousOn_r3StokesL2Path_convection hnu hu ht).intervalIntegrable_of_Icc ht.1
  rw [r3MildDecodedVelocity_duhamel hnu hu ht, inner_sub_right]
  congr 1
  exact (ContinuousLinearMap.intervalIntegral_comp_comm (innerSL ℂ ψ) hpathint).symm

set_option maxHeartbeats 2000000 in
/-- **The ν-free Laplacian recombination**: applying the decoded Laplacian to the
coordinate mild identity expresses the Laplacian of the solution through flowed data. -/
theorem inner_r3MildLaplacian_recombination (hnu : 0 < ν)
    (hu : IsR3EndpointSafeProjectedMildSolutionOn hnu T u₀ u) (ψ : R3L2Velocity) {σ : ℝ}
    (hσ : σ ∈ Set.Icc (0 : ℝ) T) :
    inner ℂ ψ (r3H3LaplacianL2Operator (u σ)) =
      inner ℂ ψ (r3StokesL2Path hnu.le (r3H3LaplacianL2Operator u₀) σ) -
        ∫ s in (0 : ℝ)..σ,
          inner ℂ ψ (r3StokesL2Path hnu.le
            (r3H2LaplacianL2Operator (r3ProjectedConvectionH3ToH2 (u s) (u s)))
            (σ - s)) := by
  obtain ⟨hintσ, heqσ⟩ := r3EndpointSafeProjectedMild_equation_at_time hnu hu hσ
  have hdec := congrArg (fun g : R3HsVelocity 3 => r3H3LaplacianL2Operator g) heqσ
  rw [map_sub, ← ContinuousLinearMap.intervalIntegral_comp_comm
    r3H3LaplacianL2Operator hintσ] at hdec
  rw [hdec, inner_sub_right]
  congr 1
  · rw [show r3H3LaplacianL2Operator (r3StokesH3Evolution hnu.le ⟨σ, hσ.1⟩ u₀) =
        r3H3LaplacianL2Operator (r3StokesL2Operator hnu.le hσ.1 u₀) from rfl,
      r3H3LaplacianL2Operator_stokes hnu.le hσ.1,
      r3StokesL2Path_of_nonneg hnu.le _ hσ.1]
  · have hslice : IntervalIntegrable
        (fun s : ℝ => r3H3LaplacianL2Operator
          (r3EndpointSafeProjectedDuhamelIntegrand hnu σ u s)) volume 0 σ :=
      ⟨r3H3LaplacianL2Operator.integrable_comp hintσ.1,
        r3H3LaplacianL2Operator.integrable_comp hintσ.2⟩
    rw [show inner ℂ ψ (∫ s in (0 : ℝ)..σ, r3H3LaplacianL2Operator
          (r3EndpointSafeProjectedDuhamelIntegrand hnu σ u s)) =
        ∫ s in (0 : ℝ)..σ, inner ℂ ψ (r3H3LaplacianL2Operator
          (r3EndpointSafeProjectedDuhamelIntegrand hnu σ u s)) from
      (ContinuousLinearMap.intervalIntegral_comp_comm (innerSL ℂ ψ) hslice).symm]
    refine intervalIntegral.integral_congr_ae ?_
    have hne : ∀ᵐ s : ℝ ∂(volume : Measure ℝ), s ≠ σ := by
      rw [MeasureTheory.ae_iff]
      simp
    filter_upwards [hne] with s hs hmem
    have hsσ : s < σ := by
      rw [Set.uIoc_of_le hσ.1] at hmem
      exact lt_of_le_of_ne hmem.2 hs
    rw [r3EndpointSafeProjectedDuhamelIntegrand_of_lt hnu σ u hsσ,
      r3H3LaplacianL2Operator_smoothing hnu (sub_pos.mpr hsσ),
      r3StokesL2Path_of_nonneg hnu.le _ (sub_pos.mpr hsσ).le]

set_option maxHeartbeats 4000000 in
/-- The ν-scaled Laplacian recombination, in the form consumed by the aggregation. -/
theorem inner_r3MildLaplacian_recombination_smul (hnu : 0 < ν)
    (hu : IsR3EndpointSafeProjectedMildSolutionOn hnu T u₀ u) (ψ : R3L2Velocity) {σ : ℝ}
    (hσ : σ ∈ Set.Icc (0 : ℝ) T) :
    inner ℂ ψ (ν • r3H3LaplacianL2Operator (u σ)) =
      inner ℂ ψ (r3StokesL2Path hnu.le (ν • r3H3LaplacianL2Operator u₀) σ) -
        ∫ s in (0 : ℝ)..σ,
          inner ℂ ψ (r3StokesL2Path hnu.le
            (ν • r3H2LaplacianL2Operator (r3ProjectedConvectionH3ToH2 (u s) (u s)))
            (σ - s)) := by
  rw [r3L2_inner_real_smul_right, inner_r3MildLaplacian_recombination hnu hu ψ hσ, smul_sub,
    r3StokesL2Path_real_smul, r3L2_inner_real_smul_right, ← intervalIntegral.integral_smul]
  congr 1
  refine intervalIntegral.integral_congr fun s _ => ?_
  rw [r3StokesL2Path_real_smul, r3L2_inner_real_smul_right]

set_option maxHeartbeats 4000000 in
/-- **Per-slice flowed FTC**: each heat-flowed convection slice decomposes into its value
plus the integrated flow of its ν-scaled order-two Laplacian (consuming
`integral_inner_r3StokesL2Path`). -/
theorem inner_r3MildConvectionSlice_FTC (hnu : 0 < ν) (u : ℝ → R3HsVelocity 3)
    (ψ : R3L2Velocity) {s t : ℝ} (hst : s ≤ t) :
    inner ℂ ψ (r3StokesL2Path hnu.le (r3MildConvectionSource u s) (t - s)) =
      inner ℂ ψ (r3MildConvectionSource u s) +
        ∫ σ in s..t,
          inner ℂ ψ (r3StokesL2Path hnu.le
            (ν • r3H2LaplacianL2Operator (r3ProjectedConvectionH3ToH2 (u s) (u s)))
            (σ - s)) := by
  have hFTC := integral_inner_r3StokesL2Path hnu.le
    (fourier_r3H2Laplacian_ae ν (r3ProjectedConvectionH3ToH2 (u s) (u s))) ψ hst
  unfold r3MildConvectionSource
  rw [hFTC]
  ring

set_option maxHeartbeats 4000000 in
/-- **The linear FTC**: the flowed initial pairing decomposes into the initial pairing
plus the integrated flow of the ν-scaled decoded Laplacian of the datum. -/
theorem inner_r3MildLinear_FTC (hnu : 0 < ν)
    (hu : IsR3EndpointSafeProjectedMildSolutionOn hnu T u₀ u) (ψ : R3L2Velocity)
    {t : ℝ} (ht0 : 0 ≤ t) :
    inner ℂ ψ (r3StokesL2Path hnu.le (r3MildDecodedVelocity u 0) t) =
      inner ℂ ψ (r3MildDecodedVelocity u 0) +
        ∫ σ in (0 : ℝ)..t,
          inner ℂ ψ (r3StokesL2Path hnu.le (ν • r3H3LaplacianL2Operator u₀) σ) := by
  have hu0 : u 0 = u₀ := hu.2.2.1
  have hFTC := integral_inner_r3StokesL2Path hnu.le
    (fourier_r3H3Laplacian_ae ν u₀) ψ ht0
  have hdec : r3MildDecodedVelocity u 0 = r3H3ToL2Operator u₀ := by
    rw [show r3MildDecodedVelocity u 0 = r3H3ToL2Operator (u 0) from rfl, hu0]
  rw [hdec]
  have hcongr : (∫ σ in (0 : ℝ)..t,
      inner ℂ ψ (r3StokesL2Path hnu.le (ν • r3H3LaplacianL2Operator u₀) σ)) =
      ∫ σ in (0 : ℝ)..t,
        inner ℂ ψ (r3StokesL2Path hnu.le (ν • r3H3LaplacianL2Operator u₀) (σ - 0)) := by
    refine intervalIntegral.integral_congr fun σ _ => ?_
    rw [sub_zero]
  rw [hcongr, hFTC, sub_zero]
  ring

set_option maxHeartbeats 4000000 in
/-- **The triangle swap for the mild convection flow** (consuming
`integral_triangle_swap`). -/
theorem r3MildConvectionTriangle_swap (hnu : 0 < ν)
    (hu : IsR3EndpointSafeProjectedMildSolutionOn hnu T u₀ u) (ψ : R3L2Velocity)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    (∫ s in (0 : ℝ)..t, ∫ σ in s..t,
        inner ℂ ψ (r3StokesL2Path hnu.le
          (ν • r3H2LaplacianL2Operator (r3ProjectedConvectionH3ToH2 (u s) (u s)))
          (σ - s))) =
      ∫ σ in (0 : ℝ)..t, ∫ s in (0 : ℝ)..σ,
        inner ℂ ψ (r3StokesL2Path hnu.le
          (ν • r3H2LaplacianL2Operator (r3ProjectedConvectionH3ToH2 (u s) (u s)))
          (σ - s)) := by
  have hIcc : Set.Icc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T := Set.Icc_subset_Icc le_rfl ht.2
  have hsrc : ContinuousOn
      (fun s : ℝ => ν • r3H2LaplacianL2Operator (r3ProjectedConvectionH3ToH2 (u s) (u s)))
      (Set.Icc (0 : ℝ) t) :=
    (continuousOn_r3MildConvectionLaplacian hnu hu).mono hIcc
  have hΦcont : ContinuousOn (fun p : ℝ × ℝ =>
      inner ℂ ψ (r3StokesL2Path hnu.le
        (ν • r3H2LaplacianL2Operator (r3ProjectedConvectionH3ToH2 (u p.2) (u p.2)))
        (p.1 - p.2)))
      (Set.Icc (0 : ℝ) t ×ˢ Set.Icc (0 : ℝ) t) := by
    have hmap : ContinuousOn (fun p : ℝ × ℝ =>
        ((p.1 - p.2),
          ν • r3H2LaplacianL2Operator (r3ProjectedConvectionH3ToH2 (u p.2) (u p.2))))
        (Set.Icc (0 : ℝ) t ×ˢ Set.Icc (0 : ℝ) t) :=
      ((continuous_fst.sub continuous_snd).continuousOn).prodMk
        (hsrc.comp continuousOn_snd fun p hp => hp.2)
    have h1 : ContinuousOn ((fun q : ℝ × R3L2Velocity => r3StokesL2Path hnu.le q.2 q.1) ∘
        fun p : ℝ × ℝ =>
          ((p.1 - p.2),
            ν • r3H2LaplacianL2Operator (r3ProjectedConvectionH3ToH2 (u p.2) (u p.2))))
        (Set.Icc (0 : ℝ) t ×ˢ Set.Icc (0 : ℝ) t) :=
      (continuous_r3StokesL2Path_action hnu.le).comp_continuousOn hmap
    have h2 : ContinuousOn ((fun w : R3L2Velocity => inner ℂ ψ w) ∘
        ((fun q : ℝ × R3L2Velocity => r3StokesL2Path hnu.le q.2 q.1) ∘
          fun p : ℝ × ℝ =>
            ((p.1 - p.2),
              ν • r3H2LaplacianL2Operator
                (r3ProjectedConvectionH3ToH2 (u p.2) (u p.2)))))
        (Set.Icc (0 : ℝ) t ×ˢ Set.Icc (0 : ℝ) t) :=
      (innerSL ℂ ψ).continuous.comp_continuousOn h1
    exact h2
  obtain ⟨C, hCb⟩ := ((isCompact_Icc (a := (0 : ℝ)) (b := t)).prod
    (isCompact_Icc (a := (0 : ℝ)) (b := t))).exists_bound_of_continuousOn hΦcont
  exact integral_triangle_swap ht.1
    (fun σ s => inner ℂ ψ (r3StokesL2Path hnu.le
      (ν • r3H2LaplacianL2Operator (r3ProjectedConvectionH3ToH2 (u s) (u s))) (σ - s)))
    hΦcont (fun σ hσ s hs => hCb (σ, s) ⟨hσ, hs⟩)

set_option maxHeartbeats 4000000 in
/-- **Stage 2: the scalar pairing integral identity** against an arbitrary `L²` test
vector. -/
theorem inner_r3MildDecodedVelocity_eq_integral (hnu : 0 < ν)
    (hu : IsR3EndpointSafeProjectedMildSolutionOn hnu T u₀ u) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) (ψ : R3L2Velocity) :
    inner ℂ ψ (r3MildDecodedVelocity u t) =
      inner ℂ ψ (r3MildDecodedVelocity u 0) +
        ∫ σ in (0 : ℝ)..t, inner ℂ ψ (r3MildMomentumIntegrand ν u σ) := by
  have ht0 : (0 : ℝ) ≤ t := ht.1
  have hIcc : Set.Icc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T := Set.Icc_subset_Icc le_rfl ht.2
  -- Interval integrabilities of the scalar slices.
  have hNint : IntervalIntegrable
      (fun s : ℝ => inner ℂ ψ (r3MildConvectionSource u s)) volume 0 t :=
    ((innerSL ℂ ψ).continuous.comp_continuousOn
      ((continuousOn_r3MildConvectionSource hnu hu).mono hIcc)).intervalIntegrable_of_Icc
      ht0
  have hLint : IntervalIntegrable
      (fun σ : ℝ => inner ℂ ψ (ν • r3H3LaplacianL2Operator (u σ))) volume 0 t :=
    ((innerSL ℂ ψ).continuous.comp_continuousOn
      ((continuousOn_r3MildLaplacian hnu hu).mono hIcc)).intervalIntegrable_of_Icc ht0
  have hAint : IntervalIntegrable
      (fun σ : ℝ =>
        inner ℂ ψ (r3StokesL2Path hnu.le (ν • r3H3LaplacianL2Operator u₀) σ))
      volume 0 t :=
    ((innerSL ℂ ψ).continuous.comp
      (continuous_r3StokesL2Path hnu.le _)).intervalIntegrable 0 t
  have hSint : IntervalIntegrable
      (fun s : ℝ =>
        inner ℂ ψ (r3StokesL2Path hnu.le (r3MildConvectionSource u s) (t - s)))
      volume 0 t :=
    ((innerSL ℂ ψ).continuous.comp_continuousOn
      (continuousOn_r3StokesL2Path_convection hnu hu ht)).intervalIntegrable_of_Icc ht0
  have hTriOuter : IntervalIntegrable (fun s : ℝ => ∫ σ in s..t,
      inner ℂ ψ (r3StokesL2Path hnu.le
        (ν • r3H2LaplacianL2Operator (r3ProjectedConvectionH3ToH2 (u s) (u s)))
        (σ - s))) volume 0 t := by
    refine (hSint.sub hNint).congr fun s hmem => ?_
    rw [Set.uIoc_of_le ht0] at hmem
    rw [inner_r3MildConvectionSlice_FTC hnu u ψ hmem.2]
    ring
  have hTriInner : IntervalIntegrable (fun σ : ℝ => ∫ s in (0 : ℝ)..σ,
      inner ℂ ψ (r3StokesL2Path hnu.le
        (ν • r3H2LaplacianL2Operator (r3ProjectedConvectionH3ToH2 (u s) (u s)))
        (σ - s))) volume 0 t := by
    refine (hAint.sub hLint).congr fun σ hmem => ?_
    rw [Set.uIoc_of_le ht0] at hmem
    rw [inner_r3MildLaplacian_recombination_smul hnu hu ψ
      (⟨hmem.1.le, hmem.2.trans ht.2⟩ : σ ∈ Set.Icc (0 : ℝ) T)]
    ring
  -- Decompose the mild identity slice by slice.
  have hdecomp : (∫ s in (0 : ℝ)..t,
      inner ℂ ψ (r3StokesL2Path hnu.le (r3MildConvectionSource u s) (t - s))) =
      (∫ s in (0 : ℝ)..t, inner ℂ ψ (r3MildConvectionSource u s)) +
        ∫ s in (0 : ℝ)..t, ∫ σ in s..t,
          inner ℂ ψ (r3StokesL2Path hnu.le
            (ν • r3H2LaplacianL2Operator (r3ProjectedConvectionH3ToH2 (u s) (u s)))
            (σ - s)) := by
    rw [← intervalIntegral.integral_add hNint hTriOuter]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le ht0] at hs
    exact inner_r3MildConvectionSlice_FTC hnu u ψ hs.2
  -- Recombine the momentum integrand.
  have hrecomb : (∫ σ in (0 : ℝ)..t, inner ℂ ψ (r3MildMomentumIntegrand ν u σ)) =
      (∫ σ in (0 : ℝ)..t,
          inner ℂ ψ (r3StokesL2Path hnu.le (ν • r3H3LaplacianL2Operator u₀) σ)) -
        (∫ σ in (0 : ℝ)..t, ∫ s in (0 : ℝ)..σ,
          inner ℂ ψ (r3StokesL2Path hnu.le
            (ν • r3H2LaplacianL2Operator (r3ProjectedConvectionH3ToH2 (u s) (u s)))
            (σ - s))) -
        ∫ σ in (0 : ℝ)..t, inner ℂ ψ (r3MildConvectionSource u σ) := by
    have hcongr : (∫ σ in (0 : ℝ)..t, inner ℂ ψ (r3MildMomentumIntegrand ν u σ)) =
        ∫ σ in (0 : ℝ)..t,
          ((inner ℂ ψ (r3StokesL2Path hnu.le (ν • r3H3LaplacianL2Operator u₀) σ) -
            ∫ s in (0 : ℝ)..σ,
              inner ℂ ψ (r3StokesL2Path hnu.le
                (ν • r3H2LaplacianL2Operator
                  (r3ProjectedConvectionH3ToH2 (u s) (u s))) (σ - s))) -
            inner ℂ ψ (r3MildConvectionSource u σ)) := by
      refine intervalIntegral.integral_congr fun σ hσ => ?_
      rw [Set.uIcc_of_le ht0] at hσ
      rw [r3MildMomentumIntegrand, inner_sub_right,
        inner_r3MildLaplacian_recombination_smul hnu hu ψ
          (⟨hσ.1, hσ.2.trans ht.2⟩ : σ ∈ Set.Icc (0 : ℝ) T)]
    rw [hcongr, intervalIntegral.integral_sub (hAint.sub hTriInner) hNint,
      intervalIntegral.integral_sub hAint hTriInner]
  -- Assemble.
  rw [inner_r3MildDecodedVelocity_duhamel hnu hu ht ψ,
    inner_r3MildLinear_FTC hnu hu ψ ht0, hdecomp,
    r3MildConvectionTriangle_swap hnu hu ψ ht, hrecomb]
  ring

/-! ## Stage 3: the `L²`-valued integral identity by pairing separation -/

set_option maxHeartbeats 1000000 in
/-- **Stage 3: the fundamental integral identity.**  Along a mild solution the decoded
velocity is its initial value plus the time integral of the momentum integrand. -/
theorem r3MildDecodedVelocity_eq_integral (hnu : 0 < ν)
    (hu : IsR3EndpointSafeProjectedMildSolutionOn hnu T u₀ u) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) :
    r3MildDecodedVelocity u t =
      r3MildDecodedVelocity u 0 +
        ∫ σ in (0 : ℝ)..t, r3MildMomentumIntegrand ν u σ := by
  have hIcc : Set.Icc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T := Set.Icc_subset_Icc le_rfl ht.2
  have hMint : IntervalIntegrable (r3MildMomentumIntegrand ν u) volume 0 t :=
    ((continuousOn_r3MildMomentumIntegrand hnu hu).mono hIcc).intervalIntegrable_of_Icc
      ht.1
  refine ext_inner_left ℂ fun ψ => ?_
  rw [inner_add_right,
    show inner ℂ ψ (∫ σ in (0 : ℝ)..t, r3MildMomentumIntegrand ν u σ) =
      ∫ σ in (0 : ℝ)..t, inner ℂ ψ (r3MildMomentumIntegrand ν u σ) from
    (ContinuousLinearMap.intervalIntegral_comp_comm (innerSL ℂ ψ) hMint).symm]
  exact inner_r3MildDecodedVelocity_eq_integral hnu hu ht ψ

/-! ## Stage 4: the interior strong derivative by the Banach-valued FTC -/

set_option maxHeartbeats 1000000 in
/-- **Stage 4**: the decoded velocity has a strong `L²`-valued derivative at every
interior time, equal to the momentum integrand. -/
theorem hasDerivAt_r3MildDecodedVelocity (hnu : 0 < ν)
    (hu : IsR3EndpointSafeProjectedMildSolutionOn hnu T u₀ u) {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (r3MildDecodedVelocity u) (r3MildMomentumIntegrand ν u t) t := by
  have htIcc : t ∈ Set.Icc (0 : ℝ) T := ⟨ht.1.le, ht.2.le⟩
  have hMcont : ContinuousOn (r3MildMomentumIntegrand ν u) (Set.Icc (0 : ℝ) T) :=
    continuousOn_r3MildMomentumIntegrand hnu hu
  have hIoo : Set.Ioo (0 : ℝ) T ∈ nhds t := Ioo_mem_nhds ht.1 ht.2
  have hMcontIoo : ContinuousOn (r3MildMomentumIntegrand ν u) (Set.Ioo (0 : ℝ) T) :=
    hMcont.mono Set.Ioo_subset_Icc_self
  have hMintt : IntervalIntegrable (r3MildMomentumIntegrand ν u) volume 0 t :=
    ((hMcont.mono (Set.Icc_subset_Icc le_rfl htIcc.2)).intervalIntegrable_of_Icc ht.1.le)
  have hmeasAt : StronglyMeasurableAtFilter (r3MildMomentumIntegrand ν u) (nhds t)
      volume :=
    ⟨Set.Ioo (0 : ℝ) T, hIoo, hMcontIoo.aestronglyMeasurable measurableSet_Ioo⟩
  have hcontAt : ContinuousAt (r3MildMomentumIntegrand ν u) t :=
    hMcontIoo.continuousAt hIoo
  have hFTC : HasDerivAt
      (fun x : ℝ => ∫ σ in (0 : ℝ)..x, r3MildMomentumIntegrand ν u σ)
      (r3MildMomentumIntegrand ν u t) t :=
    intervalIntegral.integral_hasDerivAt_right hMintt hmeasAt hcontAt
  have hshift : HasDerivAt
      (fun x : ℝ => r3MildDecodedVelocity u 0 +
        ∫ σ in (0 : ℝ)..x, r3MildMomentumIntegrand ν u σ)
      (r3MildMomentumIntegrand ν u t) t := by
    simpa using hFTC.const_add (r3MildDecodedVelocity u 0)
  refine hshift.congr_of_eventuallyEq ?_
  filter_upwards [hIoo] with x hx
  exact r3MildDecodedVelocity_eq_integral hnu hu ⟨hx.1.le, hx.2.le⟩

/-! ## Stage 5: the projected momentum equation -/

/-- **Clay semantic-promotion edge 2b-ii.a: the projected momentum equation.**

Along an endpoint-safe projected mild solution, the decoded physical velocity satisfies

`∂ₜU = νΔU − P((U·∇)U)`

at every interior time, with a strong `L²`-valued time derivative, `Δ` the decoded
Laplacian (the genuine distributional Laplacian by
`r3L2ToTempered_r3H3LaplacianL2Operator`), and the nonlinear term the Leray projection of
the edge-2b-i identified literal pointwise convection `(U·∇)U` of the decoded
representatives. -/
theorem r3EndpointSafeProjectedMild_momentum (hnu : 0 < ν)
    (hu : IsR3EndpointSafeProjectedMildSolutionOn hnu T u₀ u) {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun s : ℝ => r3H3ToL2Operator (u s))
      (ν • r3H3LaplacianL2Operator (u t) -
        r3LerayL2Operator (r3DecodedConvectionL2 (u t) (u t))) t := by
  have h := hasDerivAt_r3MildDecodedVelocity hnu hu ht
  rwa [r3MildMomentumIntegrand, r3MildConvectionSource_eq] at h

/-- **Non-vacuity by composition with local existence**: for every viscosity and every
initial coordinate, there is a certified positive horizon and a mild solution along which
the projected momentum equation holds at every interior time. -/
theorem exists_r3EndpointSafeProjectedMild_momentum {ν : ℝ} (hnu : 0 < ν)
    (u₀ : R3HsVelocity 3) :
    ∃ T : ℝ, 0 < T ∧ ∃ u : ℝ → R3HsVelocity 3,
      IsR3EndpointSafeProjectedMildSolutionOn hnu T u₀ u ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) T,
        HasDerivAt (fun s : ℝ => r3H3ToL2Operator (u s))
          (ν • r3H3LaplacianL2Operator (u t) -
            r3LerayL2Operator (r3DecodedConvectionL2 (u t) (u t))) t := by
  obtain ⟨T, hT, -, u, hu, -⟩ :=
    r3EndpointSafeProjected_exists_localMildSolution hnu u₀
  exact ⟨T, hT, u, hu, fun t ht => r3EndpointSafeProjectedMild_momentum hnu hu ht⟩

end

end MNS2
