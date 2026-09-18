import NSFormalization.Section3.T16.LocalPotential

/-!
# T16 (`lem:potential`), Gap 1: the radial vector potential on the chart ball

`research/T16/ATTEMPTS.md` §"Gap 1" isolates the two residual analytic facts of
`lem:potential` (`paper/sections/03-torus.tex:176-216`).  The Section 4 `I02`
lemmas (`timePotential_contDiffOn`, `spatialCurl_timePotential_on`) only accept a
reference velocity that is smooth (and divergence-free) on the *whole* physical
space slab `I ×ˢ (univ : Set Space)`, whereas the torus hypothesis of T16 only
gives the reference on the coordinate ball `I ×ˢ Metric.ball x₀ r`.  This module
closes that gap for the potential fields `potential_smooth`, `potential_formula`
and `potential_curl` of
`NSFormalization.Section3.T16.LocalPotentialAPI`.

## The construction

For `x ∈ Metric.ball x₀ r` the radial vector potential
`A(t,x) = ∫₀¹ ρ · v(t, x₀+ρ(x-x₀)) × (x-x₀) dρ`
reads the reference only along the radial segment `[x₀, x]`, a compact subset of
the open ball.  Choosing a `ContDiffBump` cutoff `χ` centred at `x₀` that is `1`
on a slightly smaller ball containing that segment and supported in
`Metric.ball x₀ r`, the truncated field `V = χ · v` is *globally* smooth (`χ`
kills the region where `v` is not controlled), agrees with `v` on a neighbourhood
of the segment, and is divergence-free there (`div(χ v) = ∇χ·v + χ div v` and
`∇χ = 0` where `χ ≡ 1`).  Transferring through the pointwise slicewise congruence
`timePotential_congr_segment` yields:

* `timePotential_contDiffOn_ball`  — smoothness of the potential on the ball
  (reusing `I02.timePotential_contDiffOn` for the truncated field);
* `spatialCurl_timePotential_on_ball` — the curl identity `curl A(t,·) = v(t,·)`
  on the ball (using the segment-localized curl lemma
  `curl_centeredPotential_of_segment`, a faithful weakening of
  `RadialPotential.curl_centeredPotential` that only needs divergence-freeness on
  the segment, since that is all `curl_potential` actually consumes).

`exists_potential_on_ball` packages the three T16 fields so lane 353 can fill
`potential_smooth`/`potential_formula`/`potential_curl` by `exact`.

Route decision (`ATTEMPTS.md` §"Gap 1", option (b)): `spatialCurl_timePotential_on`
is genuinely global — it feeds `RadialPotential.curl_centeredPotential`, whose
`hdiv` hypothesis is universally quantified — so we re-derive the curl identity
locally.  Inspecting `RadialPotential.curl_potential` shows the divergence is only
ever used at the segment points `r • x`, `r ∈ [0,1]`; hence
`curl_potential_of_segment` needs `hdiv` only on `Set.Icc 0 1`, and the truncated
field `χ v` (divergence-free on the plateau ball that contains the segment)
qualifies.
-/

noncomputable section

namespace NSFormalization.Section3.T16

open Set MeasureTheory
open NavierStokes NavierStokes.ProblemStatement NavierStokes.SpatialCurl
open NSFormalization.Paper1.RadialPotential
open NSFormalization.Section4.A02 (SpaceTimeField SpatialField)
open scoped ContDiff Topology

/-! ## 1. A segment-localized weakening of the curl identity

`RadialPotential.curl_potential` uses its divergence hypothesis only through
`hdiv (r • x)` for `r` ranging over the integration interval `[0,1]`.  The two
lemmas below repeat that proof verbatim, replacing the interval-integral
`funext` step by `intervalIntegral.integral_congr` on `[[0,1]] = Set.Icc 0 1`, so
that divergence-freeness is required only on the segment. -/

/-- Segment version of `RadialPotential.curl_potential`: the curl of the radial
potential equals the field, provided the field is smooth and divergence-free
**only on the radial segment** `{r • x : r ∈ [0,1]}`. -/
theorem curl_potential_of_segment {v : Space → Space} (hv : ContDiff ℝ ∞ v) {x : Space}
    (hdiv : ∀ r ∈ Set.Icc (0 : ℝ) 1,
      (∑ i : Fin 3, (fderiv ℝ v (r • x) (coordinateVector i)) i) = 0) :
    curl (potential v) x = v x := by
  rw [curl_potential_integral hv]
  have hcongr : (∫ r in (0 : ℝ)..1, curl (fun y => integrand v (y, r)) x)
      = ∫ r in (0 : ℝ)..1,
          ((2 * r) • v (r • x) + (r ^ 2) • (fderiv ℝ v (r • x) x)) := by
    apply intervalIntegral.integral_congr
    intro r hr
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hr
    exact curl_integrand hv r x (hdiv r hr)
  rw [hcongr]
  have hc : Continuous (fun r : ℝ =>
      (2 * r) • v (r • x) + (r ^ 2) • (fderiv ℝ v (r • x) x)) := by
    have hvd : Continuous (fderiv ℝ v) := (hv.fderiv_right (m := ∞) (by simp)).continuous
    fun_prop
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r _ => radial_derivative hv x r) (hc.intervalIntegrable 0 1)
  simpa using hFTC

/-- Segment version of `RadialPotential.curl_centeredPotential`: divergence
freeness is required only on the radial segment `{x₀ + r • (x - x₀) : r ∈ [0,1]}`. -/
theorem curl_centeredPotential_of_segment {v : Space → Space} (hv : ContDiff ℝ ∞ v)
    {x₀ x : Space}
    (hdiv : ∀ r ∈ Set.Icc (0 : ℝ) 1,
      (∑ i : Fin 3, (fderiv ℝ v (x₀ + r • (x - x₀)) (coordinateVector i)) i) = 0) :
    curl (centeredPotential v x₀) x = v x := by
  have hw : ContDiff ℝ ∞ (fun y => v (x₀ + y)) := hv.comp (contDiff_const.add contDiff_id)
  have hwdiv : ∀ r ∈ Set.Icc (0 : ℝ) 1,
      (∑ i : Fin 3,
        (fderiv ℝ (fun z => v (x₀ + z)) (r • (x - x₀)) (coordinateVector i)) i) = 0 := by
    intro r hr
    rw [fderiv_comp_add_left]
    exact hdiv r hr
  change curlLinear (fderiv ℝ (fun y => potential (fun z => v (x₀ + z)) (y - x₀)) x) = _
  rw [fderiv_comp_sub]
  have h := curl_potential_of_segment hw hwdiv (x := x - x₀)
  have hx : x₀ + (x - x₀) = x := by abel
  simpa only [curl, hx] using h

/-! ## 2. Slicewise segment congruence of the radial potential -/

/-- The radial potential at `(t,y)` reads the reference only along the segment
`[x₀, y]`: if `v` and `V` agree on that segment at time `t`, the potentials
agree. -/
theorem timePotential_congr_segment (v V : VelocityField) (x₀ : Space) (t : ℝ) (y : Space)
    (h : ∀ r ∈ Set.Icc (0 : ℝ) 1,
      v (t, x₀ + r • (y - x₀)) = V (t, x₀ + r • (y - x₀))) :
    timePotential v x₀ (t, y) = timePotential V x₀ (t, y) := by
  show potential (fun z => v (t, x₀ + z)) (y - x₀)
      = potential (fun z => V (t, x₀ + z)) (y - x₀)
  apply intervalIntegral.integral_congr
  intro r hr
  rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hr
  show r • cross (v (t, x₀ + r • (y - x₀))) (y - x₀)
      = r • cross (V (t, x₀ + r • (y - x₀))) (y - x₀)
  rw [h r hr]

/-! ## 3. Global smoothness of the truncated reference -/

/-- The truncated reference `χ · v` (with `χ` a spatial cutoff supported in the
ball where `v` is smooth) is jointly smooth on the whole time slab `I ×ˢ univ`:
on the ball `v` is smooth and `χ` is smooth, and off `tsupport χ` the product
vanishes. -/
theorem contDiffOn_bumpSmul {v : VelocityField} {x₀ : Space} {r : ℝ} {I : Set ℝ}
    (hI : IsOpen I) (hv : ContDiffOn ℝ ∞ v (I ×ˢ Metric.ball x₀ r))
    {χ : Space → ℝ} (hχ : ContDiff ℝ ∞ χ) (hsupp : tsupport χ ⊆ Metric.ball x₀ r) :
    ContDiffOn ℝ ∞ (fun z : SpaceTime => χ z.2 • v z) (I ×ˢ (univ : Set Space)) := by
  rintro ⟨s, y⟩ hsy
  by_cases hy : y ∈ Metric.ball x₀ r
  · have hmem : I ×ˢ Metric.ball x₀ r ∈ 𝓝 (s, y) :=
      prod_mem_nhds (hI.mem_nhds hsy.1) (Metric.isOpen_ball.mem_nhds hy)
    have hv_at : ContDiffAt ℝ ∞ v (s, y) := hv.contDiffAt hmem
    have hχ_at : ContDiffAt ℝ ∞ (fun z : SpaceTime => χ z.2) (s, y) :=
      (hχ.comp contDiff_snd).contDiffAt
    exact (hχ_at.smul hv_at).contDiffWithinAt
  · have hyc : y ∈ (tsupport χ)ᶜ := fun hy' => hy (hsupp hy')
    have hnb : (univ : Set ℝ) ×ˢ (tsupport χ)ᶜ ∈ 𝓝 (s, y) :=
      (isOpen_univ.prod (isClosed_tsupport χ).isOpen_compl).mem_nhds ⟨mem_univ s, hyc⟩
    have heq : (fun z : SpaceTime => χ z.2 • v z) =ᶠ[𝓝 (s, y)] (fun _ => (0 : Space)) := by
      filter_upwards [hnb] with z hz
      rw [image_eq_zero_of_notMem_tsupport hz.2, zero_smul]
    exact (contDiffAt_const.congr_of_eventuallyEq heq).contDiffWithinAt

/-- The spatial slice of the truncated reference at a fixed time is globally
smooth. -/
theorem contDiff_bumpSmul_slice {v : VelocityField} {x₀ : Space} {r t : ℝ}
    (hslice : ContDiffOn ℝ ∞ (fun y : Space => v (t, y)) (Metric.ball x₀ r))
    {χ : Space → ℝ} (hχ : ContDiff ℝ ∞ χ) (hsupp : tsupport χ ⊆ Metric.ball x₀ r) :
    ContDiff ℝ ∞ (fun y : Space => χ y • v (t, y)) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y ∈ Metric.ball x₀ r
  · have hv_at : ContDiffAt ℝ ∞ (fun y : Space => v (t, y)) y :=
      hslice.contDiffAt (Metric.isOpen_ball.mem_nhds hy)
    exact hχ.contDiffAt.smul hv_at
  · have hyc : y ∈ (tsupport χ)ᶜ := fun hy' => hy (hsupp hy')
    have heq : (fun y : Space => χ y • v (t, y)) =ᶠ[𝓝 y] (fun _ => (0 : Space)) := by
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hyc] with z hz
      rw [image_eq_zero_of_notMem_tsupport hz, zero_smul]
    exact contDiffAt_const.congr_of_eventuallyEq heq

/-! ## 4. The two residual lemmas of `ATTEMPTS.md` §"Gap 1" -/

-- `maxHeartbeats 400000` (≤ policy cap): the neighbourhood transfer chains
-- several `ContDiffWithinAt`/`fderiv` congruences.
set_option maxHeartbeats 400000 in
/-- **Gap 1a.** Spatial-ball companion of `I02.timePotential_contDiffOn`: the
radial potential is smooth on the coordinate ball whenever the reference is. -/
theorem timePotential_contDiffOn_ball {v : VelocityField} {x₀ : Space} {r : ℝ} {I : Set ℝ}
    (hI : IsOpen I) (hv : ContDiffOn ℝ ∞ v (I ×ˢ Metric.ball x₀ r)) :
    ContDiffOn ℝ ∞ (timePotential v x₀) (I ×ˢ Metric.ball x₀ r) := by
  rintro ⟨t₀, x₁⟩ hz
  obtain ⟨ht₀, hx₁⟩ := hz
  have hd : dist x₁ x₀ < r := by rwa [Metric.mem_ball] at hx₁
  obtain ⟨r', hdr', hr'r⟩ := exists_between hd
  obtain ⟨r'', hr'r'', hr''r⟩ := exists_between hr'r
  have hr'pos : 0 < r' := lt_of_le_of_lt dist_nonneg hdr'
  set f : ContDiffBump x₀ := ⟨r', r'', hr'pos, hr'r''⟩ with hfdef
  have hχsupp : tsupport (f : Space → ℝ) ⊆ Metric.ball x₀ r := by
    rw [f.tsupport_eq]
    exact Metric.closedBall_subset_ball hr''r
  have hV₁ : ContDiffOn ℝ ∞ (fun z : SpaceTime => (f : Space → ℝ) z.2 • v z)
      (I ×ˢ (univ : Set Space)) :=
    contDiffOn_bumpSmul hI hv f.contDiff hχsupp
  have hpotV₁ : ContDiffOn ℝ ∞ (timePotential (fun z => (f : Space → ℝ) z.2 • v z) x₀)
      (I ×ˢ (univ : Set Space)) :=
    NSFormalization.Section4.I02.timePotential_contDiffOn hI hV₁ x₀
  have hpotV₁_at : ContDiffAt ℝ ∞ (timePotential (fun z => (f : Space → ℝ) z.2 • v z) x₀)
      (t₀, x₁) :=
    hpotV₁.contDiffAt ((hI.prod isOpen_univ).mem_nhds ⟨ht₀, mem_univ x₁⟩)
  -- On the open neighbourhood `I ×ˢ ball x₀ r'` the two potentials coincide.
  have hsub : ∀ z ∈ I ×ˢ Metric.ball x₀ r',
      timePotential v x₀ z = timePotential (fun w => (f : Space → ℝ) w.2 • v w) x₀ z := by
    rintro ⟨zt, zy⟩ ⟨-, hzy⟩
    show timePotential v x₀ (zt, zy)
        = timePotential (fun w => (f : Space → ℝ) w.2 • v w) x₀ (zt, zy)
    apply timePotential_congr_segment
    intro ρ hρ
    have hpt : x₀ + ρ • (zy - x₀) ∈ Metric.closedBall x₀ r' := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      have hsub' : x₀ + ρ • (zy - x₀) - x₀ = ρ • (zy - x₀) := by abel
      rw [hsub', norm_smul, Real.norm_eq_abs, abs_of_nonneg hρ.1]
      have hzynorm : ‖zy - x₀‖ < r' := by
        rw [← dist_eq_norm]; rwa [Metric.mem_ball] at hzy
      nlinarith [hρ.1, hρ.2, norm_nonneg (zy - x₀), hzynorm]
    have hf1 : (f : Space → ℝ) (x₀ + ρ • (zy - x₀)) = 1 := f.one_of_mem_closedBall hpt
    show v (zt, x₀ + ρ • (zy - x₀))
        = (f : Space → ℝ) (x₀ + ρ • (zy - x₀)) • v (zt, x₀ + ρ • (zy - x₀))
    rw [hf1, one_smul]
  have hnb : I ×ˢ Metric.ball x₀ r' ∈ 𝓝[I ×ˢ Metric.ball x₀ r] (t₀, x₁) :=
    mem_nhdsWithin_of_mem_nhds
      ((hI.prod Metric.isOpen_ball).mem_nhds ⟨ht₀, Metric.mem_ball.mpr hdr'⟩)
  have heq : timePotential v x₀ =ᶠ[𝓝[I ×ˢ Metric.ball x₀ r] (t₀, x₁)]
      timePotential (fun w => (f : Space → ℝ) w.2 • v w) x₀ := by
    filter_upwards [hnb] with z hz' using hsub z hz'
  exact hpotV₁_at.contDiffWithinAt.congr_of_eventuallyEq heq
    (heq.self_of_nhdsWithin ⟨ht₀, hx₁⟩)

-- `maxHeartbeats 400000` (≤ policy cap): the curl transfer chains segment
-- congruences, an `fderiv` rewrite and the segment-localized curl lemma.
set_option maxHeartbeats 400000 in
/-- **Gap 1b.** Spatial-ball companion of `I02.spatialCurl_timePotential_on`: the
spatial curl of the radial potential recovers the reference on the coordinate
ball, using divergence-freeness only on the ball. -/
theorem spatialCurl_timePotential_on_ball {v : VelocityField} {x₀ : Space} {r : ℝ} {I : Set ℝ}
    (hv : ContDiffOn ℝ ∞ v (I ×ˢ Metric.ball x₀ r))
    (hdiv : ∀ t ∈ I, ∀ x ∈ Metric.ball x₀ r, spatialDivergence v t x = 0)
    {t : ℝ} (ht : t ∈ I) {x : Space} (hx : x ∈ Metric.ball x₀ r) :
    SpatialCurl.curl (fun y => timePotential v x₀ (t, y)) x = v (t, x) := by
  have hd : dist x x₀ < r := by rwa [Metric.mem_ball] at hx
  obtain ⟨r', hdr', hr'r⟩ := exists_between hd
  obtain ⟨r'', hr'r'', hr''r⟩ := exists_between hr'r
  have hr'pos : 0 < r' := lt_of_le_of_lt dist_nonneg hdr'
  set f : ContDiffBump x₀ := ⟨r', r'', hr'pos, hr'r''⟩ with hfdef
  have hχsupp : tsupport (f : Space → ℝ) ⊆ Metric.ball x₀ r := by
    rw [f.tsupport_eq]
    exact Metric.closedBall_subset_ball hr''r
  have hslice : ContDiffOn ℝ ∞ (fun y : Space => v (t, y)) (Metric.ball x₀ r) :=
    hv.comp ((contDiff_const.prodMk contDiff_id).contDiffOn) (fun y hy => ⟨ht, hy⟩)
  have hw : ContDiff ℝ ∞ (fun y : Space => (f : Space → ℝ) y • v (t, y)) :=
    contDiff_bumpSmul_slice hslice f.contDiff hχsupp
  -- The truncated slice equals `v(t,·)` on the plateau ball.
  have hweq : Set.EqOn (fun y : Space => (f : Space → ℝ) y • v (t, y))
      (fun y => v (t, y)) (Metric.ball x₀ r') := by
    intro y hy
    have h1 : (f : Space → ℝ) y = 1 := f.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)
    show (f : Space → ℝ) y • v (t, y) = v (t, y)
    rw [h1, one_smul]
  -- Divergence-freeness on the segment through `x`.
  have hwdiv : ∀ ρ ∈ Set.Icc (0 : ℝ) 1,
      (∑ i : Fin 3,
        (fderiv ℝ (fun y : Space => (f : Space → ℝ) y • v (t, y))
          (x₀ + ρ • (x - x₀)) (coordinateVector i)) i) = 0 := by
    intro ρ hρ
    have hp_ball : x₀ + ρ • (x - x₀) ∈ Metric.ball x₀ r' := by
      rw [Metric.mem_ball, dist_eq_norm]
      have hsub' : x₀ + ρ • (x - x₀) - x₀ = ρ • (x - x₀) := by abel
      rw [hsub', norm_smul, Real.norm_eq_abs, abs_of_nonneg hρ.1]
      have hxnorm : ‖x - x₀‖ < r' := by rw [← dist_eq_norm]; exact hdr'
      nlinarith [hρ.1, hρ.2, norm_nonneg (x - x₀), hxnorm]
    have hp_ballr : x₀ + ρ • (x - x₀) ∈ Metric.ball x₀ r :=
      Metric.ball_subset_ball (le_of_lt hr'r) hp_ball
    have hev : (fun y : Space => (f : Space → ℝ) y • v (t, y))
        =ᶠ[𝓝 (x₀ + ρ • (x - x₀))] (fun y => v (t, y)) :=
      hweq.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hp_ball)
    rw [hev.fderiv_eq]
    exact hdiv t ht _ hp_ballr
  -- Segment congruence: the two potential slices agree on the plateau ball.
  have hfun_eq : Set.EqOn (fun y => timePotential v x₀ (t, y))
      (fun y => timePotential (fun w => (f : Space → ℝ) w.2 • v w) x₀ (t, y))
      (Metric.ball x₀ r') := by
    intro y hy
    show timePotential v x₀ (t, y)
        = timePotential (fun w => (f : Space → ℝ) w.2 • v w) x₀ (t, y)
    apply timePotential_congr_segment
    intro ρ hρ
    have hpt : x₀ + ρ • (y - x₀) ∈ Metric.closedBall x₀ r' := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      have hsub' : x₀ + ρ • (y - x₀) - x₀ = ρ • (y - x₀) := by abel
      rw [hsub', norm_smul, Real.norm_eq_abs, abs_of_nonneg hρ.1]
      have hynorm : ‖y - x₀‖ < r' := by
        rw [← dist_eq_norm]; rwa [Metric.mem_ball] at hy
      nlinarith [hρ.1, hρ.2, norm_nonneg (y - x₀), hynorm]
    have hf1 : (f : Space → ℝ) (x₀ + ρ • (y - x₀)) = 1 := f.one_of_mem_closedBall hpt
    show v (t, x₀ + ρ • (y - x₀))
        = (f : Space → ℝ) (x₀ + ρ • (y - x₀)) • v (t, x₀ + ρ • (y - x₀))
    rw [hf1, one_smul]
  have hev : (fun y => timePotential v x₀ (t, y))
      =ᶠ[𝓝 x] (fun y => timePotential (fun w => (f : Space → ℝ) w.2 • v w) x₀ (t, y)) :=
    hfun_eq.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds (Metric.mem_ball.mpr hdr'))
  have hcurl_eq : SpatialCurl.curl (fun y => timePotential v x₀ (t, y)) x
      = SpatialCurl.curl
          (fun y => timePotential (fun w => (f : Space → ℝ) w.2 • v w) x₀ (t, y)) x := by
    unfold SpatialCurl.curl
    rw [hev.fderiv_eq]
  rw [hcurl_eq]
  -- The truncated potential slice is a centered potential of the truncated field.
  have hWslice : (fun y => timePotential (fun w => (f : Space → ℝ) w.2 • v w) x₀ (t, y))
      = centeredPotential (fun y => (f : Space → ℝ) y • v (t, y)) x₀ := rfl
  rw [hWslice, curl_centeredPotential_of_segment hw hwdiv]
  have hfx : (f : Space → ℝ) x = 1 :=
    f.one_of_mem_closedBall (Metric.ball_subset_closedBall (Metric.mem_ball.mpr hdr'))
  show (f : Space → ℝ) x • v (t, x) = v (t, x)
  rw [hfx, one_smul]

/-! ## 5. The three T16 potential fields, packaged for the assembly lane -/

/-- The radial vector potential exists on the coordinate ball with exactly the
three clauses `potential_smooth`, `potential_formula`, `potential_curl` of
`NSFormalization.Section3.T16.LocalPotentialAPI`.  Lane 353 sets
`D.potential := timePotential v x₀` and closes those fields by `exact`. -/
theorem exists_potential_on_ball {v : SpaceTimeField} {x₀ : Space} {r T δ : ℝ}
    (hv : ContDiffOn ℝ ∞ v (Ioo (0 : ℝ) (T + δ) ×ˢ Metric.ball x₀ r))
    (hdiv : ∀ t ∈ Ioo (0 : ℝ) (T + δ), ∀ x ∈ Metric.ball x₀ r,
      spatialDivergence v t x = 0) :
    ∃ A : SpaceTimeField,
      ContDiffOn ℝ ∞ A (Ioo (0 : ℝ) (T + δ) ×ˢ Metric.ball x₀ r) ∧
      (∀ t x, A (t, x) =
        ∫ ρ in (0 : ℝ)..1, ρ • cross (v (t, x₀ + ρ • (x - x₀))) (x - x₀)) ∧
      (∀ t ∈ Ioo (0 : ℝ) (T + δ), ∀ x ∈ Metric.ball x₀ r,
        SpatialCurl.curl (fun y => A (t, y)) x = v (t, x)) := by
  refine ⟨timePotential v x₀, ?_, ?_, ?_⟩
  · exact timePotential_contDiffOn_ball isOpen_Ioo hv
  · intro t x
    exact centeredPotential_eq_integral (fun y => v (t, y)) x₀ x
  · intro t ht x hx
    exact spatialCurl_timePotential_on_ball hv hdiv ht hx

end NSFormalization.Section3.T16
