import NSFormalization.Section3.T13.LocalizationKernel

/-!
# T13 kernel comparison with the paper's geometric constant (`03-torus.tex:73-98`)

This module proves the four residual analytic items of
`research/T13/ATTEMPTS_LOCALIZATION_KERNEL.md`, closing §2 of the localization
estimate `eq:localization`.  None of them is a `LocalizationAPI` field; lane 359
assembles `localization` from these together with `torus_identity` (lane 345),
`endpoint_zero`/`constant_pos_finite` (lane 344), the §3 comparison
`periodicSobolevENorm_le_l2_add_homogeneous` (lane 353) and a
`wholeSpace_identity`-shaped hypothesis.

* `exists_separation` — the closed support ball, being compact inside the open
  cube `(0,1)³`, is contained in a shrunken cube `[δ,1-δ]³` for some `δ>0`.
* `tailGeomConst` / `tailGeomConst_lt_top` / `latticeTail_le_tailGeomConst` —
  the paper's uniform geometric bound
  `sup_{x∈B̄,y∈Q} ∑_{n≠0}|x-y+n|^{-3-2s} ≤ C_{s,d} < ∞`.  The single uniform
  lower bound `|x-y+n| ≥ c₀|n|` (with `c₀ = min(1/2, δ/(2√3))`) combines the
  coordinate separation `|x-y+n| ≥ δ` (from `exists_separation`) with the
  triangle bound `|x-y+n| ≥ |n|-√3`.  This replaces the naive constant
  `tailConst s (2r)` of lane 353, which cannot control the region
  `x∈B, y∈Q\B` where `|x-y|` may reach `√3` (see the ATTEMPTS file).
* `iTorus_singular_le` — the `n=0` term of `I_𝕋(z_𝕋)` is at most `I_ℝ(z_ℝ)`:
  substitute `y=x+h` (translation-invariant `lintegral`), Tonelli, and enlarge
  both cube domains to `ℝ³`.
* `iTorus_periodize_le` — assembling the two parts with `|Q|=1` and
  `|z(x)-z(y)|² ≤ 2|z(x)|²+2|z(y)|²`, giving the localization comparison
  `I_𝕋(periodize f) ≤ I_ℝ(f) + 4·C_{s,d}·‖f‖₂²`.

No named input is used; every declaration below is proved outright.

## Statement fidelity (checked against `03-torus.tex:79-92`)

The brief's four statements match the paper, once the separation constant is
made explicit.  The paper writes `d = dist(B̄,∂Q)` and asserts `|x-y+n| ≥ d` for
`x∈B̄, y∈Q, n≠0` (line 82: "the point `y-n` lies outside `Q` up to its
boundary"), plus `|x-y+n| ≥ |n|/2` for `|n|>2√3` (line 83).  Here `d` is
realized by the concrete `separationRadius c r` (the coordinatewise distance of
`B̄` to `∂Q`); the two regimes are fused into the single uniform bound
`|x-y+n| ≥ c₀|n|` which is what the `ℝ≥0∞` `rpow` estimate needs.  The paper's
`4C_{s,d}‖z‖₂²` becomes `4·tailGeomConst s c r·(eLpNorm f 2 volume)²`.
-/

noncomputable section

namespace NSFormalization.Section3.T13

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField)
open NSFormalization.Section3.T10
open NavierStokes.PeriodicIntegration (Coords toSpace)
open scoped ContDiff ENNReal BigOperators Topology

/-! ## §0  Lattice-norm and coordinate helpers -/

/-- Public re-derivation of the (privately-stated) lower bound
`‖latticeVector n‖ ≥ 1` for `n ≠ 0`. -/
theorem latticeVector_norm_ge_one {n : PeriodicFrequency} (hn : n ≠ 0) :
    (1 : ℝ) ≤ ‖latticeVector n‖ := by
  obtain ⟨i, hi⟩ : ∃ i, n i ≠ 0 := Function.ne_iff.mp hn
  have h1 : (1 : ℝ) ≤ |(n i : ℝ)| := by exact_mod_cast Int.one_le_abs hi
  rw [← latticeVector_apply n i] at h1
  exact h1.trans (abs_spaceCoord_le_norm _ _)

/-- The nonzero-lattice tail is even in its argument: it depends only on the
distances `‖h + n‖`, which are invariant under `h ↦ -h`, `n ↦ -n`. -/
theorem latticeTail_neg (s : ℝ) (h : Space) : latticeTail s (-h) = latticeTail s h := by
  let negNe : {n : PeriodicFrequency // n ≠ 0} ≃ {n : PeriodicFrequency // n ≠ 0} :=
    { toFun := fun n => ⟨-n.1, neg_ne_zero.mpr n.2⟩
      invFun := fun n => ⟨-n.1, neg_ne_zero.mpr n.2⟩
      left_inv := fun n => by simp
      right_inv := fun n => by simp }
  rw [latticeTail, latticeTail,
    ← negNe.tsum_eq (fun n : {n : PeriodicFrequency // n ≠ 0} =>
      fractionalRadialKernel s (h + latticeVector n.1))]
  refine tsum_congr fun n => ?_
  have h1 : latticeVector (negNe n).1 = -latticeVector n.1 := latticeVector_neg n.1
  show fractionalRadialKernel s (-h + latticeVector n.1)
      = fractionalRadialKernel s (h + latticeVector (negNe n).1)
  rw [fractionalRadialKernel, fractionalRadialKernel, h1,
    show h + -latticeVector n.1 = -(-h + latticeVector n.1) by abel, norm_neg]

/-! ## §1  The coordinate separation of the support ball from `∂Q` -/

/-- Per-coordinate: both coordinates of the closed ball's supporting points lie
strictly inside `(0,1)`, so `0 < c i - r` and `c i + r < 1`. -/
theorem ball_coord_bounds {c : Space} {r : ℝ} (hr : 0 < r)
    (hball : closure (Metric.ball c r) ⊆ interior fundamentalCube) (i : Fin 3) :
    0 < c i - r ∧ c i + r < 1 := by
  have hclosed : closure (Metric.ball c r) = Metric.closedBall c r :=
    closure_ball c (ne_of_gt hr)
  have he : ‖(EuclideanSpace.single i r : Space)‖ = r := by simp [abs_of_pos hr]
  have hplus : c + EuclideanSpace.single i r ∈ interior fundamentalCube := by
    apply hball; rw [hclosed, Metric.mem_closedBall, dist_eq_norm]; simp [he]
  have hminus : c - EuclideanSpace.single i r ∈ interior fundamentalCube := by
    apply hball; rw [hclosed, Metric.mem_closedBall, dist_eq_norm]; simp [he]
  rw [interior_fundamentalCube] at hplus hminus
  have hp := hplus i
  have hm := hminus i
  have ep : (c + EuclideanSpace.single i r) i = c i + r := by simp
  have em : (c - EuclideanSpace.single i r) i = c i - r := by simp
  rw [ep] at hp
  rw [em] at hm
  exact ⟨hm.1, hp.2⟩

/-- The concrete coordinatewise distance of `B̄` from `∂Q`, realizing the
paper's `d = dist(B̄,∂Q)`. -/
def separationRadius (c : Space) (r : ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i : Fin 3 => min (c i - r) (1 - c i - r))

theorem separationRadius_le (c : Space) (r : ℝ) (i : Fin 3) :
    separationRadius c r ≤ c i - r ∧ separationRadius c r ≤ 1 - c i - r := by
  have h : separationRadius c r ≤ min (c i - r) (1 - c i - r) :=
    Finset.inf'_le (fun j => min (c j - r) (1 - c j - r)) (Finset.mem_univ i)
  exact ⟨h.trans (min_le_left _ _), h.trans (min_le_right _ _)⟩

theorem separationRadius_pos {c : Space} {r : ℝ} (hr : 0 < r)
    (hball : closure (Metric.ball c r) ⊆ interior fundamentalCube) :
    0 < separationRadius c r := by
  rw [separationRadius, Finset.lt_inf'_iff]
  intro i _
  obtain ⟨h1, h2⟩ := ball_coord_bounds hr hball i
  exact lt_min h1 (by linarith)

/-- The coordinate bounds of a point of the closed support ball inside the
shrunken cube `[δ,1-δ]³`. -/
theorem closedBall_coord_sep {c : Space} {r : ℝ}
    {x : Space} (hx : x ∈ Metric.closedBall c r) (i : Fin 3) :
    separationRadius c r ≤ x i ∧ x i ≤ 1 - separationRadius c r := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hx
  have hc : |x i - c i| ≤ r := by
    have h := abs_spaceCoord_le_norm (x - c) i
    have he : (x - c) i = x i - c i := rfl
    rw [he] at h
    exact h.trans hx
  rw [abs_le] at hc
  obtain ⟨hle1, hle2⟩ := separationRadius_le c r i
  exact ⟨by linarith [hc.1], by linarith [hc.2]⟩

/-- **Item 1.**  The compact closed ball inside the open cube is contained in a
shrunken cube `{x | ∀ i, δ ≤ x i ≤ 1-δ}` for some `δ > 0`. -/
theorem exists_separation {c : Space} {r : ℝ} (hr : 0 < r)
    (hball : closure (Metric.ball c r) ⊆ interior fundamentalCube) :
    ∃ δ : ℝ, 0 < δ ∧
      closure (Metric.ball c r) ⊆ {x : Space | ∀ i, δ ≤ x i ∧ x i ≤ 1 - δ} := by
  refine ⟨separationRadius c r, separationRadius_pos hr hball, ?_⟩
  rw [closure_ball c (ne_of_gt hr)]
  intro x hx i
  exact closedBall_coord_sep hx i

/-! ## §2  The uniform geometric lower bound `‖x-y+n‖ ≥ c₀‖n‖` -/

/-- The Euclidean diameter bound of the unit cube: `‖x-y‖ ≤ √3` for `x,y∈Q`. -/
theorem norm_sub_le_sqrt3 {x y : Space}
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) (hy : ∀ i, 0 ≤ y i ∧ y i ≤ 1) :
    ‖x - y‖ ≤ Real.sqrt 3 := by
  rw [EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  have hbound : ∀ i : Fin 3, ‖(x - y) i‖ ^ 2 ≤ 1 := by
    intro i
    have he : (x - y) i = x i - y i := rfl
    rw [he, Real.norm_eq_abs]
    have hxi := hx i; have hyi := hy i
    have habs : |x i - y i| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith [hxi.1, hxi.2, hyi.1, hyi.2]
    nlinarith [abs_nonneg (x i - y i), habs]
  calc ∑ i : Fin 3, ‖(x - y) i‖ ^ 2 ≤ ∑ _i : Fin 3, (1 : ℝ) :=
        Finset.sum_le_sum (fun i _ => hbound i)
    _ = 3 := by simp

/-- The paper's separation coefficient `c₀ = min(1/2, δ/(2√3))`. -/
def tailGeomC0 (c : Space) (r : ℝ) : ℝ :=
  min (1 / 2) (separationRadius c r / (2 * Real.sqrt 3))

theorem tailGeomC0_pos {c : Space} {r : ℝ} (hr : 0 < r)
    (hball : closure (Metric.ball c r) ⊆ interior fundamentalCube) :
    0 < tailGeomC0 c r := by
  have hsqrt3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  refine lt_min (by norm_num) (div_pos (separationRadius_pos hr hball) (by linarith))

/-- **The uniform lower bound.**  For `x∈B̄`, `y∈Q`, `n≠0`,
`‖(x-y)+latticeVector n‖ ≥ tailGeomC0 c r · ‖latticeVector n‖`.  This fuses the
coordinate separation regime and the `|n|/2` triangle regime of
`03-torus.tex:81-83`. -/
theorem geom_norm_lower {c : Space} {r : ℝ} (hr : 0 < r)
    (hball : closure (Metric.ball c r) ⊆ interior fundamentalCube)
    {x : Space} (hx : x ∈ Metric.closedBall c r)
    {y : Space} (hy : y ∈ fundamentalCube)
    {n : PeriodicFrequency} (hn : n ≠ 0) :
    tailGeomC0 c r * ‖latticeVector n‖ ≤ ‖(x - y) + latticeVector n‖ := by
  rw [tailGeomC0]
  have hδpos : 0 < separationRadius c r := separationRadius_pos hr hball
  have hL1 : (1 : ℝ) ≤ ‖latticeVector n‖ := latticeVector_norm_ge_one hn
  have hLpos : 0 < ‖latticeVector n‖ := lt_of_lt_of_le one_pos hL1
  have hxsep : ∀ i, separationRadius c r ≤ x i ∧ x i ≤ 1 - separationRadius c r :=
    fun i => closedBall_coord_sep hx i
  have hxcube : ∀ i, 0 ≤ x i ∧ x i ≤ 1 := fun i =>
    ⟨le_trans hδpos.le (hxsep i).1, le_trans (hxsep i).2 (by linarith [hδpos.le])⟩
  -- Sub-bound 1: coordinate separation.
  have hsub1 : separationRadius c r ≤ ‖(x - y) + latticeVector n‖ := by
    obtain ⟨i, hi⟩ : ∃ i, n i ≠ 0 := Function.ne_iff.mp hn
    have hwi : ((x - y) + latticeVector n) i = x i - y i + (n i : ℝ) := by
      change (x - y) i + latticeVector n i = _
      rw [latticeVector_apply]; rfl
    have hxi := hxsep i
    have hyi := hy i
    have habs : separationRadius c r ≤ |((x - y) + latticeVector n) i| := by
      rw [hwi]
      rcases lt_or_gt_of_ne hi with hneg | hpos
      · have hz : (n i : ℝ) ≤ -1 := by exact_mod_cast (show n i ≤ -1 by omega)
        rw [le_abs]; right; linarith [hxi.2, hyi.1]
      · have hz : (1 : ℝ) ≤ (n i : ℝ) := by exact_mod_cast (show 1 ≤ n i by omega)
        rw [le_abs]; left; linarith [hxi.1, hyi.2]
    exact habs.trans (abs_spaceCoord_le_norm _ i)
  -- Sub-bound 2: reverse triangle with the cube diameter.
  have hsub2 : ‖latticeVector n‖ - Real.sqrt 3 ≤ ‖(x - y) + latticeVector n‖ := by
    have hxy : ‖x - y‖ ≤ Real.sqrt 3 := norm_sub_le_sqrt3 hxcube hy
    have htri : ‖latticeVector n‖ - ‖x - y‖ ≤ ‖(x - y) + latticeVector n‖ := by
      have h := norm_sub_norm_le (latticeVector n) (-(x - y))
      rw [norm_neg] at h
      rwa [show latticeVector n - -(x - y) = (x - y) + latticeVector n by abel] at h
    linarith
  -- Combine the two regimes.
  have hsqrt3pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have ht2 : 0 < 2 * Real.sqrt 3 := by linarith
  have hc0half : min (1 / 2 : ℝ) (separationRadius c r / (2 * Real.sqrt 3)) ≤ 1 / 2 :=
    min_le_left _ _
  have hc0div : min (1 / 2 : ℝ) (separationRadius c r / (2 * Real.sqrt 3))
      ≤ separationRadius c r / (2 * Real.sqrt 3) := min_le_right _ _
  by_cases hLcase : 2 * Real.sqrt 3 ≤ ‖latticeVector n‖
  · have hstep1 : min (1 / 2 : ℝ) (separationRadius c r / (2 * Real.sqrt 3)) * ‖latticeVector n‖
        ≤ (1 / 2) * ‖latticeVector n‖ := mul_le_mul_of_nonneg_right hc0half hLpos.le
    have hstep2 : (1 / 2) * ‖latticeVector n‖ ≤ ‖latticeVector n‖ - Real.sqrt 3 := by
      linarith [hLcase]
    linarith [hsub2, hstep1, hstep2]
  · rw [not_le] at hLcase
    have hdivnn : 0 ≤ separationRadius c r / (2 * Real.sqrt 3) := div_nonneg hδpos.le ht2.le
    have hstep1 : min (1 / 2 : ℝ) (separationRadius c r / (2 * Real.sqrt 3)) * ‖latticeVector n‖
        ≤ (separationRadius c r / (2 * Real.sqrt 3)) * ‖latticeVector n‖ :=
      mul_le_mul_of_nonneg_right hc0div hLpos.le
    have hstep2 : (separationRadius c r / (2 * Real.sqrt 3)) * ‖latticeVector n‖
        ≤ (separationRadius c r / (2 * Real.sqrt 3)) * (2 * Real.sqrt 3) :=
      mul_le_mul_of_nonneg_left hLcase.le hdivnn
    have hstep3 : (separationRadius c r / (2 * Real.sqrt 3)) * (2 * Real.sqrt 3)
        = separationRadius c r := div_mul_cancel₀ _ ht2.ne'
    linarith [hsub1, hstep1, hstep2, hstep3]

/-- **Item 2, the constant.**  The paper's `C_{s,d}`. -/
def tailGeomConst (s : ℝ) (c : Space) (r : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal (tailGeomC0 c r)) ^ (-(3 + 2 * s)) * tailSum s

theorem tailGeomConst_lt_top {s : ℝ} {c : Space} {r : ℝ} (hs : 0 < s) (hr : 0 < r)
    (hball : closure (Metric.ball c r) ⊆ interior fundamentalCube) :
    tailGeomConst s c r < ⊤ := by
  rw [tailGeomConst]
  refine ENNReal.mul_lt_top ?_ (tailSum_lt_top hs)
  rw [ENNReal.ofReal_rpow_of_pos (tailGeomC0_pos hr hball)]
  exact ENNReal.ofReal_lt_top

/-- **Item 2.**  The uniform geometric tail bound: for `x∈B̄` and `y∈Q`, the
nonzero lattice tail is `≤ tailGeomConst s c r`.  This is `03-torus.tex:85-88`. -/
theorem latticeTail_le_tailGeomConst {s : ℝ} {c : Space} {r : ℝ} (hs : 0 ≤ s) (hr : 0 < r)
    (hball : closure (Metric.ball c r) ⊆ interior fundamentalCube) :
    ∀ x ∈ closure (Metric.ball c r), ∀ y ∈ fundamentalCube,
      latticeTail s (x - y) ≤ tailGeomConst s c r := by
  intro x hx y hy
  rw [closure_ball c (ne_of_gt hr)] at hx
  rw [latticeTail, tailGeomConst, tailSum, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun n => ?_
  have hlow : tailGeomC0 c r * ‖latticeVector n.1‖ ≤ ‖(x - y) + latticeVector n.1‖ :=
    geom_norm_lower hr hball hx hy n.2
  have hc0pos : 0 < tailGeomC0 c r := tailGeomC0_pos hr hball
  have hlv1 : (1 : ℝ) ≤ ‖latticeVector n.1‖ := latticeVector_norm_ge_one n.2
  have hlvpos : 0 < ‖latticeVector n.1‖ := lt_of_lt_of_le one_pos hlv1
  simp only [fractionalRadialKernel]
  have hmono : (ENNReal.ofReal ‖(x - y) + latticeVector n.1‖) ^ (-(3 + 2 * s)) ≤
      (ENNReal.ofReal (tailGeomC0 c r * ‖latticeVector n.1‖)) ^ (-(3 + 2 * s)) := by
    rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
    refine ENNReal.inv_le_inv.mpr ?_
    exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hlow) (by linarith)
  have hsplit : (ENNReal.ofReal (tailGeomC0 c r * ‖latticeVector n.1‖)) ^ (-(3 + 2 * s)) =
      (ENNReal.ofReal (tailGeomC0 c r)) ^ (-(3 + 2 * s)) *
        (ENNReal.ofReal ‖latticeVector n.1‖) ^ (-(3 + 2 * s)) := by
    rw [ENNReal.ofReal_mul hc0pos.le,
      ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top]
  exact hmono.trans (le_of_eq hsplit)

/-! ## §3  The singular part `n=0` is bounded by the whole-space integral -/

/-- **Item 3.**  The `n=0` term of the torus Gagliardo integral over the cube is
at most `I_ℝ(f)` (`03-torus.tex:89-90`).  Only the continuity of `f` is used. -/
theorem iTorus_singular_le {s : ℝ} {f : SpatialField} (hfc : Continuous f) :
    (∫⁻ x in fundamentalCube, ∫⁻ y in fundamentalCube,
        ENNReal.ofReal (‖f x - f y‖ ^ 2) * fractionalRadialKernel s (x - y)) ≤ IReal s f := by
  calc (∫⁻ x in fundamentalCube, ∫⁻ y in fundamentalCube,
          ENNReal.ofReal (‖f x - f y‖ ^ 2) * fractionalRadialKernel s (x - y))
      ≤ ∫⁻ x in fundamentalCube, ∫⁻ y : Space,
          ENNReal.ofReal (‖f x - f y‖ ^ 2) * fractionalRadialKernel s (x - y) :=
        lintegral_mono fun x => setLIntegral_le_lintegral fundamentalCube _
    _ = ∫⁻ x in fundamentalCube, ∫⁻ h : Space,
          ENNReal.ofReal (‖f x - f (x - h)‖ ^ 2) * fractionalRadialKernel s h :=
        lintegral_congr fun x => lintegral_whole_shift x
    _ ≤ ∫⁻ x : Space, ∫⁻ h : Space,
          ENNReal.ofReal (‖f x - f (x - h)‖ ^ 2) * fractionalRadialKernel s h :=
        setLIntegral_le_lintegral fundamentalCube _
    _ = ∫⁻ h : Space, ∫⁻ x : Space,
          ENNReal.ofReal (‖f x - f (x - h)‖ ^ 2) * fractionalRadialKernel s h :=
        lintegral_lintegral_swap (measurable_prod_diff hfc).aemeasurable
    _ = IReal s f := by
        refine lintegral_congr fun h => ?_
        have hshift := lintegral_add_right_eq_self (μ := (volume : Measure Space))
          (fun x : Space => ENNReal.ofReal (‖f x - f (x - h)‖ ^ 2) * fractionalRadialKernel s h) h
        rw [← hshift]
        refine lintegral_congr fun x => ?_
        rw [add_sub_cancel_right]

/-! ## §4  Measurability helpers for the assembly -/

theorem measurable_latticeTail (s : ℝ) : Measurable (fun h : Space => latticeTail s h) := by
  unfold latticeTail
  refine Measurable.tsum fun n => ?_
  exact (measurable_fractionalRadialKernel s).comp (measurable_id.add_const (latticeVector n.1))

theorem measurable_prod_frac {s : ℝ} {f : SpatialField} (hfc : Continuous f) :
    Measurable (fun p : Space × Space =>
      ENNReal.ofReal (‖f p.1 - f p.2‖ ^ 2) * fractionalRadialKernel s (p.1 - p.2)) := by
  refine Measurable.mul ?_ ((measurable_fractionalRadialKernel s).comp
    (continuous_fst.sub continuous_snd).measurable)
  exact ENNReal.measurable_ofReal.comp
    (((hfc.comp continuous_fst).sub (hfc.comp continuous_snd)).norm.pow 2).measurable

theorem measurable_prod_tail {s : ℝ} {f : SpatialField} (hfc : Continuous f) :
    Measurable (fun p : Space × Space =>
      ENNReal.ofReal (‖f p.1 - f p.2‖ ^ 2) * latticeTail s (p.1 - p.2)) := by
  refine Measurable.mul ?_ ((measurable_latticeTail s).comp
    (continuous_fst.sub continuous_snd).measurable)
  exact ENNReal.measurable_ofReal.comp
    (((hfc.comp continuous_fst).sub (hfc.comp continuous_snd)).norm.pow 2).measurable

theorem measurable_inner_frac {s : ℝ} {f : SpatialField} (hfc : Continuous f) :
    Measurable (fun x : Space => ∫⁻ y in fundamentalCube,
      ENNReal.ofReal (‖f x - f y‖ ^ 2) * fractionalRadialKernel s (x - y)) :=
  (measurable_prod_frac hfc).lintegral_prod_right

/-! ## §5  The kernel split and the cube volume -/

/-- The periodic kernel splits into its singular `n=0` term and the tail. -/
theorem periodicKernel_split (s : ℝ) (h : Space) :
    periodicKernel s h = fractionalRadialKernel s h + latticeTail s h := by
  have hlt : latticeTail s h = ∑' x : PeriodicFrequency,
      Set.indicator {n : PeriodicFrequency | n ≠ 0}
        (fun n => fractionalRadialKernel s (h + latticeVector n)) x :=
    tsum_subtype {n : PeriodicFrequency | n ≠ 0}
      (fun n => fractionalRadialKernel s (h + latticeVector n))
  rw [periodicKernel, ENNReal.tsum_eq_add_tsum_ite (0 : PeriodicFrequency), hlt]
  simp only [latticeVector_zero, add_zero]
  congr 1
  refine tsum_congr fun x => ?_
  by_cases hx : x = 0
  · simp [hx]
  · simp [hx]

/-- `|Q| = 1`: the fixed fundamental cube has unit volume. -/
theorem volume_fundamentalCube : volume fundamentalCube = 1 := by
  have hmp : MeasurePreserving (toSpace : Coords → Space) volume volume :=
    PiLp.volume_preserving_toLp (Fin 3)
  have h1 : volume (toSpace ⁻¹' fundamentalCube) = volume fundamentalCube :=
    hmp.measure_preimage measurableSet_fundamentalCube.nullMeasurableSet
  rw [← h1, toSpace_preimage_fundamentalCube, ← Set.pi_univ_Icc, volume_pi_pi]
  simp [Real.volume_Icc]

/-- `(eLpNorm f 2 volume)² = ∫⁻ ‖f‖²`, the conversion connecting the tail bound
to the registered `L²` norm used by `endpoint_zero`. -/
theorem sq_eLpNorm_two (f : SpatialField) :
    eLpNorm f 2 volume ^ 2 = ∫⁻ x : Space, ENNReal.ofReal (‖f x‖ ^ 2) := by
  have hpt : (fun a : Space => ‖f a‖ₑ ^ (2 : ℝ)) = fun a => ENNReal.ofReal (‖f a‖ ^ 2) := by
    funext a
    rw [← ofReal_norm (f a),
      ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num), eLpNorm',
    show ((2 : ℝ≥0∞).toReal) = (2 : ℝ) by norm_num, hpt,
    ← ENNReal.rpow_natCast ((∫⁻ a : Space, ENNReal.ofReal (‖f a‖ ^ 2)) ^ (1 / (2 : ℝ))) 2,
    ← ENNReal.rpow_mul, show (1 / (2 : ℝ)) * ((2 : ℕ) : ℝ) = 1 by norm_num, ENNReal.rpow_one]

/-! ## §6  The assembled kernel comparison -/

/-- **Item 4.**  The localization kernel comparison `eq:localization` (§2):
for a smooth field supported in an admissible ball,
`I_𝕋(periodize f) ≤ I_ℝ(f) + 4·tailGeomConst s c r·‖f‖₂²`. -/
theorem iTorus_periodize_le {s : ℝ} {c : Space} {r : ℝ} {f : SpatialField}
    (hs : 0 < s) (hs1 : s < 1) (hr : 0 < r)
    (hball : closure (Metric.ball c r) ⊆ interior fundamentalCube)
    (hf : ContDiff ℝ ∞ f) (hsupp : SupportedInBall c r f) :
    ITorus s (periodize f)
      ≤ IReal s f + 4 * tailGeomConst s c r * (eLpNorm f 2 volume) ^ 2 := by
  have hfc : Continuous f := hf.continuous
  -- Rewrite the torus integral by `periodize f = f` on the cube.
  have hEq : ITorus s (periodize f) =
      ∫⁻ x in fundamentalCube, ∫⁻ y in fundamentalCube,
        ENNReal.ofReal (‖f x - f y‖ ^ 2) * periodicKernel s (x - y) := by
    rw [ITorus]
    refine setLIntegral_congr_fun measurableSet_fundamentalCube (fun x hx => ?_)
    refine setLIntegral_congr_fun measurableSet_fundamentalCube (fun y hy => ?_)
    rw [periodize_eq_of_mem_cube hball hsupp hx, periodize_eq_of_mem_cube hball hsupp hy]
  -- Inner kernel split.
  have hSplit : ∀ x : Space,
      (∫⁻ y in fundamentalCube, ENNReal.ofReal (‖f x - f y‖ ^ 2) * periodicKernel s (x - y))
        = (∫⁻ y in fundamentalCube,
            ENNReal.ofReal (‖f x - f y‖ ^ 2) * fractionalRadialKernel s (x - y))
          + (∫⁻ y in fundamentalCube,
              ENNReal.ofReal (‖f x - f y‖ ^ 2) * latticeTail s (x - y)) := by
    intro x
    have hP : Measurable (fun y : Space =>
        ENNReal.ofReal (‖f x - f y‖ ^ 2) * fractionalRadialKernel s (x - y)) := by
      refine Measurable.mul ?_ ((measurable_fractionalRadialKernel s).comp
        (measurable_const.sub measurable_id))
      exact ENNReal.measurable_ofReal.comp ((continuous_const.sub hfc).norm.pow 2).measurable
    rw [← lintegral_add_left hP]
    refine setLIntegral_congr_fun measurableSet_fundamentalCube (fun y _ => ?_)
    rw [periodicKernel_split, mul_add]
  -- Pointwise domination of the norm difference.
  have hnorm_sub_bound : ∀ x y : Space,
      ENNReal.ofReal (‖f x - f y‖ ^ 2)
        ≤ 2 * ENNReal.ofReal (‖f x‖ ^ 2) + 2 * ENNReal.ofReal (‖f y‖ ^ 2) := by
    intro x y
    have hreal : ‖f x - f y‖ ^ 2 ≤ 2 * ‖f x‖ ^ 2 + 2 * ‖f y‖ ^ 2 := by
      nlinarith [norm_sub_le (f x) (f y), sq_nonneg (‖f x‖ - ‖f y‖),
        norm_nonneg (f x), norm_nonneg (f y), norm_nonneg (f x - f y)]
    calc ENNReal.ofReal (‖f x - f y‖ ^ 2)
        ≤ ENNReal.ofReal (2 * ‖f x‖ ^ 2 + 2 * ‖f y‖ ^ 2) := ENNReal.ofReal_le_ofReal hreal
      _ = 2 * ENNReal.ofReal (‖f x‖ ^ 2) + 2 * ENNReal.ofReal (‖f y‖ ^ 2) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
          norm_num
  -- The two tail bounds (via the geometric constant), on `x∈B̄` and by symmetry on `y∈B̄`.
  have hpt1 : ∀ x y : Space, y ∈ fundamentalCube →
      ENNReal.ofReal (‖f x‖ ^ 2) * latticeTail s (x - y)
        ≤ ENNReal.ofReal (‖f x‖ ^ 2) * tailGeomConst s c r := by
    intro x y hy
    rcases eq_or_ne (f x) 0 with hfx | hfx
    · simp [hfx]
    · have hxball : x ∈ closure (Metric.ball c r) :=
        subset_closure (hsupp (subset_tsupport f (Function.mem_support.mpr hfx)))
      exact mul_le_mul_right (latticeTail_le_tailGeomConst hs.le hr hball x hxball y hy) _
  have hpt2 : ∀ y x : Space, x ∈ fundamentalCube →
      ENNReal.ofReal (‖f y‖ ^ 2) * latticeTail s (x - y)
        ≤ ENNReal.ofReal (‖f y‖ ^ 2) * tailGeomConst s c r := by
    intro y x hx
    rcases eq_or_ne (f y) 0 with hfy | hfy
    · simp [hfy]
    · have hyball : y ∈ closure (Metric.ball c r) :=
        subset_closure (hsupp (subset_tsupport f (Function.mem_support.mpr hfy)))
      have heven : latticeTail s (x - y) = latticeTail s (y - x) := by
        rw [show x - y = -(y - x) by abel, latticeTail_neg]
      rw [heven]
      exact mul_le_mul_right (latticeTail_le_tailGeomConst hs.le hr hball y hyball x hx) _
  -- Pointwise bound for the tail integrand on `Q × Q`.
  have hpoint : ∀ x ∈ fundamentalCube, ∀ y ∈ fundamentalCube,
      ENNReal.ofReal (‖f x - f y‖ ^ 2) * latticeTail s (x - y)
        ≤ 2 * tailGeomConst s c r * ENNReal.ofReal (‖f x‖ ^ 2)
          + 2 * tailGeomConst s c r * ENNReal.ofReal (‖f y‖ ^ 2) := by
    intro x hx y hy
    calc ENNReal.ofReal (‖f x - f y‖ ^ 2) * latticeTail s (x - y)
        ≤ (2 * ENNReal.ofReal (‖f x‖ ^ 2) + 2 * ENNReal.ofReal (‖f y‖ ^ 2))
            * latticeTail s (x - y) := mul_le_mul_left (hnorm_sub_bound x y) _
      _ = 2 * (ENNReal.ofReal (‖f x‖ ^ 2) * latticeTail s (x - y))
          + 2 * (ENNReal.ofReal (‖f y‖ ^ 2) * latticeTail s (x - y)) := by ring
      _ ≤ 2 * (ENNReal.ofReal (‖f x‖ ^ 2) * tailGeomConst s c r)
          + 2 * (ENNReal.ofReal (‖f y‖ ^ 2) * tailGeomConst s c r) :=
          add_le_add (mul_le_mul_right (hpt1 x y hy) 2) (mul_le_mul_right (hpt2 y x hx) 2)
      _ = 2 * tailGeomConst s c r * ENNReal.ofReal (‖f x‖ ^ 2)
          + 2 * tailGeomConst s c r * ENNReal.ofReal (‖f y‖ ^ 2) := by ring
  -- The `∫⁻ ‖f‖²` majorant.
  have hN : Measurable (fun x : Space => ENNReal.ofReal (‖f x‖ ^ 2)) :=
    ENNReal.measurable_ofReal.comp (hfc.norm.pow 2).measurable
  have hNle : (∫⁻ x in fundamentalCube, ENNReal.ofReal (‖f x‖ ^ 2)) ≤ (eLpNorm f 2 volume) ^ 2 := by
    rw [sq_eLpNorm_two]
    exact setLIntegral_le_lintegral fundamentalCube _
  -- The tail estimate.
  have hTail : (∫⁻ x in fundamentalCube, ∫⁻ y in fundamentalCube,
      ENNReal.ofReal (‖f x - f y‖ ^ 2) * latticeTail s (x - y))
      ≤ 4 * tailGeomConst s c r * (eLpNorm f 2 volume) ^ 2 := by
    have hstep : (∫⁻ x in fundamentalCube, ∫⁻ y in fundamentalCube,
        ENNReal.ofReal (‖f x - f y‖ ^ 2) * latticeTail s (x - y))
        ≤ ∫⁻ x in fundamentalCube, ∫⁻ y in fundamentalCube,
          (2 * tailGeomConst s c r * ENNReal.ofReal (‖f x‖ ^ 2)
            + 2 * tailGeomConst s c r * ENNReal.ofReal (‖f y‖ ^ 2)) := by
      refine setLIntegral_mono' measurableSet_fundamentalCube (fun x hx => ?_)
      exact setLIntegral_mono' measurableSet_fundamentalCube (fun y hy => hpoint x hx y hy)
    refine hstep.trans ?_
    have hInner : ∀ x : Space, (∫⁻ y in fundamentalCube,
        (2 * tailGeomConst s c r * ENNReal.ofReal (‖f x‖ ^ 2)
          + 2 * tailGeomConst s c r * ENNReal.ofReal (‖f y‖ ^ 2)))
        = 2 * tailGeomConst s c r * ENNReal.ofReal (‖f x‖ ^ 2)
          + 2 * tailGeomConst s c r * ∫⁻ y in fundamentalCube, ENNReal.ofReal (‖f y‖ ^ 2) := by
      intro x
      rw [lintegral_add_left measurable_const, setLIntegral_const, volume_fundamentalCube,
        mul_one, lintegral_const_mul (2 * tailGeomConst s c r) hN]
    rw [lintegral_congr hInner, lintegral_add_left (hN.const_mul (2 * tailGeomConst s c r)),
      lintegral_const_mul (2 * tailGeomConst s c r) hN, setLIntegral_const,
      volume_fundamentalCube, mul_one]
    refine le_trans (add_le_add (mul_le_mul_right hNle _) (mul_le_mul_right hNle _))
      (le_of_eq ?_)
    ring
  -- Assemble.
  calc ITorus s (periodize f)
      = ∫⁻ x in fundamentalCube, ∫⁻ y in fundamentalCube,
          ENNReal.ofReal (‖f x - f y‖ ^ 2) * periodicKernel s (x - y) := hEq
    _ = ∫⁻ x in fundamentalCube,
          ((∫⁻ y in fundamentalCube,
              ENNReal.ofReal (‖f x - f y‖ ^ 2) * fractionalRadialKernel s (x - y))
            + (∫⁻ y in fundamentalCube,
                ENNReal.ofReal (‖f x - f y‖ ^ 2) * latticeTail s (x - y))) :=
        lintegral_congr hSplit
    _ = (∫⁻ x in fundamentalCube, ∫⁻ y in fundamentalCube,
            ENNReal.ofReal (‖f x - f y‖ ^ 2) * fractionalRadialKernel s (x - y))
          + (∫⁻ x in fundamentalCube, ∫⁻ y in fundamentalCube,
              ENNReal.ofReal (‖f x - f y‖ ^ 2) * latticeTail s (x - y)) :=
        lintegral_add_left (measurable_inner_frac hfc) _
    _ ≤ IReal s f + 4 * tailGeomConst s c r * (eLpNorm f 2 volume) ^ 2 :=
        add_le_add (iTorus_singular_le hfc) hTail

end NSFormalization.Section3.T13
