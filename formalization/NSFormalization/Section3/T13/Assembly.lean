import NSFormalization.Section3.T13.ConstantEndpoints
import NSFormalization.Section3.T13.TorusIdentity
import NSFormalization.Section3.T13.WholeSpaceIdentity
import NSFormalization.Section3.T13.KernelComparison
import NSFormalization.Section3.T13.LocalizationKernel
import NSFormalization.Section3.T15.ParsevalZero
import NSFormalization.Section3.T12.MeanZeroCalculus
import NSFormalization.Section4.D01.HomogeneousNorm
import NavierStokes.PeriodicLocalization

/-!
# T13 assembly: the `localization` estimate and the full `LocalizationAPI`

This module combines the six already-proved pieces of `lem:localization`
(`paper/sections/03-torus.tex:22-98`) into the fractional-order estimate
`eq:localization` and the reconciled six-field record `LocalizationAPI`
(`research/T13/probes/api_on_canonical.lean`).

The proved inputs, all in the canonical `NSFormalization.Section3.T13`
vocabulary, are:

* `constant_pos_finite`, `endpoint_zero`, `endpoint_one` (lane 344,
  `ConstantEndpoints`);
* `wholeSpace_identity` (lanes 345/348, `WholeSpaceIdentity`):
  `IReal s f = cFrac s * dotHomogeneousENorm s f ^ 2`;
* `torus_identity` (lane 345, `TorusIdentity`):
  `ITorus s f = cFrac s * periodicHomogeneousENorm s (meanZeroPartT f) ^ 2`;
* `periodicSobolevENorm_le_l2_add_homogeneous` (lane 353, `LocalizationKernel`):
  `‖·‖_{H^s} ≤ ‖·‖_{H^0} + ‖(·)₀‖_{Ḣ^s}`;
* `iTorus_periodize_le` (lane 354, `KernelComparison`):
  `ITorus s (periodize f) ≤ IReal s f + 4·tailGeomConst s c r·‖f‖₂²`;
* `periodicSobolevENorm_zero_eq` (lane 363, `Section3/T15/ParsevalZero`):
  `‖·‖_{H^0} = ‖torusLift ·‖_{L²(T³)}`.

The two supporting bridges proved here are:

* smoothness and unit-periodicity of the spatial periodization
  `periodize f`, via the upstream `NavierStokes.PeriodicLocalization`
  lattice-sum lemmas applied to the time-constant lift `fun z ↦ f z.2`;
* the physical `L²` torus/cube identity
  `eLpNorm (torusLift v) 2 periodicTorusMeasure
    = eLpNorm v 2 (volume.restrict fundamentalCube)`
  (`research/T13/COMPARISON.md` item 8), through the upstream
  `NSFormalization.Paper1.integral_torusLift` Haar/cube bridge.
-/

noncomputable section

namespace NSFormalization.Section3.T13

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField)
open NSFormalization.Section4.D01 (dotHomogeneousENorm)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T12 (SmoothPeriodicT)
open scoped ContDiff ENNReal BigOperators Topology

/-! ## §1  Generic `ℝ≥0∞` helpers -/

/-- If two extended nonnegative reals have `A² ≤ B²` then `A ≤ B`; the reverse
of squaring is monotone on `ℝ≥0∞` (no finiteness needed). -/
theorem enn_le_of_sq_le {A B : ℝ≥0∞} (h : A ^ 2 ≤ B ^ 2) : A ≤ B := by
  have h2 := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ 2⁻¹)
  rwa [← ENNReal.rpow_natCast A 2, ← ENNReal.rpow_natCast B 2, ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul, show ((2 : ℕ) : ℝ) * 2⁻¹ = 1 by norm_num, ENNReal.rpow_one,
    ENNReal.rpow_one] at h2

/-- The squared order-`2` extended seminorm as a `lintegral` of `‖·‖²`, for any
measure.  This is the measure-agnostic version of
`KernelComparison.sq_eLpNorm_two`. -/
theorem eLpNorm_two_sq {α : Type*} [MeasurableSpace α] (u : α → Space) (μ : Measure α) :
    eLpNorm u 2 μ ^ 2 = ∫⁻ a, ENNReal.ofReal (‖u a‖ ^ 2) ∂μ := by
  have hpt : (fun a => ‖u a‖ₑ ^ (2 : ℝ)) = fun a => ENNReal.ofReal (‖u a‖ ^ 2) := by
    funext a
    rw [← ofReal_norm (u a),
      ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num), eLpNorm',
    show ((2 : ℝ≥0∞).toReal) = (2 : ℝ) by norm_num, hpt,
    ← ENNReal.rpow_natCast ((∫⁻ a, ENNReal.ofReal (‖u a‖ ^ 2) ∂μ) ^ (1 / (2 : ℝ))) 2,
    ← ENNReal.rpow_mul, show (1 / (2 : ℝ)) * ((2 : ℕ) : ℝ) = 1 by norm_num, ENNReal.rpow_one]

/-! ## §2  Smoothness and unit-periodicity of `periodize f` -/

/-- The T13 embedded lattice vector coincides with the upstream one. -/
theorem latticeVector_eq_lattice (n : PeriodicFrequency) :
    latticeVector n = NavierStokes.PeriodicLocalization.lattice n := by
  ext i
  rw [latticeVector_apply, NavierStokes.PeriodicLocalization.lattice_apply]

/-- The spatial periodization is the time slice of the upstream spacetime
periodization of the time-constant lift `fun z ↦ f z.2`. -/
theorem periodize_eq_vendor (f : SpatialField) (x : Space) :
    periodize f x
      = NavierStokes.PeriodicLocalization.periodize (fun z : SpaceTime => f z.2) (0, x) := by
  unfold NSFormalization.Section3.T13.periodize NavierStokes.PeriodicLocalization.periodize
  refine tsum_congr (fun n => ?_)
  rw [latticeVector_eq_lattice n]
  rfl

/-- `periodize f` is smooth whenever `f` is smooth and supported in an
admissible ball, through the upstream locally finite lattice sum. -/
theorem contDiff_periodize_supported {c : Space} {r : ℝ} {f : SpatialField}
    (hball : closure (Metric.ball c r) ⊆ interior fundamentalCube)
    (hsupp : SupportedInBall c r f) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (periodize f) := by
  set F : SpaceTime → Space := fun z => f z.2 with hF
  have hFsm : ContDiff ℝ ∞ F := hf.comp contDiff_snd
  have hFsupp : NavierStokes.PeriodicLocalization.SupportedInCube 1 F := by
    intro z hz i
    have hz2 : f z.2 ≠ 0 := hz
    have hmem : z.2 ∈ fundamentalCube :=
      tsupport_subset_cube hball hsupp (subset_tsupport f hz2)
    have hcoord := hmem i
    rw [abs_le]
    exact ⟨by linarith [hcoord.1], hcoord.2⟩
  have hper : ContDiff ℝ ∞ (NavierStokes.PeriodicLocalization.periodize F) :=
    NavierStokes.PeriodicLocalization.contDiff_periodize hFsupp hFsm
  have hcomp : ContDiff ℝ ∞
      (fun x : Space => NavierStokes.PeriodicLocalization.periodize F (0, x)) :=
    hper.comp (contDiff_const.prodMk contDiff_id)
  have heq : periodize f =
      fun x : Space => NavierStokes.PeriodicLocalization.periodize F (0, x) :=
    funext (fun x => periodize_eq_vendor f x)
  rw [heq]; exact hcomp

/-- `periodize f` is unit-periodic in space, unconditionally, through the
upstream lattice reindexing. -/
theorem isPeriodicSpatial_periodize (f : SpatialField) : IsPeriodicSpatial (periodize f) := by
  intro x i
  rw [periodize_eq_vendor f (x + coordinateVector i), periodize_eq_vendor f x]
  exact NavierStokes.PeriodicLocalization.unitSpatialPeriodsOn_periodize
    (fun z : SpaceTime => f z.2) univ 0 (mem_univ 0) x i

/-! ## §3  The physical `L²` torus/cube identity (COMPARISON item 8) -/

/-- `∫_{T³} ‖torusLift v‖² dHaar = ∫_{[0,1]³} ‖v‖² dx` for continuous `v`,
through the upstream Haar/cube integral bridge. -/
theorem lintegral_torusLift_normSq {v : SpatialField} (hv : Continuous v) :
    ∫⁻ z, ENNReal.ofReal (‖torusLift v z‖ ^ 2) ∂periodicTorusMeasure
      = ∫⁻ x in fundamentalCube, ENNReal.ofReal (‖v x‖ ^ 2) ∂(volume : Measure Space) := by
  have hcont : Continuous fun x : Space => ‖v x‖ ^ 2 := hv.norm.pow 2
  have hpos : ∀ x : Space, 0 ≤ ‖v x‖ ^ 2 := fun x => sq_nonneg _
  have hInt : Integrable (fun z : PeriodicTorus => ‖torusLift v z‖ ^ 2) periodicTorusMeasure :=
    MemLp.integrable_norm_pow (p := 2) (by simpa using memLp_torusLift_space hv 2) (by norm_num)
  rw [lintegral_fundamentalCube_ofReal hcont hpos,
    ← ofReal_integral_eq_lintegral_ofReal hInt (Filter.Eventually.of_forall (fun z => sq_nonneg _))]
  congr 1
  rw [← NSFormalization.Paper1.integral_torusLift (fun x => ‖v x‖ ^ 2)]
  rfl

/-- COMPARISON item 8: the physical `L²(T³)` torus norm of `torusLift v` equals
the physical `L²` norm of `v` over the fundamental cube. -/
theorem torus_cube_L2 {v : SpatialField} (hv : Continuous v) :
    eLpNorm (torusLift v) 2 periodicTorusMeasure
      = eLpNorm v 2 (volume.restrict fundamentalCube) := by
  have hsq : eLpNorm (torusLift v) 2 periodicTorusMeasure ^ 2
      = eLpNorm v 2 (volume.restrict fundamentalCube) ^ 2 := by
    rw [eLpNorm_two_sq, eLpNorm_two_sq]
    exact lintegral_torusLift_normSq hv
  exact le_antisymm (enn_le_of_sq_le hsq.le) (enn_le_of_sq_le hsq.ge)

/-! ## §4  The homogeneous half of `eq:localization` -/

/-- The `Ḣ^s`-norm of the mean-free part of `periodize f` is controlled by the
whole-space homogeneous norm plus the `L²` tail term, after dividing the kernel
comparison by `c_s` and taking a square root. -/
theorem homogeneous_bound {s : ℝ} {c : Space} {r : ℝ} {f : SpatialField}
    (hs0 : 0 < s) (hs1 : s < 1) (hr : 0 < r)
    (hball : closure (Metric.ball c r) ⊆ interior fundamentalCube)
    (hf : ContDiff ℝ ∞ f) (hsupp : SupportedInBall c r f) :
    periodicHomogeneousENorm s (meanZeroPartT (periodize f))
      ≤ dotHomogeneousENorm s f
        + (4 * tailGeomConst s c r / cFrac s) ^ (2⁻¹ : ℝ) * eLpNorm f 2 volume := by
  have hfsm : ContDiff ℝ ∞ (periodize f) := contDiff_periodize_supported hball hsupp hf
  have hfper : IsPeriodicSpatial (periodize f) := isPeriodicSpatial_periodize f
  have hcs : HasCompactSupport f :=
    IsCompact.of_isClosed_subset (isCompact_closedBall c r) isClosed_closure
      (hsupp.trans Metric.ball_subset_closedBall)
  have hTor := (torus_identity hs0 hs1 hfsm hfper).2
  have hWho := (wholeSpace_identity s hs0 hs1 f hf hcs).2
  have hKer := iTorus_periodize_le hs0 hs1 hr hball hf hsupp
  set C0 := cFrac s with hC0
  set a := dotHomogeneousENorm s f with ha
  set b := eLpNorm f 2 volume with hb
  set x := periodicHomogeneousENorm s (meanZeroPartT (periodize f)) with hx
  set Tg := tailGeomConst s c r with hTg
  have hC0pos : 0 < C0 := (constant_pos_finite s hs0 hs1).1
  have hC0top : C0 < ⊤ := (constant_pos_finite s hs0 hs1).2
  have hC0ne0 : C0 ≠ 0 := hC0pos.ne'
  have hC0netop : C0 ≠ ⊤ := hC0top.ne
  -- The kernel comparison in the form `C0·x² ≤ C0·a² + 4·Tg·b²`.
  have hchain : C0 * x ^ 2 ≤ C0 * a ^ 2 + 4 * Tg * b ^ 2 := by
    calc C0 * x ^ 2 = ITorus s (periodize f) := hTor.symm
      _ ≤ IReal s f + 4 * Tg * b ^ 2 := hKer
      _ = C0 * a ^ 2 + 4 * Tg * b ^ 2 := by rw [hWho]
  -- The chosen square-root constant.
  set sK := (4 * Tg / C0) ^ (2⁻¹ : ℝ) with hsK
  have hsKsq : C0 * sK ^ 2 = 4 * Tg := by
    have hsq : sK ^ 2 = 4 * Tg / C0 := by
      rw [hsK, ← ENNReal.rpow_natCast ((4 * Tg / C0) ^ (2⁻¹ : ℝ)) 2, ← ENNReal.rpow_mul]
      norm_num
    rw [hsq, ENNReal.div_eq_inv_mul, ← mul_assoc, ENNReal.mul_inv_cancel hC0ne0 hC0netop, one_mul]
  -- Expand and drop the nonnegative cross term.
  have hexp : C0 * (a + sK * b) ^ 2
      = (C0 * a ^ 2 + 4 * Tg * b ^ 2) + 2 * (C0 * (a * (sK * b))) := by
    have hraw : C0 * (a + sK * b) ^ 2
        = C0 * a ^ 2 + C0 * sK ^ 2 * b ^ 2 + 2 * (C0 * (a * (sK * b))) := by ring
    rw [hraw, hsKsq]
  have hCbig : C0 * x ^ 2 ≤ C0 * (a + sK * b) ^ 2 := by
    rw [hexp]; exact le_trans hchain le_self_add
  -- Cancel `C0` and conclude by monotone square root.
  have hcancel : ∀ u : ℝ≥0∞, C0⁻¹ * (C0 * u) = u := fun u => by
    rw [← mul_assoc, ENNReal.inv_mul_cancel hC0ne0 hC0netop, one_mul]
  have hxsq : x ^ 2 ≤ (a + sK * b) ^ 2 := by
    have h : C0⁻¹ * (C0 * x ^ 2) ≤ C0⁻¹ * (C0 * (a + sK * b) ^ 2) := by gcongr
    rwa [hcancel, hcancel] at h
  exact enn_le_of_sq_le hxsq

/-! ## §5  The `localization` field (`eq:localization`) -/

/-- `LocalizationAPI.localization`, `03-torus.tex:22-28,73-96`, `eq:localization`.
For every admissible ball there is one positive finite real constant controlling
the periodic `H^s` norm of every zero extension supported in it, in terms of the
whole-space `L²` and homogeneous norms. -/
theorem localization :
    ∀ (s : ℝ), 0 < s → s < 1 → ∀ (c : Space) (r : ℝ),
      0 < r → closure (Metric.ball c r) ⊆ interior fundamentalCube →
        ∃ C : ℝ, 0 < C ∧ ∀ f : SpatialField,
          (ContDiff ℝ ∞ f ∧ SupportedInBall c r f) →
            periodicSobolevENorm s (periodize f) ≤
              ENNReal.ofReal C * (eLpNorm f 2 volume + dotHomogeneousENorm s f) := by
  intro s hs0 hs1 c r hr hball
  have hTgtop : tailGeomConst s c r < ⊤ := tailGeomConst_lt_top hs0 hr hball
  have hC0pos : 0 < cFrac s := (constant_pos_finite s hs0 hs1).1
  have hKtop : 4 * tailGeomConst s c r / cFrac s ≠ ⊤ := by
    rw [ENNReal.div_eq_inv_mul]
    exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hC0pos.ne')
      (ENNReal.mul_ne_top (by norm_num) hTgtop.ne)
  set sK := (4 * tailGeomConst s c r / cFrac s) ^ (2⁻¹ : ℝ) with hsKdef
  have hsKtop : sK ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hKtop
  have h1sKtop : (1 : ℝ≥0∞) + sK ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, hsKtop⟩
  refine ⟨(1 + sK).toReal, ?_, ?_⟩
  · exact ENNReal.toReal_pos (lt_of_lt_of_le one_pos le_self_add).ne' h1sKtop
  · rintro f ⟨hf, hsupp⟩
    have hfsm : ContDiff ℝ ∞ (periodize f) := contDiff_periodize_supported hball hsupp hf
    have hfper : IsPeriodicSpatial (periodize f) := isPeriodicSpatial_periodize f
    have hroute := periodicSobolevENorm_le_l2_add_homogeneous hs0 hs1.le hfsm hfper
    have hLeq : periodicSobolevENorm 0 (periodize f) = eLpNorm f 2 volume := by
      rw [NSFormalization.Section3.T15.periodicSobolevENorm_zero_eq (periodize f) ⟨hfsm, hfper⟩,
        torus_cube_L2 hfsm.continuous, endpoint_zero_eq hball hsupp]
    have hHom := homogeneous_bound hs0 hs1 hr hball hf hsupp
    rw [← hsKdef] at hHom
    calc periodicSobolevENorm s (periodize f)
        ≤ periodicSobolevENorm 0 (periodize f)
            + periodicHomogeneousENorm s (meanZeroPartT (periodize f)) := hroute
      _ = eLpNorm f 2 volume
            + periodicHomogeneousENorm s (meanZeroPartT (periodize f)) := by rw [hLeq]
      _ ≤ eLpNorm f 2 volume + (dotHomogeneousENorm s f + sK * eLpNorm f 2 volume) := by
            gcongr
      _ ≤ ENNReal.ofReal ((1 + sK).toReal)
            * (eLpNorm f 2 volume + dotHomogeneousENorm s f) := by
            rw [ENNReal.ofReal_toReal h1sKtop]
            have hexpand : (1 + sK) * (eLpNorm f 2 volume + dotHomogeneousENorm s f)
                = eLpNorm f 2 volume + (dotHomogeneousENorm s f + sK * eLpNorm f 2 volume)
                  + sK * dotHomogeneousENorm s f := by ring
            rw [hexpand]
            exact le_self_add

/-! ## §6  The reconciled six-field API record -/

/-- Statement-only API for `lem:localization` and the Fourier/Gagliardo
identifications used by its proof (`03-torus.tex:22-98`).  The range is always
`0 < s < 1`; the two endpoints are stated separately.  Copied token-for-token
from `research/T13/probes/api_on_canonical.lean` / `research/T13/Spec.lean`. -/
structure LocalizationAPI : Prop where
  /-- `03-torus.tex:35-39`: the defined constant `c_s` is strictly positive
  and finite for `0 < s < 1`. -/
  constant_pos_finite :
    ∀ (s : ℝ), 0 < s → s < 1 → 0 < cFrac s ∧ cFrac s < ⊤
  /-- `03-torus.tex:40-51`: the whole-space Gagliardo integral of every smooth
  compactly supported real vector field equals `c_s` times the square of the
  registered `dotHomogeneousENorm`. -/
  wholeSpace_identity :
    ∀ (s : ℝ), 0 < s → s < 1 → ∀ f : SpatialField,
      ContDiff ℝ ∞ f → HasCompactSupport f →
        IReal s f < ⊤ ∧
          IReal s f = cFrac s * dotHomogeneousENorm s f ^ (2 : ℕ)
  /-- `03-torus.tex:53-72`: the periodic Gagliardo integral of every smooth
  periodic vector field equals the same `c_s` times T10's homogeneous norm of
  its explicitly mean-zero part. -/
  torus_identity :
    ∀ (s : ℝ), 0 < s → s < 1 → ∀ f : SpatialField,
      ContDiff ℝ ∞ f → IsPeriodicSpatial f →
        ITorus s f < ⊤ ∧
          ITorus s f = cFrac s *
            periodicHomogeneousENorm s (meanZeroPartT f) ^ (2 : ℕ)
  /-- `03-torus.tex:22-28,73-96`, equation `eq:localization`: for every fixed
  positive-radius ball strictly inside the fixed cube, one positive finite real
  constant is chosen before every smooth zero extension supported in that ball. -/
  localization :
    ∀ (s : ℝ), 0 < s → s < 1 → ∀ (c : Space) (r : ℝ),
      0 < r → closure (Metric.ball c r) ⊆ interior fundamentalCube →
        ∃ C : ℝ, 0 < C ∧ ∀ f : SpatialField,
          (ContDiff ℝ ∞ f ∧ SupportedInBall c r f) →
            periodicSobolevENorm s (periodize f) ≤
              ENNReal.ofReal C * (eLpNorm f 2 volume + dotHomogeneousENorm s f)
  /-- `03-torus.tex:29,96-98`: at `s=0`, integration over the single copy of
  the support gives equality of the physical `L²` norms. -/
  endpoint_zero :
    ∀ (c : Space) (r : ℝ),
      0 < r → closure (Metric.ball c r) ⊆ interior fundamentalCube →
        ∀ f : SpatialField, (ContDiff ℝ ∞ f ∧ SupportedInBall c r f) →
          eLpNorm (periodize f) 2 (volume.restrict fundamentalCube) =
            eLpNorm f 2 volume
  /-- `03-torus.tex:29,96-98`: at `s=1`, integration over the single copy of
  the support gives equality of the corresponding physical `L²` gradient
  norms, without identifying them with the full inhomogeneous `H¹` norm. -/
  endpoint_one :
    ∀ (c : Space) (r : ℝ),
      0 < r → closure (Metric.ball c r) ⊆ interior fundamentalCube →
        ∀ f : SpatialField, (ContDiff ℝ ∞ f ∧ SupportedInBall c r f) →
          gradientENorm (periodize f) (volume.restrict fundamentalCube) =
            gradientENorm f volume

/-- The reconciled `LocalizationAPI` record, assembled from all six proved
fields. -/
theorem localizationAPI : LocalizationAPI :=
  ⟨constant_pos_finite,
    wholeSpace_identity,
    fun _s hs0 hs1 _f hfs hfp => torus_identity hs0 hs1 hfs hfp,
    localization,
    endpoint_zero,
    endpoint_one⟩

end NSFormalization.Section3.T13
