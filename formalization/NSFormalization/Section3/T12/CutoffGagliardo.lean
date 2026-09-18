import NSFormalization.Section3.T12.Cutoff
import NSFormalization.Section3.T12.MeanZeroCalculus
import NSFormalization.Section3.T13.WholeSpaceIdentity
import NSFormalization.Section3.T13.KernelComparison
import NSFormalization.Section3.T15.HaarBridge

/-!
# T12 U3: the cutoff–Gagliardo comparison at `a = 1/2`

For a smooth mean-zero periodic vector field `v`, the whole-space homogeneous
`Ḣ^{1/2}(ℝ³)` norm of the localization `χ·v` is controlled by the physical
`L²(Q)` norm of `v` plus the torus homogeneous `Ḣ^{1/2}(T³)` norm of `v`
(`03-torus.tex`, `appendix-b-embeddings.tex`; `research/T12/T12_SPLIT.md` U3).

## Reduction backbone (this file)

The manuscript route reduces the target to two localization kernel bounds via
the two proved T13 Gagliardo identities:

* `wholeSpace_identity` at `s = 1/2` turns `IReal (1/2) (χv)` into
  `cFrac (1/2) · dotHomogeneousENorm (1/2) (χv) ^ 2` (`ireal_cutoffMul_eq`;
  needs `χv` smooth with compact support, from `Cutoff.lean`);
* `torus_identity_smooth` at `s = 1/2` turns `ITorus (1/2) v` into
  `cFrac (1/2) · periodicHomogeneousENorm (1/2) v ^ 2` after
  `meanZeroPartT v = v` for mean-zero `v` (`itorus_meanZero_eq`);
* the difference split `χ(x+h)v(x+h) − χ(x)v(x)
  = χ(x+h)(v(x+h)−v(x)) + (χ(x+h)−χ(x))v(x)` gives
  `IReal (1/2) (χv) ≤ 2·IA v + 2·IB v` (`ireal_cutoffMul_le_split`), where
  `IA` is the Gagliardo integral of the first (mean-difference) piece and
  `IB` that of the second (cutoff-commutator) piece;
* dividing by `0 < cFrac (1/2) < ⊤` and the monotone `ℝ≥0∞` square root
  (`enn_sqrt_div_bound`) turn bounds on `IA`, `IB` into the target bound on
  `dotHomogeneousENorm (1/2) (χv)` (`dotHomogeneousENorm_cutoffMul_le`).

The two remaining analytic inputs are the reverse-localization bounds
`IA v ≤ C · ITorus (1/2) v` (first piece, kernel comparison
`fractionalRadialKernel ≤ periodicKernel` plus lattice tiling of the whole
`x`-integral back to the fundamental cube) and
`IB v ≤ C · ‖v‖²_{L²(Q)}` (second piece, Lipschitz bound on `χ` and
integrability of `min(L²‖h‖²,1)‖h‖^{-4}` on `ℝ³`); see
`research/T12/ATTEMPTS_U3.md`.
-/

noncomputable section

namespace NSFormalization.Section3.T12

open Set MeasureTheory Metric
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Section3.T13
open NSFormalization.Section4.A02 (SpatialField)
open NSFormalization.Section4.D01 (dotHomogeneousENorm)
open scoped ContDiff ENNReal BigOperators Topology

/-! ## §1  Mean-zero fields are their own mean-free parts -/

/-- For a mean-zero periodic field the mean-free projection is the identity. -/
theorem meanZeroPartT_eq_self {v : SpatialField} (hm : IsMeanZeroT v) :
    meanZeroPartT v = v := by
  funext x
  show v x - meanT v = v x
  rw [show meanT v = 0 from hm, sub_zero]

/-! ## §2  The paper constant `cFrac (1/2)` is positive and finite -/

/-- `0 < cFrac (1/2)`. -/
theorem cFrac_half_pos : 0 < cFrac (1 / 2) :=
  (constant_pos_finite (1 / 2) (by norm_num) (by norm_num)).1

/-- `cFrac (1/2) < ⊤`. -/
theorem cFrac_half_lt_top : cFrac (1 / 2) < ⊤ :=
  (constant_pos_finite (1 / 2) (by norm_num) (by norm_num)).2

/-- `cFrac (1/2) ≠ 0`. -/
theorem cFrac_half_ne_zero : cFrac (1 / 2) ≠ 0 := cFrac_half_pos.ne'

/-- `cFrac (1/2) ≠ ⊤`. -/
theorem cFrac_half_ne_top : cFrac (1 / 2) ≠ ⊤ := cFrac_half_lt_top.ne

/-! ## §3  The two Gagliardo identities specialised to `s = 1/2` -/

/-- Whole-space Gagliardo identity for the cutoff localization at `s = 1/2`. -/
theorem ireal_cutoffMul_eq {v : SpatialField} (hv : SmoothPeriodicT v) :
    IReal (1 / 2) (cutoffMul v)
      = cFrac (1 / 2) * dotHomogeneousENorm (1 / 2) (cutoffMul v) ^ (2 : ℕ) :=
  (wholeSpace_identity (1 / 2) (by norm_num) (by norm_num) (cutoffMul v)
    (contDiff_cutoffMul hv.1) (hasCompactSupport_cutoffMul v)).2

/-- Torus Gagliardo identity for a mean-zero smooth periodic field at
`s = 1/2`. -/
theorem itorus_meanZero_eq {v : SpatialField} (hv : SmoothPeriodicT v)
    (hm : IsMeanZeroT v) :
    ITorus (1 / 2) v
      = cFrac (1 / 2) * periodicHomogeneousENorm (1 / 2) v ^ (2 : ℕ) := by
  rw [torus_identity_smooth (by norm_num) hv.1 hv.2, meanZeroPartT_eq_self hm]

/-! ## §4  The `ℝ≥0∞` square-root / division step

From `c·D² ≤ c1·(c·P²) + c2·L²` with `0 < c < ⊤` we divide by `c` and take
the monotone `ℝ≥0∞` square root, absorbing the `L²` remainder into the
constant. -/

/-- Divide by `c > 0` and take the square root: the algebraic core of the
reduction, over abstract nonnegative quantities. -/
theorem enn_sqrt_div_bound {c D P L : ℝ≥0∞} {c1 c2 : ℝ}
    (hc0 : c ≠ 0) (hct : c ≠ ⊤) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2)
    (hb : c * D ^ 2 ≤ ENNReal.ofReal c1 * (c * P ^ 2) + ENNReal.ofReal c2 * L ^ 2) :
    D ≤ ENNReal.ofReal (max (Real.sqrt c1) (Real.sqrt (c2 * c.toReal⁻¹))) * (L + P) := by
  set M : ℝ := max (Real.sqrt c1) (Real.sqrt (c2 * c.toReal⁻¹)) with hM
  have hcpos : 0 < c.toReal := by
    rw [ENNReal.toReal_pos_iff]
    exact ⟨lt_of_le_of_ne bot_le (Ne.symm hc0), lt_top_iff_ne_top.mpr hct⟩
  have hrw : ENNReal.ofReal c1 * (c * P ^ 2) = c * (ENNReal.ofReal c1 * P ^ 2) := by ring
  rw [hrw] at hb
  have hcinv : c⁻¹ * c = 1 := ENNReal.inv_mul_cancel hc0 hct
  have hb2 : D ^ 2 ≤ ENNReal.ofReal c1 * P ^ 2
      + (c⁻¹ * ENNReal.ofReal c2) * L ^ 2 := by
    have hmul := mul_le_mul_right hb c⁻¹
    calc D ^ 2 = c⁻¹ * (c * D ^ 2) := by rw [← mul_assoc, hcinv, one_mul]
      _ ≤ c⁻¹ * (c * (ENNReal.ofReal c1 * P ^ 2) + ENNReal.ofReal c2 * L ^ 2) := hmul
      _ = ENNReal.ofReal c1 * P ^ 2 + (c⁻¹ * ENNReal.ofReal c2) * L ^ 2 := by
              rw [mul_add, ← mul_assoc, hcinv, one_mul, ← mul_assoc]
  have hcinv_ofReal : c⁻¹ = ENNReal.ofReal (c.toReal⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos hcpos, ENNReal.ofReal_toReal hct]
  have hcoef2 : c⁻¹ * ENNReal.ofReal c2 = ENNReal.ofReal (c2 * c.toReal⁻¹) := by
    rw [hcinv_ofReal, ← ENNReal.ofReal_mul (by positivity), mul_comm]
  rw [hcoef2] at hb2
  set m : ℝ≥0∞ := ENNReal.ofReal M with hm
  have hMnn : 0 ≤ M := le_trans (Real.sqrt_nonneg _) (le_max_left _ _)
  have hsq : m ^ 2 = ENNReal.ofReal (M ^ 2) := by rw [hm, ← ENNReal.ofReal_pow hMnn]
  have hb_c1 : ENNReal.ofReal c1 ≤ m ^ 2 := by
    rw [hsq]; apply ENNReal.ofReal_le_ofReal
    have hle : Real.sqrt c1 ≤ M := le_max_left _ _
    nlinarith [Real.sq_sqrt hc1, Real.sqrt_nonneg c1, hle, hMnn]
  have hb_c2 : ENNReal.ofReal (c2 * c.toReal⁻¹) ≤ m ^ 2 := by
    rw [hsq]; apply ENNReal.ofReal_le_ofReal
    have hnn : 0 ≤ c2 * c.toReal⁻¹ := by positivity
    have hle : Real.sqrt (c2 * c.toReal⁻¹) ≤ M := le_max_right _ _
    nlinarith [Real.sq_sqrt hnn, Real.sqrt_nonneg (c2 * c.toReal⁻¹), hle, hMnn]
  have hstep : D ^ 2 ≤ (m * (L + P)) ^ 2 := by
    calc D ^ 2 ≤ ENNReal.ofReal c1 * P ^ 2 + ENNReal.ofReal (c2 * c.toReal⁻¹) * L ^ 2 := hb2
      _ ≤ m ^ 2 * P ^ 2 + m ^ 2 * L ^ 2 :=
          add_le_add (mul_le_mul_left hb_c1 _) (mul_le_mul_left hb_c2 _)
      _ = m ^ 2 * (P ^ 2 + L ^ 2) := by rw [mul_add]
      _ ≤ m ^ 2 * (L + P) ^ 2 := by
          apply mul_le_mul_right
          have hexp : (L + P) ^ 2 = L ^ 2 + P ^ 2 + 2 * (L * P) := by ring
          rw [hexp, add_comm (P ^ 2) (L ^ 2)]; exact le_add_right (le_refl _)
      _ = (m * (L + P)) ^ 2 := by rw [mul_pow]
  have h2 : D ^ (2 : ℝ) ≤ (m * (L + P)) ^ (2 : ℝ) := by
    rw [ENNReal.rpow_two, ENNReal.rpow_two]; simpa [sq] using hstep
  exact (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2)).mp h2

/-! ## §5  The difference split `IReal (1/2) (χv) ≤ 2·IA + 2·IB` -/

/-- Gagliardo integrand of the first (mean-difference) piece
`χ(x+h)(v(x+h) − v(x))`. -/
def gA (v : SpatialField) (h x : Space) : ℝ≥0∞ :=
  ENNReal.ofReal (‖cutoff (x + h) • (v (x + h) - v x)‖ ^ 2)
    * fractionalRadialKernel (1 / 2) h

/-- Gagliardo integrand of the second (cutoff-commutator) piece
`(χ(x+h) − χ(x))v(x)`. -/
def gB (v : SpatialField) (h x : Space) : ℝ≥0∞ :=
  ENNReal.ofReal (‖(cutoff (x + h) - cutoff x) • v x‖ ^ 2)
    * fractionalRadialKernel (1 / 2) h

/-- The whole-space Gagliardo integral of the first split piece. -/
def IA (v : SpatialField) : ℝ≥0∞ := ∫⁻ h : Space, ∫⁻ x : Space, gA v h x

/-- The whole-space Gagliardo integral of the second split piece. -/
def IB (v : SpatialField) : ℝ≥0∞ := ∫⁻ h : Space, ∫⁻ x : Space, gB v h x

/-- Linearity of the iterated `lintegral` over `2·f + 2·g` (abstract, so no
cutoff data is unfolded during the rewrites). -/
theorem lintegral_two_add_two (f g : Space → Space → ℝ≥0∞)
    (hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g)) :
    ∫⁻ h : Space, ∫⁻ x : Space, (2 * f h x + 2 * g h x)
      = 2 * (∫⁻ h : Space, ∫⁻ x : Space, f h x)
        + 2 * (∫⁻ h : Space, ∫⁻ x : Space, g h x) := by
  have hinner : ∀ h : Space, ∫⁻ x : Space, (2 * f h x + 2 * g h x)
      = 2 * (∫⁻ x, f h x) + 2 * (∫⁻ x, g h x) := by
    intro h
    have hfx : Measurable (fun x => f h x) := hf.comp measurable_prodMk_left
    have hgx : Measurable (fun x => g h x) := hg.comp measurable_prodMk_left
    rw [lintegral_add_left (f := fun x => 2 * f h x) (hfx.const_mul 2) (fun x => 2 * g h x),
      lintegral_const_mul 2 hfx, lintegral_const_mul 2 hgx]
  rw [lintegral_congr hinner]
  have hfh : Measurable (fun h => ∫⁻ x, f h x) := hf.lintegral_prod_right
  have hgh : Measurable (fun h => ∫⁻ x, g h x) := hg.lintegral_prod_right
  rw [lintegral_add_left (f := fun h => 2 * ∫⁻ x, f h x) (hfh.const_mul 2)
      (fun h => 2 * ∫⁻ x, g h x),
    lintegral_const_mul 2 hfh, lintegral_const_mul 2 hgh]

/-- Measurability of the first split integrand as a function on `Space × Space`. -/
theorem measurable_gA_pair {v : SpatialField} (hv : SmoothPeriodicT v) :
    Measurable (Function.uncurry (gA v)) := by
  have hc : Continuous cutoff := cutoff_contDiff.continuous
  have hvc : Continuous v := hv.1.continuous
  unfold Function.uncurry gA
  refine Measurable.mul ?_ ((measurable_fractionalRadialKernel (1 / 2)).comp measurable_fst)
  refine ENNReal.measurable_ofReal.comp ?_
  have hcm : Continuous (fun p : Space × Space =>
      cutoff (p.2 + p.1) • (v (p.2 + p.1) - v p.2)) :=
    ((hc.comp (continuous_snd.add continuous_fst)).smul
      ((hvc.comp (continuous_snd.add continuous_fst)).sub (hvc.comp continuous_snd)))
  exact (hcm.norm.pow 2).measurable

/-- Measurability of the second split integrand as a function on
`Space × Space`. -/
theorem measurable_gB_pair {v : SpatialField} (hv : SmoothPeriodicT v) :
    Measurable (Function.uncurry (gB v)) := by
  have hc : Continuous cutoff := cutoff_contDiff.continuous
  have hvc : Continuous v := hv.1.continuous
  unfold Function.uncurry gB
  refine Measurable.mul ?_ ((measurable_fractionalRadialKernel (1 / 2)).comp measurable_fst)
  refine ENNReal.measurable_ofReal.comp ?_
  have hcm : Continuous (fun p : Space × Space =>
      (cutoff (p.2 + p.1) - cutoff p.2) • v p.2) :=
    (((hc.comp (continuous_snd.add continuous_fst)).sub (hc.comp continuous_snd)).smul
      (hvc.comp continuous_snd))
  exact (hcm.norm.pow 2).measurable

/-- **The difference split.**  `IReal (1/2) (χv) ≤ 2·IA v + 2·IB v`, from the
pointwise decomposition `χ(x+h)v(x+h) − χ(x)v(x)
= χ(x+h)(v(x+h)−v(x)) + (χ(x+h)−χ(x))v(x)` and `‖a+b‖² ≤ 2‖a‖²+2‖b‖²`. -/
theorem ireal_cutoffMul_le_split {v : SpatialField} (hv : SmoothPeriodicT v) :
    IReal (1 / 2) (cutoffMul v) ≤ 2 * IA v + 2 * IB v := by
  have hpt : ∀ h x : Space,
      ENNReal.ofReal (‖cutoffMul v (x + h) - cutoffMul v x‖ ^ 2)
          * fractionalRadialKernel (1 / 2) h
        ≤ 2 * gA v h x + 2 * gB v h x := by
    intro h x
    have hsplit : cutoffMul v (x + h) - cutoffMul v x
        = cutoff (x + h) • (v (x + h) - v x) + (cutoff (x + h) - cutoff x) • v x := by
      simp only [cutoffMul]; rw [smul_sub, sub_smul]; abel
    have hnormsq : ‖cutoffMul v (x + h) - cutoffMul v x‖ ^ 2
        ≤ 2 * ‖cutoff (x + h) • (v (x + h) - v x)‖ ^ 2
          + 2 * ‖(cutoff (x + h) - cutoff x) • v x‖ ^ 2 := by
      rw [hsplit]
      nlinarith [norm_add_le (cutoff (x + h) • (v (x + h) - v x))
          ((cutoff (x + h) - cutoff x) • v x),
        sq_nonneg (‖cutoff (x + h) • (v (x + h) - v x)‖
          - ‖(cutoff (x + h) - cutoff x) • v x‖),
        norm_nonneg (cutoff (x + h) • (v (x + h) - v x)),
        norm_nonneg ((cutoff (x + h) - cutoff x) • v x),
        norm_nonneg (cutoff (x + h) • (v (x + h) - v x)
          + (cutoff (x + h) - cutoff x) • v x)]
    calc ENNReal.ofReal (‖cutoffMul v (x + h) - cutoffMul v x‖ ^ 2)
            * fractionalRadialKernel (1 / 2) h
        ≤ ENNReal.ofReal (2 * ‖cutoff (x + h) • (v (x + h) - v x)‖ ^ 2
            + 2 * ‖(cutoff (x + h) - cutoff x) • v x‖ ^ 2)
            * fractionalRadialKernel (1 / 2) h :=
          mul_le_mul_left (ENNReal.ofReal_le_ofReal hnormsq) _
      _ = 2 * gA v h x + 2 * gB v h x := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
          simp only [gA, gB]; ring
  calc IReal (1 / 2) (cutoffMul v)
      = ∫⁻ h : Space, ∫⁻ x : Space,
          ENNReal.ofReal (‖cutoffMul v (x + h) - cutoffMul v x‖ ^ 2)
            * fractionalRadialKernel (1 / 2) h := rfl
    _ ≤ ∫⁻ h : Space, ∫⁻ x : Space, (2 * gA v h x + 2 * gB v h x) :=
        lintegral_mono fun h => lintegral_mono fun x => hpt h x
    _ = 2 * IA v + 2 * IB v :=
        lintegral_two_add_two (gA v) (gB v) (measurable_gA_pair hv) (measurable_gB_pair hv)

/-! ## §6  Assembly of the target from the two localization kernel bounds

Given the two reverse-localization bounds `IA v ≤ Ca · ITorus (1/2) v` and
`IB v ≤ Cb · ‖v‖²_{L²(Q)}`, the reduction backbone above yields the U3 target
with the explicit constant
`max (√(2·Ca)) (√(2·Cb / cFrac (1/2)))`. -/

/-- **Assembly.**  The two localization kernel bounds imply the U3 target. -/
theorem dotHomogeneousENorm_cutoffMul_le {v : SpatialField} (hv : SmoothPeriodicT v)
    (hm : IsMeanZeroT v) {Ca Cb : ℝ} (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb)
    (hA : IA v ≤ ENNReal.ofReal Ca * ITorus (1 / 2) v)
    (hB : IB v ≤ ENNReal.ofReal Cb
        * eLpNorm v 2 (volume.restrict fundamentalCube) ^ 2) :
    dotHomogeneousENorm (1 / 2) (cutoffMul v)
      ≤ ENNReal.ofReal
          (max (Real.sqrt (2 * Ca))
            (Real.sqrt (2 * Cb * (cFrac (1 / 2)).toReal⁻¹)))
        * (eLpNorm v 2 (volume.restrict fundamentalCube)
            + periodicHomogeneousENorm (1 / 2) v) := by
  set L : ℝ≥0∞ := eLpNorm v 2 (volume.restrict fundamentalCube) with hL
  set P : ℝ≥0∞ := periodicHomogeneousENorm (1 / 2) v with hP
  set D : ℝ≥0∞ := dotHomogeneousENorm (1 / 2) (cutoffMul v) with hD
  -- Chain the split with the two kernel bounds and the two identities.
  have hchain : cFrac (1 / 2) * D ^ (2 : ℕ)
      ≤ ENNReal.ofReal (2 * Ca) * (cFrac (1 / 2) * P ^ (2 : ℕ))
        + ENNReal.ofReal (2 * Cb) * L ^ 2 := by
    have h2Ca : (2 : ℝ≥0∞) * ENNReal.ofReal Ca = ENNReal.ofReal (2 * Ca) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
    have h2Cb : (2 : ℝ≥0∞) * ENNReal.ofReal Cb = ENNReal.ofReal (2 * Cb) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
    calc cFrac (1 / 2) * D ^ (2 : ℕ)
        = IReal (1 / 2) (cutoffMul v) := (ireal_cutoffMul_eq hv).symm
      _ ≤ 2 * IA v + 2 * IB v := ireal_cutoffMul_le_split hv
      _ ≤ 2 * (ENNReal.ofReal Ca * ITorus (1 / 2) v)
            + 2 * (ENNReal.ofReal Cb * L ^ 2) :=
          add_le_add (mul_le_mul_right hA 2) (mul_le_mul_right hB 2)
      _ = ENNReal.ofReal (2 * Ca) * ITorus (1 / 2) v
            + ENNReal.ofReal (2 * Cb) * L ^ 2 := by
          rw [← mul_assoc, ← mul_assoc, h2Ca, h2Cb]
      _ = ENNReal.ofReal (2 * Ca) * (cFrac (1 / 2) * P ^ (2 : ℕ))
            + ENNReal.ofReal (2 * Cb) * L ^ 2 := by
          rw [itorus_meanZero_eq hv hm]
  -- Divide by `cFrac (1/2)` and take the square root.
  have hres := enn_sqrt_div_bound (c := cFrac (1 / 2)) (D := D) (P := P) (L := L)
    (c1 := 2 * Ca) (c2 := 2 * Cb) cFrac_half_ne_zero cFrac_half_ne_top
    (by positivity) (by positivity)
    (by simpa [pow_two, sq] using hchain)
  simpa [hL, hP, hD] using hres

/-! ## §7  The two localization kernel bounds (reverse localization)

`iA_bound` (first split piece → torus Gagliardo integral, constant `343 = 7³`
from the lattice tiling) and `iB_bound` (second split piece → `L²(Q)`,
constant `cbConst = 686 · Jval` with `Jval` the finite commutator-kernel
integral) are the two analytic inputs of `dotHomogeneousENorm_cutoffMul_le`. -/

/-! ## §1  Cutoff support helpers -/

/-- The closed support ball of the cutoff. -/
theorem tsupport_cutoff_closedBall : tsupport cutoff ⊆ closedBall (0 : Space) 3 := by
  have h : tsupport (cutoffBump : Space → ℝ) = closedBall (0 : Space) cutoffBump.rOut :=
    cutoffBump.tsupport_eq
  have : tsupport cutoff = closedBall (0 : Space) 3 := by
    change tsupport (cutoffBump : Space → ℝ) = _
    rw [h]; norm_num [cutoffBump]
  rw [this]

/-- Off the closed support ball the cutoff vanishes. -/
theorem cutoff_eq_zero_of_not_mem {x : Space} (hx : x ∉ closedBall (0 : Space) 3) :
    cutoff x = 0 := by
  by_contra h
  exact hx (tsupport_cutoff_closedBall (subset_tsupport cutoff (Function.mem_support.mpr h)))

/-- `cutoff x ^ 2 ≤ indicator of the closed support ball`, in `ℝ≥0∞`. -/
theorem ofReal_cutoff_sq_le_indicator (x : Space) :
    ENNReal.ofReal (cutoff x ^ 2)
      ≤ (closedBall (0 : Space) 3).indicator (fun _ => (1 : ℝ≥0∞)) x := by
  by_cases hx : x ∈ closedBall (0 : Space) 3
  · rw [Set.indicator_of_mem hx]
    have h1 : cutoff x ^ 2 ≤ 1 := by
      have hr := cutoff_range x
      nlinarith [hr.1, hr.2]
    calc ENNReal.ofReal (cutoff x ^ 2) ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal h1
      _ = 1 := by simp
  · rw [Set.indicator_of_notMem hx, cutoff_eq_zero_of_not_mem hx]
    simp

/-! ## §2  Kernel evenness and lattice invariance -/

theorem fractionalRadialKernel_neg (s : ℝ) (w : Space) :
    fractionalRadialKernel s (-w) = fractionalRadialKernel s w := by
  simp only [fractionalRadialKernel, norm_neg]

theorem periodicKernel_neg (s : ℝ) (w : Space) :
    periodicKernel s (-w) = periodicKernel s w := by
  rw [periodicKernel, periodicKernel,
    ← (Equiv.neg PeriodicFrequency).tsum_eq
        (fun n => fractionalRadialKernel s (-w + latticeVector n))]
  refine tsum_congr fun n => ?_
  show fractionalRadialKernel s (-w + latticeVector (-n))
      = fractionalRadialKernel s (w + latticeVector n)
  rw [latticeVector_neg, show -w + -latticeVector n = -(w + latticeVector n) by abel,
    fractionalRadialKernel_neg]

theorem latticeVector_add (m n : PeriodicFrequency) :
    latticeVector (m + n) = latticeVector m + latticeVector n := by
  ext j
  show (((m + n) j : ℤ) : ℝ) = _
  simp [latticeVector, Pi.add_apply]

theorem periodicKernel_add_latticeVector (s : ℝ) (w : Space) (m : PeriodicFrequency) :
    periodicKernel s (w + latticeVector m) = periodicKernel s w := by
  rw [periodicKernel, periodicKernel,
    ← (Equiv.addLeft m).tsum_eq (fun n => fractionalRadialKernel s (w + latticeVector n))]
  refine tsum_congr fun n => ?_
  show fractionalRadialKernel s (w + latticeVector m + latticeVector n)
      = fractionalRadialKernel s (w + latticeVector (m + n))
  rw [latticeVector_add, add_assoc]

theorem coordinateVector_eq_latticeVector (i : Fin 3) :
    coordinateVector i = latticeVector (Pi.single i 1) := by
  ext j
  rw [latticeVector_apply, coordinateVector]
  by_cases hj : j = i <;>
    simp [hj]

theorem periodicKernel_add_coordinateVector (s : ℝ) (w : Space) (i : Fin 3) :
    periodicKernel s (w + coordinateVector i) = periodicKernel s w := by
  rw [coordinateVector_eq_latticeVector, periodicKernel_add_latticeVector]

/-! ## §3  Measurability -/

theorem measurable_periodicKernel (s : ℝ) : Measurable (fun h : Space => periodicKernel s h) := by
  unfold periodicKernel
  refine Measurable.tsum fun n => ?_
  exact (measurable_fractionalRadialKernel s).comp (measurable_id.add_const (latticeVector n))

theorem measurable_cubeInnerIntegrand {v : SpatialField} (hv : SmoothPeriodicT v) :
    Measurable (fun p : Space × Space =>
      ENNReal.ofReal (‖v p.1 - v p.2‖ ^ 2) * periodicKernel (1 / 2) (p.1 - p.2)) := by
  have hvc := hv.1.continuous
  refine Measurable.mul ?_
    ((measurable_periodicKernel (1 / 2)).comp (continuous_fst.sub continuous_snd).measurable)
  exact ENNReal.measurable_ofReal.comp
    (((hvc.comp continuous_fst).sub (hvc.comp continuous_snd)).norm.pow 2).measurable

/-! ## §4  The folded torus inner integral -/

/-- The folded single-cube inner integral (with the periodized kernel). -/
def cubeInner (v : SpatialField) (y : Space) : ℝ≥0∞ :=
  ∫⁻ x in halfOpenCube, ENNReal.ofReal (‖v y - v x‖ ^ 2) * periodicKernel (1 / 2) (y - x)

theorem measurable_cubeInner {v : SpatialField} (hv : SmoothPeriodicT v) :
    Measurable (cubeInner v) :=
  (measurable_cubeInnerIntegrand hv).lintegral_prod_right

theorem isPeriodicSpatial_cubeInner {v : SpatialField} (hv : SmoothPeriodicT v) :
    IsPeriodicSpatial (cubeInner v) := by
  intro y i
  unfold cubeInner
  refine lintegral_congr fun x => ?_
  rw [hv.2 y i, show y + coordinateVector i - x = (y - x) + coordinateVector i by abel,
    periodicKernel_add_coordinateVector]

/-! ## §5  The `IA` transform to the folded torus integral -/

theorem norm_smul_sq (a : ℝ) (w : Space) : ‖a • w‖ ^ 2 = a ^ 2 * ‖w‖ ^ 2 := by
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

/-- The transformed first-split integrand, with the cutoff pushed onto `y`. -/
def gPsi (v : SpatialField) (x y : Space) : ℝ≥0∞ :=
  ENNReal.ofReal (cutoff y ^ 2)
    * (ENNReal.ofReal (‖v y - v x‖ ^ 2) * fractionalRadialKernel (1 / 2) (y - x))

theorem measurable_gPsi {v : SpatialField} (hv : SmoothPeriodicT v) :
    Measurable (Function.uncurry (gPsi v)) := by
  have hc : Continuous cutoff := cutoff_contDiff.continuous
  have hvc : Continuous v := hv.1.continuous
  unfold Function.uncurry gPsi
  refine Measurable.mul ?_ (Measurable.mul ?_ ?_)
  · exact ENNReal.measurable_ofReal.comp ((hc.comp continuous_snd).pow 2).measurable
  · exact ENNReal.measurable_ofReal.comp
      (((hvc.comp continuous_snd).sub (hvc.comp continuous_fst)).norm.pow 2).measurable
  · exact (measurable_fractionalRadialKernel (1 / 2)).comp
      (continuous_snd.sub continuous_fst).measurable

/-- Substitution `h ↦ y = x + h` inside the first-split `h`-integral. -/
theorem iA_inner_sub {v : SpatialField} (x : Space) :
    (∫⁻ h : Space, gA v h x) = ∫⁻ y : Space, gPsi v x y := by
  have hsub : (∫⁻ h : Space, gA v h x)
      = ∫⁻ y : Space, ENNReal.ofReal (‖cutoff y • (v y - v x)‖ ^ 2)
          * fractionalRadialKernel (1 / 2) (y - x) := by
    rw [← lintegral_add_left_eq_self
      (fun y : Space => ENNReal.ofReal (‖cutoff y • (v y - v x)‖ ^ 2)
        * fractionalRadialKernel (1 / 2) (y - x)) x]
    refine lintegral_congr fun h => ?_
    have he : x + h - x = h := by abel
    simp only [gA, he]
  rw [hsub]
  refine lintegral_congr fun y => ?_
  rw [gPsi, norm_smul_sq (cutoff y) (v y - v x), ENNReal.ofReal_mul (by positivity), mul_assoc]

theorem measurable_innerFrac {v : SpatialField} (hv : SmoothPeriodicT v) (y : Space) :
    Measurable (fun x : Space =>
      ENNReal.ofReal (‖v y - v x‖ ^ 2) * fractionalRadialKernel (1 / 2) (y - x)) := by
  have hvc : Continuous v := hv.1.continuous
  refine Measurable.mul ?_
    ((measurable_fractionalRadialKernel (1 / 2)).comp (measurable_const.sub measurable_id))
  exact ENNReal.measurable_ofReal.comp ((continuous_const.sub hvc).norm.pow 2).measurable

/-- **`IA` transform.**  `IA v = ∫⁻ y, χ(y)² · cubeInner v y`. -/
theorem iA_transform {v : SpatialField} (hv : SmoothPeriodicT v) :
    IA v = ∫⁻ y : Space, ENNReal.ofReal (cutoff y ^ 2) * cubeInner v y := by
  calc IA v = ∫⁻ h : Space, ∫⁻ x : Space, gA v h x := rfl
    _ = ∫⁻ x : Space, ∫⁻ h : Space, gA v h x :=
        lintegral_lintegral_swap (measurable_gA_pair hv).aemeasurable
    _ = ∫⁻ x : Space, ∫⁻ y : Space, gPsi v x y :=
        lintegral_congr fun x => iA_inner_sub x
    _ = ∫⁻ y : Space, ∫⁻ x : Space, gPsi v x y :=
        lintegral_lintegral_swap (measurable_gPsi hv).aemeasurable
    _ = ∫⁻ y : Space, ENNReal.ofReal (cutoff y ^ 2) * cubeInner v y := by
        refine lintegral_congr fun y => ?_
        simp only [gPsi]
        rw [lintegral_const_mul _ (measurable_innerFrac hv y)]
        congr 1
        exact (lintegral_cube_periodicKernel hv.2 hv.1.continuous y).symm

/-- **Torus integral as folded cube integral.** -/
theorem itorus_eq_cubeInner {v : SpatialField} (hv : SmoothPeriodicT v) :
    ITorus (1 / 2) v = ∫⁻ y in halfOpenCube, cubeInner v y := by
  rw [ITorus, setLIntegral_congr fundamentalCube_ae_eq_halfOpenCube,
    lintegral_congr (fun _ => setLIntegral_congr fundamentalCube_ae_eq_halfOpenCube)]
  rw [lintegral_lintegral_swap (measurable_cubeInnerIntegrand hv).aemeasurable]
  refine lintegral_congr fun y => ?_
  refine lintegral_congr fun x => ?_
  rw [norm_sub_rev (v x) (v y), show x - y = -(y - x) by abel, periodicKernel_neg]

/-! ## §6  Lattice counting and the `IA` bound -/

/-- For ANY offset `w`, the number of unit-lattice translates `w + latticeVector n`
landing in `closedBall 0 3` is at most `7^3 = 343`. -/
theorem lattice_count_le (w : Space) :
    (∑' n : PeriodicFrequency,
        (Metric.closedBall (0 : Space) 3).indicator (fun _ => (1 : ℝ≥0∞))
          (w + latticeVector n))
      ≤ (343 : ℝ≥0∞) := by
  set F : Finset PeriodicFrequency :=
      Fintype.piFinset (fun i : Fin 3 => Finset.Icc ⌈(-3 - w i : ℝ)⌉ ⌊(3 - w i : ℝ)⌋) with hF
  have hsupp : ∀ n ∉ F,
      (Metric.closedBall (0 : Space) 3).indicator (fun _ => (1 : ℝ≥0∞))
        (w + latticeVector n) = 0 := by
    intro n hn
    apply Set.indicator_of_notMem
    intro hmem
    apply hn
    rw [Metric.mem_closedBall, dist_zero_right] at hmem
    rw [hF, Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    have hcoord : |w i + (n i : ℝ)| ≤ 3 := by
      have happly : (w + latticeVector n) i = w i + (n i : ℝ) := by
        simp [latticeVector_apply]
      calc |w i + (n i : ℝ)| = |(w + latticeVector n) i| := by rw [happly]
        _ ≤ ‖w + latticeVector n‖ := abs_spaceCoord_le_norm _ _
        _ ≤ 3 := hmem
    have habs := abs_le.mp hcoord
    refine ⟨Int.ceil_le.mpr ?_, Int.le_floor.mpr ?_⟩
    · have := habs.1; push_cast; linarith
    · have := habs.2; push_cast; linarith
  rw [tsum_eq_sum hsupp]
  have hcard : F.card ≤ 343 := by
    rw [hF, Fintype.card_piFinset]
    calc ∏ i : Fin 3, (Finset.Icc ⌈(-3 - w i : ℝ)⌉ ⌊(3 - w i : ℝ)⌋).card
        ≤ ∏ _i : Fin 3, 7 := by
          apply Finset.prod_le_prod'
          intro i _
          rw [Int.card_Icc]
          apply Int.toNat_le.mpr
          have hb : (⌊(3 - w i : ℝ)⌋ : ℝ) ≤ 3 - w i := Int.floor_le _
          have ha : (-3 - w i : ℝ) ≤ (⌈(-3 - w i : ℝ)⌉ : ℝ) := Int.le_ceil _
          have hreal :
              ((⌊(3 - w i : ℝ)⌋ + 1 - ⌈(-3 - w i : ℝ)⌉ : ℤ) : ℝ) ≤ (7 : ℝ) := by
            push_cast; linarith
          exact_mod_cast hreal
      _ = 343 := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]; norm_num
  calc ∑ n ∈ F, (Metric.closedBall (0 : Space) 3).indicator (fun _ => (1 : ℝ≥0∞))
          (w + latticeVector n)
      ≤ ∑ _n ∈ F, (1 : ℝ≥0∞) := by
        apply Finset.sum_le_sum
        intro n _
        exact Set.indicator_apply_le' (fun _ => le_rfl) (fun _ => zero_le_one)
    _ = (F.card : ℝ≥0∞) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ (343 : ℝ≥0∞) := by exact_mod_cast hcard

/-- **First localization kernel bound.**  `IA v ≤ 343 · ITorus (1/2) v`. -/
theorem iA_bound {v : SpatialField} (hv : SmoothPeriodicT v) :
    IA v ≤ ENNReal.ofReal 343 * ITorus (1 / 2) v := by
  have hmeasG : Measurable (fun y : Space => ENNReal.ofReal (cutoff y ^ 2) * cubeInner v y) :=
    (ENNReal.measurable_ofReal.comp (cutoff_contDiff.continuous.pow 2).measurable).mul
      (measurable_cubeInner hv)
  have hterm : ∀ n : PeriodicFrequency,
      (∫⁻ y in halfOpenCube, ENNReal.ofReal (cutoff (y + latticeVector n) ^ 2)
          * cubeInner v (y + latticeVector n))
        = ∫⁻ y in halfOpenCube,
            ENNReal.ofReal (cutoff (y + latticeVector n) ^ 2) * cubeInner v y := by
    intro n
    refine lintegral_congr fun y => ?_
    rw [periodic_latticeVector (isPeriodicSpatial_cubeInner hv) y n]
  have hmeasTerm : ∀ n : PeriodicFrequency,
      Measurable (fun y : Space =>
        ENNReal.ofReal (cutoff (y + latticeVector n) ^ 2) * cubeInner v y) :=
    fun n => (ENNReal.measurable_ofReal.comp
      (((cutoff_contDiff.continuous.comp (continuous_id.add_const _)).pow 2).measurable)).mul
      (measurable_cubeInner hv)
  have hcount : ∀ y : Space,
      (∑' n : PeriodicFrequency, ENNReal.ofReal (cutoff (y + latticeVector n) ^ 2)) ≤ 343 := by
    intro y
    refine le_trans (ENNReal.tsum_le_tsum fun n =>
      ofReal_cutoff_sq_le_indicator (y + latticeVector n)) (lattice_count_le y)
  rw [iA_transform hv, itorus_eq_cubeInner hv, lintegral_eq_tsum_halfOpenCube hmeasG,
    tsum_congr hterm, ← lintegral_tsum (fun n => (hmeasTerm n).aemeasurable)]
  calc ∫⁻ y in halfOpenCube, ∑' n : PeriodicFrequency,
          ENNReal.ofReal (cutoff (y + latticeVector n) ^ 2) * cubeInner v y
      = ∫⁻ y in halfOpenCube,
          (∑' n : PeriodicFrequency, ENNReal.ofReal (cutoff (y + latticeVector n) ^ 2))
            * cubeInner v y := by
        refine lintegral_congr fun y => ?_
        rw [ENNReal.tsum_mul_right]
    _ ≤ ∫⁻ y in halfOpenCube, (343 : ℝ≥0∞) * cubeInner v y :=
        lintegral_mono fun y => mul_le_mul' (hcount y) le_rfl
    _ = (343 : ℝ≥0∞) * ∫⁻ y in halfOpenCube, cubeInner v y :=
        lintegral_const_mul _ (measurable_cubeInner hv)
    _ = ENNReal.ofReal 343 * ∫⁻ y in halfOpenCube, cubeInner v y := by
        rw [ENNReal.ofReal_ofNat]

/-! ## §7  Kernel integrability and the cutoff Lipschitz constant -/

/-- The Gagliardo-tail integral with a Lipschitz-truncated numerator is finite
(proved by mirroring `cFrac_lt_top`). -/
theorem jkernel_lt_top (L : ℝ) (hL : 0 ≤ L) :
    (∫⁻ h : Space, min (ENNReal.ofReal (L ^ 2 * ‖h‖ ^ 2)) 1
        * fractionalRadialKernel (1 / 2) h) < ⊤ := by
  have hker : ∀ h : Space, 0 < ‖h‖ →
      fractionalRadialKernel (1 / 2) h = ENNReal.ofReal (‖h‖ ^ (-(4 : ℝ))) := by
    intro h hpos
    simp only [fractionalRadialKernel]
    rw [show (-(3 + 2 * (1 / 2 : ℝ))) = -(4 : ℝ) by norm_num,
      ENNReal.ofReal_rpow_of_pos hpos]
  have key : ∀ h : Space, ENNReal.ofReal (L ^ 2 * ‖h‖ ^ 2) * fractionalRadialKernel (1 / 2) h
      = ENNReal.ofReal (L ^ 2 * ‖h‖ ^ (-(2 : ℝ))) := by
    intro h
    rcases eq_or_lt_of_le (norm_nonneg h) with h0 | hpos
    · have hz : h = 0 := norm_eq_zero.1 h0.symm
      subst hz
      rw [norm_zero, Real.zero_rpow (by norm_num : (-(2 : ℝ)) ≠ 0)]
      simp [fractionalRadialKernel]
    · rw [hker h hpos, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ L ^ 2 * ‖h‖ ^ 2)]
      congr 1
      have hexp : ((2 : ℕ) : ℝ) + (-(4 : ℝ)) = -(2 : ℝ) := by norm_num
      rw [mul_assoc, ← Real.rpow_natCast ‖h‖ 2, ← Real.rpow_add hpos, hexp]
  have hmeasA : MeasurableSet (Metric.ball (0 : Space) 1) := measurableSet_ball
  have hsplit := lintegral_add_compl (μ := (volume : Measure Space))
    (fun h : Space ↦ min (ENNReal.ofReal (L ^ 2 * ‖h‖ ^ 2)) 1
      * fractionalRadialKernel (1 / 2) h) hmeasA
  rw [← hsplit]
  refine ENNReal.add_lt_top.2 ⟨?_, ?_⟩
  · have hbound : ∫⁻ h in Metric.ball (0 : Space) 1,
        min (ENNReal.ofReal (L ^ 2 * ‖h‖ ^ 2)) 1 * fractionalRadialKernel (1 / 2) h ≤
        ∫⁻ h in Metric.ball (0 : Space) 1, ENNReal.ofReal (L ^ 2 * ‖h‖ ^ (-(2 : ℝ))) := by
      refine setLIntegral_mono_ae (Measurable.aemeasurable (by measurability)) ?_
      filter_upwards with h hh
      calc min (ENNReal.ofReal (L ^ 2 * ‖h‖ ^ 2)) 1 * fractionalRadialKernel (1 / 2) h
          ≤ ENNReal.ofReal (L ^ 2 * ‖h‖ ^ 2) * fractionalRadialKernel (1 / 2) h :=
            mul_le_mul' (min_le_left _ _) le_rfl
        _ = ENNReal.ofReal (L ^ 2 * ‖h‖ ^ (-(2 : ℝ))) := key h
    refine lt_of_le_of_lt hbound ?_
    have hint : IntegrableOn (fun h : Space ↦ L ^ 2 * ‖h‖ ^ (-(2 : ℝ)))
        (Metric.ball (0 : Space) 1) volume := by
      refine integrableOn_ball_of_norm_le_rpow (μ := (volume : Measure Space))
        (by simp) (C := L ^ 2) (α := 2)
        (by rw [finrank_euclideanSpace_fin]; push_cast; linarith) ?_
        (Measurable.aestronglyMeasurable (by measurability))
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hfin := hint.hasFiniteIntegral
    rw [hasFiniteIntegral_iff_enorm,
      lintegral_enorm_of_nonneg (fun x ↦ by positivity)] at hfin
    exact hfin
  · have hbound : ∫⁻ h in (Metric.ball (0 : Space) 1)ᶜ,
        min (ENNReal.ofReal (L ^ 2 * ‖h‖ ^ 2)) 1 * fractionalRadialKernel (1 / 2) h ≤
        ∫⁻ h : Space, ENNReal.ofReal (2 ^ (4 : ℝ) * (1 + ‖h‖) ^ (-(4 : ℝ))) := by
      refine le_trans (setLIntegral_mono_ae (Measurable.aemeasurable (by measurability)) ?_)
        (setLIntegral_le_lintegral _ _)
      filter_upwards with h hh
      have hge : 1 ≤ ‖h‖ := by
        have hnb : ¬ ‖h‖ < 1 := by simpa [mem_ball_zero_iff] using hh
        exact not_lt.1 hnb
      have hpos : (0 : ℝ) < ‖h‖ := lt_of_lt_of_le zero_lt_one hge
      have farbound : fractionalRadialKernel (1 / 2) h ≤
          ENNReal.ofReal (2 ^ (4 : ℝ) * (1 + ‖h‖) ^ (-(4 : ℝ))) := by
        rw [hker h hpos]
        refine ENNReal.ofReal_le_ofReal ?_
        have hhalf : (1 + ‖h‖) / 2 ≤ ‖h‖ := by linarith
        have hhalfpos : (0 : ℝ) < (1 + ‖h‖) / 2 := by linarith
        have hmono : ‖h‖ ^ (-(4 : ℝ)) ≤ ((1 + ‖h‖) / 2) ^ (-(4 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos hhalfpos hhalf (by norm_num)
        have h2a : ((2 : ℝ)⁻¹) ^ (-(4 : ℝ)) = 2 ^ (4 : ℝ) := by
          rw [Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), inv_inv]
        have hsplit2 : ((1 + ‖h‖) / 2) ^ (-(4 : ℝ)) =
            2 ^ (4 : ℝ) * (1 + ‖h‖) ^ (-(4 : ℝ)) := by
          rw [div_eq_mul_inv, Real.mul_rpow (by linarith) (by norm_num), h2a]
          ring
        calc ‖h‖ ^ (-(4 : ℝ)) ≤ ((1 + ‖h‖) / 2) ^ (-(4 : ℝ)) := hmono
          _ = 2 ^ (4 : ℝ) * (1 + ‖h‖) ^ (-(4 : ℝ)) := hsplit2
      calc min (ENNReal.ofReal (L ^ 2 * ‖h‖ ^ 2)) 1 * fractionalRadialKernel (1 / 2) h
          ≤ 1 * fractionalRadialKernel (1 / 2) h := mul_le_mul' (min_le_right _ _) le_rfl
        _ = fractionalRadialKernel (1 / 2) h := one_mul _
        _ ≤ ENNReal.ofReal (2 ^ (4 : ℝ) * (1 + ‖h‖) ^ (-(4 : ℝ))) := farbound
    refine lt_of_le_of_lt hbound ?_
    have hc : (0 : ℝ) ≤ 2 ^ (4 : ℝ) := by positivity
    have hrw : ∀ h : Space, ENNReal.ofReal (2 ^ (4 : ℝ) * (1 + ‖h‖) ^ (-(4 : ℝ))) =
        ENNReal.ofReal (2 ^ (4 : ℝ)) *
          ENNReal.ofReal ((1 + ‖h‖) ^ (-(4 : ℝ))) := fun h ↦ ENNReal.ofReal_mul hc
    rw [lintegral_congr hrw, lintegral_const_mul _ (by measurability)]
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
    exact finite_integral_one_add_norm (E := Space) (μ := (volume : Measure Space))
      (by rw [finrank_euclideanSpace_fin]; push_cast; linarith)

/-- A cutoff-derivative bound realizing the paper's Lipschitz constant. -/
def cutoffLip : ℝ := exists_cutoff_fderiv_bound.choose

theorem cutoffLip_spec (x : Space) : ‖fderiv ℝ cutoff x‖ ≤ cutoffLip :=
  exists_cutoff_fderiv_bound.choose_spec x

theorem cutoffLip_nonneg : 0 ≤ cutoffLip := le_trans (norm_nonneg _) (cutoffLip_spec 0)

/-- Mean-value Lipschitz bound: `(χ(x+h)-χ(x))² ≤ L²‖h‖²`. -/
theorem cutoff_diff_sq_le_lip (x h : Space) :
    (cutoff (x + h) - cutoff x) ^ 2 ≤ cutoffLip ^ 2 * ‖h‖ ^ 2 := by
  have hmvt : ‖cutoff (x + h) - cutoff x‖ ≤ cutoffLip * ‖(x + h) - x‖ :=
    Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => (cutoff_contDiff.differentiable (by norm_num)).differentiableAt)
      (fun z _ => cutoffLip_spec z) convex_univ (mem_univ _) (mem_univ _)
  rw [add_sub_cancel_left] at hmvt
  have h2 : |cutoff (x + h) - cutoff x| ≤ cutoffLip * ‖h‖ := by
    rwa [Real.norm_eq_abs] at hmvt
  nlinarith [sq_abs (cutoff (x + h) - cutoff x), abs_nonneg (cutoff (x + h) - cutoff x),
    mul_self_le_mul_self (abs_nonneg (cutoff (x + h) - cutoff x)) h2,
    mul_nonneg cutoffLip_nonneg (norm_nonneg h)]

/-- Range bound: `(χ(x+h)-χ(x))² ≤ 1`. -/
theorem cutoff_diff_sq_le_one (x h : Space) :
    (cutoff (x + h) - cutoff x) ^ 2 ≤ 1 := by
  have a := cutoff_range (x + h)
  have b := cutoff_range x
  nlinarith [a.1, a.2, b.1, b.2]

/-! ## §8  `L²(Q)` conversion and the ball-tiling bound -/

theorem sq_eLpNorm_two_measure (f : SpatialField) (μ : Measure Space) :
    eLpNorm f 2 μ ^ 2 = ∫⁻ x : Space, ENNReal.ofReal (‖f x‖ ^ 2) ∂μ := by
  have hpt : (fun a : Space => ‖f a‖ₑ ^ (2 : ℝ)) = fun a => ENNReal.ofReal (‖f a‖ ^ 2) := by
    funext a
    rw [← ofReal_norm (f a),
      ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num), eLpNorm',
    show ((2 : ℝ≥0∞).toReal) = (2 : ℝ) by norm_num, hpt,
    ← ENNReal.rpow_natCast ((∫⁻ a : Space, ENNReal.ofReal (‖f a‖ ^ 2) ∂μ) ^ (1 / (2 : ℝ))) 2,
    ← ENNReal.rpow_mul, show (1 / (2 : ℝ)) * ((2 : ℕ) : ℝ) = 1 by norm_num, ENNReal.rpow_one]

/-- The `L²(Q)` norm squared as the physical cube integral of `‖v‖²`. -/
theorem sq_eLpNorm_restrict_eq {v : SpatialField} :
    eLpNorm v 2 (volume.restrict fundamentalCube) ^ 2
      = ∫⁻ x in halfOpenCube, ENNReal.ofReal (‖v x‖ ^ 2) := by
  rw [sq_eLpNorm_two_measure v (volume.restrict fundamentalCube)]
  exact setLIntegral_congr fundamentalCube_ae_eq_halfOpenCube

/-- The physical mass over a radius-3 ball is at most `343` cubes of mass. -/
theorem ballMass_le {v : SpatialField} (hv : SmoothPeriodicT v) (w : Space) :
    (∫⁻ x : Space, (Metric.closedBall (0 : Space) 3).indicator (fun _ => (1 : ℝ≥0∞)) (x + w)
        * ENNReal.ofReal (‖v x‖ ^ 2))
      ≤ ENNReal.ofReal 343 * ∫⁻ x in halfOpenCube, ENNReal.ofReal (‖v x‖ ^ 2) := by
  have hvc : Continuous v := hv.1.continuous
  have hmeasG : Measurable (fun x : Space =>
      (Metric.closedBall (0 : Space) 3).indicator (fun _ => (1 : ℝ≥0∞)) (x + w)
        * ENNReal.ofReal (‖v x‖ ^ 2)) :=
    ((measurable_const.indicator measurableSet_closedBall).comp (measurable_id.add_const w)).mul
      (ENNReal.measurable_ofReal.comp (hvc.norm.pow 2).measurable)
  have hterm : ∀ n : PeriodicFrequency,
      (∫⁻ x in halfOpenCube,
          (Metric.closedBall (0 : Space) 3).indicator (fun _ => (1 : ℝ≥0∞))
              ((x + latticeVector n) + w) * ENNReal.ofReal (‖v (x + latticeVector n)‖ ^ 2))
        = ∫⁻ x in halfOpenCube,
            (Metric.closedBall (0 : Space) 3).indicator (fun _ => (1 : ℝ≥0∞))
                ((x + w) + latticeVector n) * ENNReal.ofReal (‖v x‖ ^ 2) := by
    intro n
    refine lintegral_congr fun x => ?_
    rw [periodic_latticeVector hv.2 x n,
      show x + latticeVector n + w = (x + w) + latticeVector n by abel]
  have hmeasTerm : ∀ n : PeriodicFrequency,
      Measurable (fun x : Space =>
        (Metric.closedBall (0 : Space) 3).indicator (fun _ => (1 : ℝ≥0∞))
            ((x + w) + latticeVector n) * ENNReal.ofReal (‖v x‖ ^ 2)) :=
    fun n => ((measurable_const.indicator measurableSet_closedBall).comp
      ((measurable_id.add_const w).add_const (latticeVector n))).mul
      (ENNReal.measurable_ofReal.comp (hvc.norm.pow 2).measurable)
  have hcount : ∀ x : Space,
      (∑' n : PeriodicFrequency,
        (Metric.closedBall (0 : Space) 3).indicator (fun _ => (1 : ℝ≥0∞))
          ((x + w) + latticeVector n)) ≤ 343 := fun x => lattice_count_le (x + w)
  rw [lintegral_eq_tsum_halfOpenCube hmeasG, tsum_congr hterm,
    ← lintegral_tsum (fun n => (hmeasTerm n).aemeasurable)]
  calc ∫⁻ x in halfOpenCube, ∑' n : PeriodicFrequency,
          (Metric.closedBall (0 : Space) 3).indicator (fun _ => (1 : ℝ≥0∞))
              ((x + w) + latticeVector n) * ENNReal.ofReal (‖v x‖ ^ 2)
      = ∫⁻ x in halfOpenCube,
          (∑' n : PeriodicFrequency, (Metric.closedBall (0 : Space) 3).indicator
              (fun _ => (1 : ℝ≥0∞)) ((x + w) + latticeVector n)) * ENNReal.ofReal (‖v x‖ ^ 2) := by
        refine lintegral_congr fun x => ?_
        rw [ENNReal.tsum_mul_right]
    _ ≤ ∫⁻ x in halfOpenCube, (343 : ℝ≥0∞) * ENNReal.ofReal (‖v x‖ ^ 2) :=
        lintegral_mono fun x => mul_le_mul' (hcount x) le_rfl
    _ = (343 : ℝ≥0∞) * ∫⁻ x in halfOpenCube, ENNReal.ofReal (‖v x‖ ^ 2) :=
        lintegral_const_mul _ (ENNReal.measurable_ofReal.comp (hvc.norm.pow 2).measurable)
    _ = ENNReal.ofReal 343 * ∫⁻ x in halfOpenCube, ENNReal.ofReal (‖v x‖ ^ 2) := by
        rw [ENNReal.ofReal_ofNat]

/-! ## §9  The `IB` bound -/

/-- The `ℝ≥0∞` indicator of the closed support ball. -/
def chiBall : Space → ℝ≥0∞ := (Metric.closedBall (0 : Space) 3).indicator (fun _ => 1)

theorem measurable_chiBall : Measurable chiBall :=
  measurable_const.indicator measurableSet_closedBall

/-- The Lipschitz-truncated numerator weight `min(L²‖h‖², 1)`. -/
def Ecut : Space → ℝ≥0∞ := fun h => min (ENNReal.ofReal (cutoffLip ^ 2 * ‖h‖ ^ 2)) 1

theorem measurable_Ecut : Measurable Ecut :=
  (ENNReal.measurable_ofReal.comp
    (continuous_const.mul (continuous_norm.pow 2)).measurable).min measurable_const

/-- The finite Lipschitz-tail constant. -/
def Jval : ℝ≥0∞ := ∫⁻ h : Space, Ecut h * fractionalRadialKernel (1 / 2) h

theorem Jval_lt_top : Jval < ⊤ := by
  show (∫⁻ h : Space, min (ENNReal.ofReal (cutoffLip ^ 2 * ‖h‖ ^ 2)) 1
      * fractionalRadialKernel (1 / 2) h) < ⊤
  exact jkernel_lt_top cutoffLip cutoffLip_nonneg

/-- The explicit second constant `Cb = 686 · J`. -/
def cbConst : ℝ := 686 * Jval.toReal

theorem cbConst_nonneg : 0 ≤ cbConst := by
  unfold cbConst; positivity

/-- The `ℝ≥0∞` bound `ofReal((χ(x+h)-χ x)²) ≤ Ecut h`. -/
theorem ofReal_cutoff_diff_sq_le_Ecut (h x : Space) :
    ENNReal.ofReal ((cutoff (x + h) - cutoff x) ^ 2) ≤ Ecut h := by
  refine le_min ?_ ?_
  · exact ENNReal.ofReal_le_ofReal (cutoff_diff_sq_le_lip x h)
  · rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (cutoff_diff_sq_le_one x h)

/-- Support-localized bound: the commutator numerator is controlled by the
truncated weight times the two support indicators. -/
theorem ofReal_cutoff_diff_sq_le_split (h x : Space) :
    ENNReal.ofReal ((cutoff (x + h) - cutoff x) ^ 2)
      ≤ Ecut h * chiBall x + Ecut h * chiBall (x + h) := by
  by_cases hx : x ∈ Metric.closedBall (0 : Space) 3
  · have hc : chiBall x = 1 := Set.indicator_of_mem hx _
    rw [hc, mul_one]
    exact (ofReal_cutoff_diff_sq_le_Ecut h x).trans (self_le_add_right _ _)
  · by_cases hxh : x + h ∈ Metric.closedBall (0 : Space) 3
    · have hc : chiBall (x + h) = 1 := Set.indicator_of_mem hxh _
      rw [hc, mul_one]
      exact (ofReal_cutoff_diff_sq_le_Ecut h x).trans (self_le_add_left _ _)
    · have hcx : chiBall x = 0 := Set.indicator_of_notMem hx _
      have hcxh : chiBall (x + h) = 0 := Set.indicator_of_notMem hxh _
      rw [hcx, hcxh, mul_zero, add_zero,
        cutoff_eq_zero_of_not_mem hx, cutoff_eq_zero_of_not_mem hxh]
      simp

/-- First localized integrand. -/
def gP1 (v : SpatialField) (h x : Space) : ℝ≥0∞ :=
  (Ecut h * fractionalRadialKernel (1 / 2) h) * (chiBall x * ENNReal.ofReal (‖v x‖ ^ 2))

/-- Second localized integrand. -/
def gP2 (v : SpatialField) (h x : Space) : ℝ≥0∞ :=
  (Ecut h * fractionalRadialKernel (1 / 2) h) * (chiBall (x + h) * ENNReal.ofReal (‖v x‖ ^ 2))

theorem measurable_gP1_pair {v : SpatialField} (hv : SmoothPeriodicT v) :
    Measurable (Function.uncurry (gP1 v)) := by
  have hvc : Continuous v := hv.1.continuous
  unfold Function.uncurry gP1
  refine Measurable.mul (Measurable.mul ?_ ?_) (Measurable.mul ?_ ?_)
  · exact measurable_Ecut.comp measurable_fst
  · exact (measurable_fractionalRadialKernel (1 / 2)).comp measurable_fst
  · exact measurable_chiBall.comp measurable_snd
  · exact ENNReal.measurable_ofReal.comp ((hvc.comp continuous_snd).norm.pow 2).measurable

/-- Pointwise split of the commutator integrand. -/
theorem gB_le_split (v : SpatialField) (h x : Space) :
    gB v h x ≤ gP1 v h x + gP2 v h x := by
  have hstep : gB v h x
      = ENNReal.ofReal ((cutoff (x + h) - cutoff x) ^ 2)
          * ENNReal.ofReal (‖v x‖ ^ 2) * fractionalRadialKernel (1 / 2) h := by
    simp only [gB]
    rw [norm_smul_sq, ENNReal.ofReal_mul (by positivity)]
  rw [hstep]
  calc ENNReal.ofReal ((cutoff (x + h) - cutoff x) ^ 2) * ENNReal.ofReal (‖v x‖ ^ 2)
        * fractionalRadialKernel (1 / 2) h
      ≤ (Ecut h * chiBall x + Ecut h * chiBall (x + h)) * ENNReal.ofReal (‖v x‖ ^ 2)
          * fractionalRadialKernel (1 / 2) h :=
        mul_le_mul' (mul_le_mul' (ofReal_cutoff_diff_sq_le_split h x) le_rfl) le_rfl
    _ = gP1 v h x + gP2 v h x := by simp only [gP1, gP2]; ring

/-- **Second localization kernel bound.**
`IB v ≤ Cb · ‖v‖²_{L²(Q)}` with `Cb = 686 · J`. -/
theorem iB_bound {v : SpatialField} (hv : SmoothPeriodicT v) :
    IB v ≤ ENNReal.ofReal cbConst
      * eLpNorm v 2 (volume.restrict fundamentalCube) ^ 2 := by
  rw [sq_eLpNorm_restrict_eq]
  set M : ℝ≥0∞ := ∫⁻ x in halfOpenCube, ENNReal.ofReal (‖v x‖ ^ 2) with hM
  have hvmeas : Measurable (fun x : Space => ENNReal.ofReal (‖v x‖ ^ 2)) :=
    ENNReal.measurable_ofReal.comp (hv.1.continuous.norm.pow 2).measurable
  have hEfrac : Measurable (fun h : Space => Ecut h * fractionalRadialKernel (1 / 2) h) :=
    measurable_Ecut.mul (measurable_fractionalRadialKernel (1 / 2))
  -- The two ball-mass estimates.
  have hA : ∀ h : Space,
      (∫⁻ x : Space, chiBall (x + h) * ENNReal.ofReal (‖v x‖ ^ 2)) ≤ ENNReal.ofReal 343 * M :=
    fun h => ballMass_le hv h
  have hA0 : (∫⁻ x : Space, chiBall x * ENNReal.ofReal (‖v x‖ ^ 2)) ≤ ENNReal.ofReal 343 * M := by
    have h0 := ballMass_le hv 0
    simp only [add_zero] at h0
    exact h0
  -- Bound on the first split integral.
  have hT1 : (∫⁻ h : Space, ∫⁻ x : Space, gP1 v h x) ≤ Jval * (ENNReal.ofReal 343 * M) := by
    have hinner : ∀ h : Space, (∫⁻ x : Space, gP1 v h x)
        = (Ecut h * fractionalRadialKernel (1 / 2) h)
            * ∫⁻ x : Space, chiBall x * ENNReal.ofReal (‖v x‖ ^ 2) := by
      intro h
      have hfx : Measurable (fun x : Space => chiBall x * ENNReal.ofReal (‖v x‖ ^ 2)) :=
        measurable_chiBall.mul hvmeas
      simp only [gP1]
      rw [lintegral_const_mul _ hfx]
    rw [lintegral_congr hinner,
      lintegral_mul_const _ hEfrac]
    exact mul_le_mul' le_rfl hA0
  -- Bound on the second split integral.
  have hT2 : (∫⁻ h : Space, ∫⁻ x : Space, gP2 v h x) ≤ Jval * (ENNReal.ofReal 343 * M) := by
    have hinner : ∀ h : Space, (∫⁻ x : Space, gP2 v h x)
        = (Ecut h * fractionalRadialKernel (1 / 2) h)
            * ∫⁻ x : Space, chiBall (x + h) * ENNReal.ofReal (‖v x‖ ^ 2) := by
      intro h
      have hfx : Measurable (fun x : Space => chiBall (x + h) * ENNReal.ofReal (‖v x‖ ^ 2)) :=
        (measurable_chiBall.comp (measurable_id.add_const h)).mul hvmeas
      simp only [gP2]
      rw [lintegral_const_mul _ hfx]
    rw [lintegral_congr hinner]
    calc ∫⁻ h : Space, (Ecut h * fractionalRadialKernel (1 / 2) h)
            * ∫⁻ x : Space, chiBall (x + h) * ENNReal.ofReal (‖v x‖ ^ 2)
        ≤ ∫⁻ h : Space, (Ecut h * fractionalRadialKernel (1 / 2) h) * (ENNReal.ofReal 343 * M) :=
          lintegral_mono fun h => mul_le_mul' le_rfl (hA h)
      _ = Jval * (ENNReal.ofReal 343 * M) := lintegral_mul_const _ hEfrac
  -- Constant conversion.
  have hcb : ENNReal.ofReal cbConst = 686 * Jval := by
    unfold cbConst
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 686),
      ENNReal.ofReal_toReal Jval_lt_top.ne, ENNReal.ofReal_ofNat]
  calc IB v = ∫⁻ h : Space, ∫⁻ x : Space, gB v h x := rfl
    _ ≤ ∫⁻ h : Space, ∫⁻ x : Space, (gP1 v h x + gP2 v h x) :=
        lintegral_mono fun h => lintegral_mono fun x => gB_le_split v h x
    _ = (∫⁻ h : Space, ∫⁻ x : Space, gP1 v h x)
          + (∫⁻ h : Space, ∫⁻ x : Space, gP2 v h x) := by
        have hinner : ∀ h : Space, (∫⁻ x : Space, (gP1 v h x + gP2 v h x))
            = (∫⁻ x : Space, gP1 v h x) + (∫⁻ x : Space, gP2 v h x) :=
          fun h => lintegral_add_left ((measurable_gP1_pair hv).comp measurable_prodMk_left) _
        rw [lintegral_congr hinner,
          lintegral_add_left (measurable_gP1_pair hv).lintegral_prod_right]
    _ ≤ Jval * (ENNReal.ofReal 343 * M) + Jval * (ENNReal.ofReal 343 * M) :=
        add_le_add hT1 hT2
    _ = ENNReal.ofReal cbConst * M := by
        rw [hcb]; simp only [ENNReal.ofReal_ofNat]; ring


/-! ## §8  The U3 target `cutoff_gagliardo_half` -/

/-- The explicit U3 constant. -/
def cutoffGagliardoConst : ℝ :=
  max (Real.sqrt (2 * 343)) (Real.sqrt (2 * cbConst * (cFrac (1 / 2)).toReal⁻¹))

/-- `0 < cutoffGagliardoConst`. -/
theorem cutoffGagliardoConst_pos : 0 < cutoffGagliardoConst := by
  have h : 0 < Real.sqrt (2 * 343) := Real.sqrt_pos.mpr (by norm_num)
  exact lt_of_lt_of_le h (le_max_left _ _)

/-- **T12 U3 (`appendix-b-embeddings.tex`, `03-torus.tex`).**  The reverse
localization comparison at the half order: for a smooth mean-zero periodic
field `v`, the whole-space homogeneous `Ḣ^{1/2}` norm of the cutoff `χ·v` is
controlled by the physical `L²(Q)` norm of `v` plus the torus homogeneous
`Ḣ^{1/2}(T³)` norm of `v`, with the explicit positive constant
`cutoffGagliardoConst`. -/
theorem cutoff_gagliardo_half (v : SpatialField) (hv : SmoothPeriodicT v)
    (hmean : IsMeanZeroT v) :
    dotHomogeneousENorm (1 / 2) (cutoffMul v)
      ≤ ENNReal.ofReal cutoffGagliardoConst
        * (eLpNorm v 2 (volume.restrict fundamentalCube)
            + periodicHomogeneousENorm (1 / 2) v) :=
  dotHomogeneousENorm_cutoffMul_le hv hmean (by norm_num) cbConst_nonneg
    (iA_bound hv) (iB_bound hv)

end NSFormalization.Section3.T12
