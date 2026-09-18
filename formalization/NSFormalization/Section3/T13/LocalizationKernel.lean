import NSFormalization.Section3.T13.ConstantEndpoints
import NSFormalization.Section3.T13.TorusIdentity
import NSFormalization.Section3.T11.CriterionBridge
import NSFormalization.Section3.T12.FourierEmbeddings
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# T13 localization kernel estimates (`03-torus.tex:73-98`)

This module proves the three concrete analytic estimates behind the uniform
localization inequality `eq:localization`, none of them a `LocalizationAPI`
field on its own; lane 354 assembles them with `torus_identity` (lane 345),
`endpoint_zero`/`constant_pos_finite` (lane 344) and `wholeSpace_identity`
(lane 348).

* §1 — the uniform lattice-tail bound.  For `0 < s` and `0 < ρ < 1` the
  nonzero-lattice tail `latticeTail s h` is bounded, uniformly over `‖h‖ ≤ ρ`,
  by the finite constant `tailConst s ρ`.  The convergence of the lattice
  series `∑_{n≠0} ‖n‖^{-(3+2s)}` is obtained from `ZLattice.summable_norm_rpow`
  (exponent `3 + 2s > 3`).  The geometric implication `2r < 1` from the
  admissible-ball hypothesis is `two_r_lt_one_of_closure_ball_subset`.
* §3 — the inhomogeneous/homogeneous comparison on `T³`.  For `0 < s ≤ 1` and
  a smooth periodic field `g`,
  `periodicSobolevENorm s g ≤ periodicSobolevENorm 0 g +
      periodicHomogeneousENorm s (meanZeroPartT g)`,
  by the coefficientwise subadditivity `(1+x)^{s/2} ≤ 1 + x^{s/2}` and the
  `ℓ²` triangle inequality on the Fourier data.
-/

noncomputable section

namespace NSFormalization.Section3.T13

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T11 (exists_periodicDatum_smooth periodicSobolevENorm_eq_datum)
open NSFormalization.Section3.T12 (reweightDatum reweightDatum_apply reweightDatum_enorm_le')
open scoped ContDiff ENNReal BigOperators Topology

/-! ## §1  Lattice-tail summability and the uniform tail bound -/

/-- The lattice `ℤ³ ⊂ ℝ³` in sup-norm coordinates, used only to import
`ZLattice.summable_norm_rpow`. -/
private def freqLattice : Submodule ℤ (Fin 3 → ℝ) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 3)))

private def freqEquiv : PeriodicFrequency ≃ₗ[ℤ] freqLattice :=
  ((Pi.basisFun ℝ (Fin 3)).restrictScalars ℤ).equivFun.symm

private theorem freqEquiv_coe (k : PeriodicFrequency) :
    (freqEquiv k : Fin 3 → ℝ) = fun i => (k i : ℝ) := by
  ext i
  show ((((Pi.basisFun ℝ (Fin 3)).restrictScalars ℤ).equivFun.symm k :
      freqLattice) : Fin 3 → ℝ) i = (k i : ℝ)
  simp [Module.Basis.equivFun_symm_apply, Finset.sum_apply, Pi.single_apply]

private theorem latticeVector_coord (n : PeriodicFrequency) (i : Fin 3) :
    latticeVector n i = (n i : ℝ) := rfl

private theorem norm_freqPi_le_latticeVector (n : PeriodicFrequency) :
    ‖(fun i => (n i : ℝ))‖ ≤ ‖latticeVector n‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro i
  rw [Real.norm_eq_abs, ← latticeVector_coord n i]
  exact abs_spaceCoord_le_norm _ _

private theorem latticeVector_norm_ge_one {n : PeriodicFrequency} (hn : n ≠ 0) :
    (1 : ℝ) ≤ ‖latticeVector n‖ := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hn
  have h1 : (1 : ℝ) ≤ |(n i : ℝ)| := by exact_mod_cast Int.one_le_abs hi
  rw [← latticeVector_coord n i] at h1
  exact h1.trans (abs_spaceCoord_le_norm _ _)

/-- The Euclidean lattice series `∑_k ‖k‖^{-p}` converges for `p > 3`. -/
theorem summable_latticeVector_rpow {p : ℝ} (hp : (3 : ℝ) < p) :
    Summable (fun n : PeriodicFrequency => ‖latticeVector n‖ ^ (-p)) := by
  have hsup : Summable (fun k : PeriodicFrequency => ‖(fun i => (k i : ℝ))‖ ^ (-p)) := by
    let _i : DiscreteTopology freqLattice := ZSpan.discreteTopology_pi_basisFun
    have hdim : Module.finrank ℤ freqLattice = 3 := by
      show Module.finrank ℤ
        (↥(Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 3))))) = 3
      rw [Module.finrank_eq_card_basis ((Pi.basisFun ℝ (Fin 3)).restrictScalars ℤ)]
      rfl
    have h := (freqEquiv.toEquiv.summable_iff).mpr
      (ZLattice.summable_norm_rpow freqLattice (-p) (by rw [hdim]; push_cast; linarith))
    change Summable (fun k => ‖(freqEquiv k : Fin 3 → ℝ)‖ ^ (-p)) at h
    simpa only [freqEquiv_coe] using h
  refine Summable.of_nonneg_of_le (fun n => Real.rpow_nonneg (norm_nonneg _) _) (fun n => ?_) hsup
  by_cases hn : n = 0
  · subst hn
    simp
  · have hxpos : 0 < ‖(fun i => (n i : ℝ))‖ := by
      rw [norm_pos_iff]
      intro hc
      apply hn
      ext i
      have := congrFun hc i
      simpa using this
    exact Real.rpow_le_rpow_of_nonpos hxpos (norm_freqPi_le_latticeVector n) (by linarith)

/-- The nonzero-lattice series in `ℝ≥0∞` coordinates. -/
def tailSum (s : ℝ) : ℝ≥0∞ :=
  ∑' n : {n : PeriodicFrequency // n ≠ 0},
    (ENNReal.ofReal ‖latticeVector n.1‖) ^ (-(3 + 2 * s))

/-- The uniform lattice-tail constant for support-difference radius `ρ`. -/
def tailConst (s ρ : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal (1 - ρ)) ^ (-(3 + 2 * s)) * tailSum s

theorem tailSum_lt_top {s : ℝ} (hs : 0 < s) : tailSum s < ⊤ := by
  have hp : (3 : ℝ) < 3 + 2 * s := by linarith
  have hsummable : Summable (fun n : {n : PeriodicFrequency // n ≠ 0} =>
      ‖latticeVector n.1‖ ^ (-(3 + 2 * s))) :=
    (summable_latticeVector_rpow hp).subtype {n | n ≠ 0}
  have hnn : ∀ n : {n : PeriodicFrequency // n ≠ 0},
      0 ≤ ‖latticeVector n.1‖ ^ (-(3 + 2 * s)) := fun n => Real.rpow_nonneg (norm_nonneg _) _
  have hpos : ∀ n : {n : PeriodicFrequency // n ≠ 0}, 0 < ‖latticeVector n.1‖ :=
    fun n => lt_of_lt_of_le one_pos (latticeVector_norm_ge_one n.2)
  have hcong : tailSum s =
      ENNReal.ofReal (∑' n : {n : PeriodicFrequency // n ≠ 0},
        ‖latticeVector n.1‖ ^ (-(3 + 2 * s))) := by
    rw [tailSum, ENNReal.ofReal_tsum_of_nonneg hnn hsummable]
    exact tsum_congr fun n => ENNReal.ofReal_rpow_of_pos (hpos n)
  rw [hcong]
  exact ENNReal.ofReal_lt_top

theorem tailConst_lt_top {s ρ : ℝ} (hs : 0 < s) (hρ : ρ < 1) : tailConst s ρ < ⊤ := by
  rw [tailConst]
  refine ENNReal.mul_lt_top ?_ (tailSum_lt_top hs)
  rw [ENNReal.ofReal_rpow_of_pos (show (0 : ℝ) < 1 - ρ by linarith)]
  exact ENNReal.ofReal_lt_top

/-- **Uniform lattice-tail bound.**  For `0 < s`, `0 < ρ < 1`, the nonzero
lattice tail is bounded by `tailConst s ρ` uniformly over `‖h‖ ≤ ρ`. -/
theorem latticeTail_le_tailConst {s ρ : ℝ} (hs : 0 ≤ s) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    {h : Space} (hh : ‖h‖ ≤ ρ) : latticeTail s h ≤ tailConst s ρ := by
  rw [latticeTail, tailConst, tailSum, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun n => ?_
  have hlv1 : (1 : ℝ) ≤ ‖latticeVector n.1‖ := latticeVector_norm_ge_one n.2
  have hlvpos : 0 < ‖latticeVector n.1‖ := lt_of_lt_of_le one_pos hlv1
  have h1ρ : (0 : ℝ) < 1 - ρ := by linarith
  have hsub : ‖latticeVector n.1‖ - ‖h‖ ≤ ‖h + latticeVector n.1‖ := by
    have := norm_sub_norm_le (latticeVector n.1) (-h)
    simpa [norm_neg, sub_neg_eq_add, add_comm] using this
  have hge : (1 - ρ) * ‖latticeVector n.1‖ ≤ ‖h + latticeVector n.1‖ := by
    nlinarith [hsub, hh, hlv1, hρ0, mul_nonneg hρ0.le (sub_nonneg.mpr hlv1)]
  simp only [fractionalRadialKernel]
  have hmono : (ENNReal.ofReal ‖h + latticeVector n.1‖) ^ (-(3 + 2 * s)) ≤
      (ENNReal.ofReal ((1 - ρ) * ‖latticeVector n.1‖)) ^ (-(3 + 2 * s)) := by
    rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
    refine ENNReal.inv_le_inv.mpr ?_
    exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hge) (by linarith)
  have hsplit : (ENNReal.ofReal ((1 - ρ) * ‖latticeVector n.1‖)) ^ (-(3 + 2 * s)) =
      (ENNReal.ofReal (1 - ρ)) ^ (-(3 + 2 * s)) *
        (ENNReal.ofReal ‖latticeVector n.1‖) ^ (-(3 + 2 * s)) := by
    rw [ENNReal.ofReal_mul h1ρ.le,
      ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top]
  exact hmono.trans (le_of_eq hsplit)

/-- The admissible-ball hypothesis forces the support-difference radius `2r`
below `1`: the closed cube has unit side and the ball fits inside its
interior. -/
theorem two_r_lt_one_of_closure_ball_subset {c : Space} {r : ℝ} (hr : 0 < r)
    (hball : closure (Metric.ball c r) ⊆ interior fundamentalCube) : 2 * r < 1 := by
  have hclosed : closure (Metric.ball c r) = Metric.closedBall c r :=
    closure_ball c (ne_of_gt hr)
  have he : ‖(EuclideanSpace.single (0 : Fin 3) r)‖ = r := by
    simp [abs_of_pos hr]
  have hplus : c + EuclideanSpace.single (0 : Fin 3) r ∈ interior fundamentalCube := by
    apply hball
    rw [hclosed, Metric.mem_closedBall, dist_eq_norm]
    simp [he]
  have hminus : c - EuclideanSpace.single (0 : Fin 3) r ∈ interior fundamentalCube := by
    apply hball
    rw [hclosed, Metric.mem_closedBall, dist_eq_norm]
    simp [he]
  rw [interior_fundamentalCube] at hplus hminus
  have hp := hplus 0
  have hm := hminus 0
  have ep : (c + EuclideanSpace.single (0 : Fin 3) r) 0 = c 0 + r := by
    simp
  have em : (c - EuclideanSpace.single (0 : Fin 3) r) 0 = c 0 - r := by
    simp
  rw [ep] at hp
  rw [em] at hm
  linarith [hp.2, hm.1]

/-! ## §3  Inhomogeneous ≤ `L²` + homogeneous on `T³` -/

/-- **Inhomogeneous/homogeneous comparison on `T³`.**  For `0 < s ≤ 1` and a
smooth periodic field `g`, the inhomogeneous `H^s(T³)` norm is bounded by the
sum of the coefficient-side `L²(T³)` norm (`periodicSobolevENorm 0`) and the
homogeneous `Ḣ^s(T³)` norm of the mean-free part.  This is the coefficientwise
subadditivity `(1+x)^{s/2} ≤ 1 + x^{s/2}` combined with the `ℓ²` triangle
inequality on the Fourier data. -/
theorem periodicSobolevENorm_le_l2_add_homogeneous {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    {g : SpatialField} (hg : ContDiff ℝ ∞ g) (hgp : IsPeriodicSpatial g) :
    periodicSobolevENorm s g ≤
      periodicSobolevENorm 0 g + periodicHomogeneousENorm s (meanZeroPartT g) := by
  classical
  have hgc : Continuous g := hg.continuous
  obtain ⟨As, hAs⟩ := exists_periodicDatum_smooth s hg hgp
  obtain ⟨A0, hA0⟩ := exists_periodicDatum_smooth 0 hg hgp
  obtain ⟨Ah, hAh, -⟩ := exists_homogeneous_datum hs hgp hg
  have hpwpos : ∀ k : PeriodicFrequency, 0 < periodicFrequencyWeight k := by
    intro k
    have hnn : (0 : ℝ) ≤ 4 * Real.pi ^ 2 * ∑ i : Fin 3, (k i : ℝ) ^ 2 := by positivity
    simp only [periodicFrequencyWeight]; linarith
  have hden : ∀ k : PeriodicFrequency, (0 : ℝ) < 1 + homogeneousDatumWeight s k := by
    intro k; have := homogeneousDatumWeight_nonneg s k; linarith
  set w : PeriodicFrequency → ℝ :=
    fun k => periodicFrequencyWeight k ^ (s / 2) / (1 + homogeneousDatumWeight s k) with hw_def
  have hprod : ∀ k, w k * (1 + homogeneousDatumWeight s k) =
      periodicFrequencyWeight k ^ (s / 2) := by
    intro k; rw [hw_def]; exact div_mul_cancel₀ _ (hden k).ne'
  have hwnn : ∀ k, 0 ≤ w k := fun k =>
    div_nonneg (Real.rpow_nonneg (hpwpos k).le _) (hden k).le
  have hsubadd : ∀ k, periodicFrequencyWeight k ^ (s / 2) ≤
      1 + homogeneousDatumWeight s k := by
    intro k
    have hx : (0 : ℝ) ≤ periodicAngularFrequencySq k := by
      unfold periodicAngularFrequencySq; positivity
    have hpw : periodicFrequencyWeight k = 1 + periodicAngularFrequencySq k := rfl
    by_cases hk : k = 0
    · subst hk
      have hpw0 : periodicFrequencyWeight (0 : PeriodicFrequency) = 1 := by
        have hz : ∑ i : Fin 3, ((0 : PeriodicFrequency) i : ℝ) ^ 2 = 0 := by simp
        rw [periodicFrequencyWeight, hz]; ring
      rw [homogeneousDatumWeight_zero, add_zero, hpw0, Real.one_rpow]
    · have hhk : homogeneousDatumWeight s k = periodicAngularFrequencySq k ^ (s / 2) :=
        if_neg hk
      rw [hpw, hhk]
      have h := Real.rpow_add_le_add_rpow (p := s / 2) (a := 1)
        (b := periodicAngularFrequencySq k) zero_le_one hx (by linarith) (by linarith)
      rwa [Real.one_rpow] at h
  have hw1 : ∀ k, |w k| ≤ 1 := by
    intro k
    rw [abs_of_nonneg (hwnn k), hw_def, div_le_one (hden k)]
    exact hsubadd k
  have hAhcoeff : ∀ (i : Fin 3) (k : PeriodicFrequency),
      Ah.1 i k = (homogeneousDatumWeight s k : ℂ) *
        periodicFourierCoeff (fun x => ((g x i : ℝ) : ℂ)) k := by
    intro i k
    rw [hAh.2.2.2 i k]
    by_cases hk : k = 0
    · subst hk; rw [homogeneousDatumWeight_zero]; simp
    · rw [smul_eq_mul, periodicFourierCoeff_meanZeroPart hgc i hk]
  have hA0coeff : ∀ (i : Fin 3) (k : PeriodicFrequency),
      A0.1 i k = periodicFourierCoeff (fun x => ((g x i : ℝ) : ℂ)) k := by
    intro i k
    rw [hA0.2.2 i k]
    simp
  have hAsEq : As.1 = reweightDatum w 1 zero_le_one hw1 (A0.1 + Ah.1) := by
    apply WithLp.ofLp_injective 2
    funext i
    ext k
    rw [hAs.2.2 i k, reweightDatum_apply,
      show (A0.1 + Ah.1) i k = A0.1 i k + Ah.1 i k from rfl, hA0coeff i k, hAhcoeff i k,
      Complex.real_smul, smul_eq_mul, ← hprod k]
    push_cast
    ring
  have hHnorm : periodicHomogeneousENorm s (meanZeroPartT g) = ‖Ah‖ₑ := by
    apply le_antisymm
    · exact iInf_le_of_le ⟨Ah, hAh⟩ le_rfl
    · refine le_iInf fun B => ?_
      rw [homogeneousDatum_unique B.1 Ah B.2 hAh]
  rw [periodicSobolevENorm_eq_datum hAs, periodicSobolevENorm_eq_datum hA0, hHnorm]
  calc ‖As‖ₑ = ‖As.1‖ₑ := rfl
    _ = ‖reweightDatum w 1 zero_le_one hw1 (A0.1 + Ah.1)‖ₑ := by rw [hAsEq]
    _ ≤ ENNReal.ofReal 1 * ‖A0.1 + Ah.1‖ₑ := reweightDatum_enorm_le' w 1 zero_le_one hw1 _
    _ = ‖A0.1 + Ah.1‖ₑ := by rw [ENNReal.ofReal_one, one_mul]
    _ ≤ ‖A0.1‖ₑ + ‖Ah.1‖ₑ := enorm_add_le _ _
    _ = ‖A0‖ₑ + ‖Ah‖ₑ := rfl

end NSFormalization.Section3.T13
