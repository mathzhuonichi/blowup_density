import NSFormalization.Section4.D01.OrderZeroDatum
import NSFormalization.Section4.D01.Transverse
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import NSFormalization.Section4.A03.OuterTameProduct

/-!
# Order-0 transverse (and cycles) Fourier identity — D01 · P2 · sub-lemma SL7b-α

`research/D01/P2_SPLIT.md` SL7 and `research/D01/REVIEW_TRANSVERSE.md` F5.

Lanes 079/089 proved the transverse/longitudinal Fourier identities for a `SmoothL2Field`
(all spatial jets in `L²`) at orders `≥ 1`, via `isSobolevDatum_partialDeriv`.  For `∂ₜu(t,·)`
and `∇p(t,·)` that all-jets wrapper is, under `MemForceR f`, equivalent to P2's own target, so the
seed of `eq:Rpressure` must be produced at **order 0** from `MemLp z 2` + pointwise smoothness
only — through distributional derivatives, with *no* integrability of the derivatives.

This module supplies exactly that for the transverse (divergence-free) case:

* `Cut.physical_pairing_zero` — the analytic heart: for a pointwise-divergence-free smooth `L²`
  field, `∑ⱼ ∫ (∂ⱼψ) zⱼ = 0` for every Schwartz `ψ`.  The derivatives are **not** assumed
  integrable; integration by parts is carried out against a compactly-supported cutoff
  `χ(·/R)` (Mathlib `ContDiffBump`), and the boundary term vanishes as `R → ∞`
  (`‖∇χ_R‖ ≤ C/R`, dominated convergence).  This is the step lanes 079/089 avoided by assuming
  all jets are `L²`.
* `tempered_div_zero` — hence the distributional divergence `∑ⱼ ∂ⱼ(zⱼ : 𝓢')` is the zero
  tempered distribution.
* `fourier_transverse` — Fourier transform (Mathlib `TemperedDistribution.fourier_lineDerivOp_eq`,
  `MeasureTheory.Lp.fourier_toTemperedDistribution_eq`) turns this into `∑ⱼ ξⱼ (𝓕 zⱼ)(ξ) = 0`
  a.e., via the fundamental lemma of the calculus of variations
  (`ae_eq_zero_of_integral_contDiff_smul_eq_zero`).
* `orderZeroDatum_transverse_of_divergence_free` — **Lemma A**, the datum-level statement matching
  lane 079's `transverse_of_divergence_free` shape, but for the order-0 `orderZeroDatum hz`
  (`OrderZeroDatum.lean`) of a bare `MemLp` smooth field: `∑ⱼ ξⱼ Âⱼ(ξ) = 0` a.e.

No `sorry`, no `axiom`; `#print axioms` is standard (`research/D01/axioms_order_zero.lean`).
-/


noncomputable section
open Set MeasureTheory FourierTransform NavierStokes.ProblemStatement
open scoped SchwartzMap ContDiff LineDeriv
open NSFormalization.Section4.A03 (partialDeriv)

namespace NSFormalization.Section4.D01.Cut

def bump : ContDiffBump (0 : Space) := ⟨1, 2, one_pos, one_lt_two⟩
theorem bump_smooth : ContDiff ℝ ∞ (bump : Space → ℝ) := bump.contDiff
theorem bump_cs : HasCompactSupport (bump : Space → ℝ) := bump.hasCompactSupport
theorem bump_le1 (x : Space) : (bump : Space → ℝ) x ≤ 1 := bump.le_one
theorem bump_nonneg (x : Space) : 0 ≤ (bump : Space → ℝ) x := bump.nonneg
theorem bump_one {x : Space} (hx : ‖x‖ ≤ 1) : (bump : Space → ℝ) x = 1 :=
  bump.one_of_mem_closedBall (by rw [mem_closedBall_zero_iff]; exact hx)

theorem norm_cv (j : Fin 3) : ‖coordinateVector j‖ = 1 := by
  rw [coordinateVector]; simp

/-- scaled real cutoff -/
def chi (n : ℕ) (x : Space) : ℝ := bump ((↑n + 1 : ℝ)⁻¹ • x)

theorem chi_smooth (n : ℕ) : ContDiff ℝ ∞ (chi n) :=
  bump_smooth.comp (contDiff_const_smul _)

theorem chi_cs (n : ℕ) : HasCompactSupport (chi n) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : Space) (2 * (↑n + 1)))
  intro x hx
  rw [mem_closedBall_zero_iff, not_le] at hx
  unfold chi
  apply bump.zero_of_le_dist
  rw [dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (by positivity)]
  show (2:ℝ) ≤ (↑n + 1 : ℝ)⁻¹ * ‖x‖
  rw [inv_mul_eq_div, le_div_iff₀ (by positivity : (0:ℝ) < ↑n + 1)]
  linarith [hx]

theorem chi_le1 (n : ℕ) (x : Space) : chi n x ≤ 1 := bump_le1 _
theorem chi_nonneg (n : ℕ) (x : Space) : 0 ≤ chi n x := bump_nonneg _

theorem chi_eventually_one (x : Space) :
    ∀ᶠ n in Filter.atTop, chi n x = 1 := by
  filter_upwards [Filter.eventually_ge_atTop ⌈‖x‖⌉₊] with n hn
  apply bump_one
  rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [inv_mul_le_one₀ (by positivity)]
  calc ‖x‖ ≤ (⌈‖x‖⌉₊ : ℝ) := Nat.le_ceil _
    _ ≤ (n : ℝ) := by exact_mod_cast hn
    _ ≤ (↑n + 1 : ℝ) := by linarith


theorem chi_deriv_bound {C : ℝ} (hC : ∀ y, ‖fderiv ℝ (bump : Space → ℝ) y‖ ≤ C)
    (n : ℕ) (x : Space) (j : Fin 3) :
    ‖fderiv ℝ (chi n) x (coordinateVector j)‖ ≤ C * ((n : ℝ) + 1)⁻¹ := by
  have hc0 : (0:ℝ) ≤ ((n:ℝ)+1)⁻¹ := by positivity
  have hLf : HasFDerivAt (fun y : Space => ((n:ℝ)+1)⁻¹ • y)
      (((n:ℝ)+1)⁻¹ • ContinuousLinearMap.id ℝ Space) x :=
    (((n:ℝ)+1)⁻¹ • ContinuousLinearMap.id ℝ Space).hasFDerivAt
  have hbf : HasFDerivAt (bump : Space → ℝ)
      (fderiv ℝ bump (((n:ℝ)+1)⁻¹ • x)) (((n:ℝ)+1)⁻¹ • x) :=
    (bump_smooth.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hchi : HasFDerivAt (chi n)
      ((fderiv ℝ bump (((n:ℝ)+1)⁻¹ • x)).comp
        (((n:ℝ)+1)⁻¹ • ContinuousLinearMap.id ℝ Space)) x :=
    hbf.comp x hLf
  rw [hchi.fderiv, ContinuousLinearMap.comp_apply]
  simp only [smul_apply, ContinuousLinearMap.id_apply, map_smul, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg hc0]
  calc ((n:ℝ)+1)⁻¹ * ‖fderiv ℝ bump (((n:ℝ)+1)⁻¹ • x) (coordinateVector j)‖
      ≤ ((n:ℝ)+1)⁻¹ * (‖fderiv ℝ bump (((n:ℝ)+1)⁻¹ • x)‖ * ‖coordinateVector j‖) :=
        mul_le_mul_of_nonneg_left ((fderiv ℝ bump _).le_opNorm _) hc0
    _ = ((n:ℝ)+1)⁻¹ * ‖fderiv ℝ bump (((n:ℝ)+1)⁻¹ • x)‖ := by rw [norm_cv, mul_one]
    _ ≤ ((n:ℝ)+1)⁻¹ * C := mul_le_mul_of_nonneg_left (hC _) hc0
    _ = C * ((n:ℝ)+1)⁻¹ := by ring


theorem exists_deriv_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : Space, ‖fderiv ℝ (bump : Space → ℝ) y‖ ≤ C := by
  have hcont : Continuous (fun y => ‖fderiv ℝ (bump : Space → ℝ) y‖) :=
    (bump_smooth.continuous_fderiv (by simp)).norm
  have hcs : HasCompactSupport (fun y => ‖fderiv ℝ (bump : Space → ℝ) y‖) :=
    (bump_cs.fderiv ℝ).norm
  obtain ⟨y0, hy0⟩ := hcont.exists_forall_ge_of_hasCompactSupport hcs
  exact ⟨‖fderiv ℝ (bump : Space → ℝ) y0‖, norm_nonneg _, hy0⟩

variable {z : Space → Space}

/-- component projection CLM -/
def Pj (j : Fin 3) : Space →L[ℝ] ℂ := Complex.ofRealCLM.comp (EuclideanSpace.proj j)

/-- complex j-th component field -/
def zc (z : Space → Space) (j : Fin 3) : Space → ℂ := fun x => ((z x j : ℝ) : ℂ)

theorem zc_eq (z : Space → Space) (j : Fin 3) : zc z j = ⇑(Pj j) ∘ z := by
  funext x; simp [zc, Pj, EuclideanSpace.proj]

theorem hasFDeriv_zc (hsmooth : ContDiff ℝ ∞ z) (j : Fin 3) (x : Space) :
    HasFDerivAt (zc z j) ((Pj j).comp (fderiv ℝ z x)) x := by
  rw [zc_eq]
  exact (Pj j).hasFDerivAt.comp x (hsmooth.differentiable (by simp)).differentiableAt.hasFDerivAt

theorem zc_smooth (hsmooth : ContDiff ℝ ∞ z) (j : Fin 3) : ContDiff ℝ ∞ (zc z j) := by
  rw [zc_eq]; exact (Pj j).contDiff.comp hsmooth

theorem fderiv_zc_eq (hsmooth : ContDiff ℝ ∞ z) (j : Fin 3) (x : Space) :
    fderiv ℝ (zc z j) x (coordinateVector j) = ((partialDeriv j z x j : ℝ) : ℂ) := by
  rw [(hasFDeriv_zc hsmooth j x).fderiv, ContinuousLinearMap.comp_apply, Pj,
    ContinuousLinearMap.comp_apply]
  simp only [Complex.ofRealCLM_apply, EuclideanSpace.coe_proj]
  rfl

theorem sum_fderiv_zc (hsmooth : ContDiff ℝ ∞ z)
    (hdiv : ∀ x, ∑ j : Fin 3, partialDeriv j z x j = 0) (x : Space) :
    (∑ j : Fin 3, fderiv ℝ (zc z j) x (coordinateVector j)) = 0 := by
  rw [Finset.sum_congr rfl (fun j _ => fderiv_zc_eq hsmooth j x)]
  rw [← Complex.ofReal_sum, hdiv x, Complex.ofReal_zero]


theorem cs_pairing_zero (hsmooth : ContDiff ℝ ∞ z)
    (hdiv : ∀ x, ∑ j : Fin 3, partialDeriv j z x j = 0)
    {φ : Space → ℂ} (hφs : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    (∑ j : Fin 3, ∫ x, (fderiv ℝ φ x (coordinateVector j)) • zc z j x) = 0 := by
  have hφcont := hφs.continuous
  have hφdcont : ∀ j : Fin 3, Continuous (fun x => fderiv ℝ φ x (coordinateVector j)) :=
    fun j => (hφs.continuous_fderiv (by simp)).clm_apply continuous_const
  have hzcont : ∀ j : Fin 3, Continuous (zc z j) := fun j => (zc_smooth hsmooth j).continuous
  have hzdcont : ∀ j : Fin 3, Continuous (fun x => fderiv ℝ (zc z j) x (coordinateVector j)) :=
    fun j => ((zc_smooth hsmooth j).continuous_fderiv (by simp)).clm_apply continuous_const
  have hibp : ∀ j : Fin 3, (∫ x, φ x • fderiv ℝ (zc z j) x (coordinateVector j))
      = -∫ x, (fderiv ℝ φ x (coordinateVector j)) • zc z j x := by
    intro j
    apply integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
    · exact ((hφdcont j).smul (hzcont j)).integrable_of_hasCompactSupport
        ((hφc.fderiv_apply ℝ (coordinateVector j)).smul_right)
    · exact (hφcont.smul (hzdcont j)).integrable_of_hasCompactSupport hφc.smul_right
    · exact (hφcont.smul (hzcont j)).integrable_of_hasCompactSupport hφc.smul_right
    · exact fun x _ => (hφs.differentiable (by simp)).differentiableAt
    · exact fun x _ => ((zc_smooth hsmooth j).differentiable (by simp)).differentiableAt
  have hpair : ∀ j : Fin 3,
      (∫ x, (fderiv ℝ φ x (coordinateVector j)) • zc z j x)
        + (∫ x, φ x • fderiv ℝ (zc z j) x (coordinateVector j)) = 0 :=
    fun j => by rw [hibp j]; ring
  have hzero : (∑ j : Fin 3, ∫ x, φ x • fderiv ℝ (zc z j) x (coordinateVector j)) = 0 := by
    have hcancel : (∫ x, ∑ j : Fin 3, φ x • fderiv ℝ (zc z j) x (coordinateVector j)) = 0 := by
      have heq : (fun x => ∑ j : Fin 3, φ x • fderiv ℝ (zc z j) x (coordinateVector j))
          = (fun _ => (0:ℂ)) := by
        funext x; rw [← Finset.smul_sum, sum_fderiv_zc hsmooth hdiv x, smul_zero]
      rw [heq]; simp
    rw [integral_finsetSum Finset.univ
      (f := fun j x => φ x • fderiv ℝ (zc z j) x (coordinateVector j))
      (fun j _ =>
        (hφcont.smul (hzdcont j)).integrable_of_hasCompactSupport hφc.smul_right)] at hcancel
    exact hcancel
  have hsum0 : (∑ j : Fin 3,
      ((∫ x, (fderiv ℝ φ x (coordinateVector j)) • zc z j x)
        + (∫ x, φ x • fderiv ℝ (zc z j) x (coordinateVector j)))) = 0 :=
    Finset.sum_eq_zero (fun j _ => hpair j)
  rw [Finset.sum_add_distrib, hzero, add_zero] at hsum0
  exact hsum0

theorem physical_pairing_zero (hz : MemLp z 2 volume) (hsmooth : ContDiff ℝ ∞ z)
    (hdiv : ∀ x, ∑ j : Fin 3, partialDeriv j z x j = 0) (ψ : SchwartzMap Space ℂ) :
    (∑ j : Fin 3, ∫ x, (∂_{coordinateVector j} ψ) x • zc z j x) = 0 := by
  obtain ⟨C, hC0, hCbound⟩ := exists_deriv_bound
  set cn : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹ with hcn
  set chic : ℕ → Space → ℂ := fun n x => ((chi n x : ℝ) : ℂ) with hchic
  -- basic facts about chic
  have hchic_smooth : ∀ n, ContDiff ℝ ∞ (chic n) := fun n =>
    Complex.ofRealCLM.contDiff.comp (chi_smooth n)
  have hchic_cs : ∀ n, HasCompactSupport (chic n) := fun n =>
    (chi_cs n).comp_left (g := fun r : ℝ => ((r : ℝ) : ℂ)) (by simp)
  have hchic_cont : ∀ n, Continuous (chic n) := fun n => (hchic_smooth n).continuous
  have hchic_le1 : ∀ n x, ‖chic n x‖ ≤ 1 := by
    intro n x
    rw [hchic]; simp only [Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (chi_nonneg n x)]; exact chi_le1 n x
  have hchic_tendsto : ∀ x, Filter.Tendsto (fun n => chic n x) Filter.atTop (nhds 1) := by
    intro x
    apply Filter.Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [chi_eventually_one x] with n hn
    rw [hchic]; simp [hn]
  -- derivative norm bound for chic
  have hchic_deriv : ∀ n x (j : Fin 3), ‖fderiv ℝ (chic n) x (coordinateVector j)‖ ≤ C * cn n := by
    intro n x j
    have hhfd : HasFDerivAt (chic n)
        (Complex.ofRealCLM.comp (fderiv ℝ (chi n) x)) x :=
      Complex.ofRealCLM.hasFDerivAt.comp x
        ((chi_smooth n).differentiable (by simp)).differentiableAt.hasFDerivAt
    rw [hhfd.fderiv, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, Complex.norm_real,
      Real.norm_eq_abs, ← Real.norm_eq_abs]
    exact chi_deriv_bound hCbound n x j
  -- SchwartzMap directional derivative and integrability facts
  have hMψ : ∀ j : Fin 3, Integrable (fun x => ψ x • zc z j x) volume := fun j =>
    memLp_one_iff_integrable.mp ((memLp_component hz j).smul (ψ.memLp 2))
  have hMdψ : ∀ j : Fin 3, Integrable (fun x => (∂_{coordinateVector j} ψ) x • zc z j x) volume :=
    fun j => memLp_one_iff_integrable.mp
      ((memLp_component hz j).smul ((∂_{coordinateVector j} ψ).memLp 2))
  -- continuity facts
  have hzcont : ∀ j : Fin 3, Continuous (zc z j) := fun j => (zc_smooth hsmooth j).continuous
  have hdψcont : ∀ j : Fin 3, Continuous (fun x => (∂_{coordinateVector j} ψ) x) :=
    fun j => (∂_{coordinateVector j} ψ).continuous
  have hchicdcont : ∀ n (j : Fin 3), Continuous (fun x => fderiv ℝ (chic n) x (coordinateVector j)) :=
    fun n j => ((hchic_smooth n).continuous_fderiv (by simp)).clm_apply continuous_const
  -- integrability of the split parts (both by compact support)
  have hBint : ∀ n (j : Fin 3),
      Integrable (fun x => chic n x • ((∂_{coordinateVector j} ψ) x • zc z j x)) volume :=
    fun n j => ((hchic_cont n).smul ((hdψcont j).smul (hzcont j))).integrable_of_hasCompactSupport
      ((hchic_cs n).smul_right)
  have hAint : ∀ n (j : Fin 3),
      Integrable (fun x => ψ x • ((fderiv ℝ (chic n) x (coordinateVector j)) • zc z j x)) volume :=
    fun n j => (ψ.continuous.smul ((hchicdcont n j).smul (hzcont j))).integrable_of_hasCompactSupport
      (((hchic_cs n).fderiv_apply ℝ (coordinateVector j)).smul_right.smul_left)
  -- Leibniz split of each term
  have hterm : ∀ n (j : Fin 3),
      (∫ x, (fderiv ℝ (fun y => chic n y * ψ y) x (coordinateVector j)) • zc z j x)
        = (∫ x, chic n x • ((∂_{coordinateVector j} ψ) x • zc z j x))
          + (∫ x, ψ x • ((fderiv ℝ (chic n) x (coordinateVector j)) • zc z j x)) := by
    intro n j
    rw [← integral_add (hBint n j) (hAint n j)]
    apply integral_congr_ae
    filter_upwards with x
    have hc_fd : HasFDerivAt (chic n) (fderiv ℝ (chic n) x) x :=
      ((hchic_smooth n).differentiable (by simp)).differentiableAt.hasFDerivAt
    have hd_fd : HasFDerivAt (⇑ψ) (fderiv ℝ (⇑ψ) x) x :=
      ((ψ.smooth ⊤).differentiable (by simp)).differentiableAt.hasFDerivAt
    rw [show fderiv ℝ (fun y => chic n y * ψ y) x
          = chic n x • fderiv ℝ (⇑ψ) x + ψ x • fderiv ℝ (chic n) x from (hc_fd.mul hd_fd).fderiv,
      add_apply, smul_apply,
      smul_apply, add_smul, smul_assoc, smul_assoc,
      ← SchwartzMap.lineDerivOp_apply_eq_fderiv]
  -- the per-n cancellation
  have hcancel : ∀ n, (∑ j : Fin 3, ∫ x, chic n x • ((∂_{coordinateVector j} ψ) x • zc z j x))
      + (∑ j : Fin 3, ∫ x, ψ x • ((fderiv ℝ (chic n) x (coordinateVector j)) • zc z j x)) = 0 := by
    intro n
    have hcsn := cs_pairing_zero hsmooth hdiv
      (φ := fun x => chic n x * ψ x)
      ((hchic_smooth n).mul (ψ.smooth ⊤)) ((hchic_cs n).mul_right)
    rw [Finset.sum_congr rfl (fun j _ => hterm n j), Finset.sum_add_distrib] at hcsn
    exact hcsn
  -- the B-limit (dominated convergence)
  have hBlim : Filter.Tendsto
      (fun n => ∑ j : Fin 3, ∫ x, chic n x • ((∂_{coordinateVector j} ψ) x • zc z j x))
      Filter.atTop
      (nhds (∑ j : Fin 3, ∫ x, (∂_{coordinateVector j} ψ) x • zc z j x)) := by
    apply tendsto_finsetSum
    intro j _
    apply MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun x => ‖(∂_{coordinateVector j} ψ) x • zc z j x‖)
    · exact fun n => ((hchic_cont n).smul ((hdψcont j).smul (hzcont j))).aestronglyMeasurable
    · exact (hMdψ j).norm
    · intro n
      filter_upwards with x
      rw [norm_smul]
      calc ‖chic n x‖ * ‖(∂_{coordinateVector j} ψ) x • zc z j x‖
          ≤ 1 * ‖(∂_{coordinateVector j} ψ) x • zc z j x‖ :=
            mul_le_mul_of_nonneg_right (hchic_le1 n x) (norm_nonneg _)
        _ = ‖(∂_{coordinateVector j} ψ) x • zc z j x‖ := one_mul _
    · filter_upwards with x
      have := (hchic_tendsto x).smul (tendsto_const_nhds
        (x := (∂_{coordinateVector j} ψ) x • zc z j x))
      simpa using this
  -- the A-limit (goes to zero)
  have hAlim : Filter.Tendsto
      (fun n => ∑ j : Fin 3, ∫ x, ψ x • ((fderiv ℝ (chic n) x (coordinateVector j)) • zc z j x))
      Filter.atTop (nhds 0) := by
    apply squeeze_zero_norm
      (a := fun n => C * cn n * ∑ j : Fin 3, ∫ x, ‖ψ x • zc z j x‖)
    · intro n
      refine (norm_sum_le _ _).trans ?_
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      have hbound : ∀ x, ‖ψ x • ((fderiv ℝ (chic n) x (coordinateVector j)) • zc z j x)‖
          ≤ C * cn n * ‖ψ x • zc z j x‖ := by
        intro x
        rw [norm_smul, norm_smul, norm_smul]
        have h1 : ‖fderiv ℝ (chic n) x (coordinateVector j)‖ ≤ C * cn n := hchic_deriv n x j
        nlinarith [h1, norm_nonneg (ψ x), norm_nonneg (zc z j x),
          mul_nonneg (norm_nonneg (ψ x)) (norm_nonneg (zc z j x))]
      calc ‖∫ x, ψ x • ((fderiv ℝ (chic n) x (coordinateVector j)) • zc z j x)‖
          ≤ ∫ x, C * cn n * ‖ψ x • zc z j x‖ :=
            norm_integral_le_of_norm_le ((hMψ j).norm.const_mul (C * cn n))
              (Filter.Eventually.of_forall hbound)
        _ = C * cn n * ∫ x, ‖ψ x • zc z j x‖ := integral_const_mul _ _
    · have hcn0 : Filter.Tendsto (fun n : ℕ => cn n) Filter.atTop (nhds 0) := by
        rw [hcn]
        exact tendsto_inv_atTop_zero.comp
          (Filter.tendsto_atTop_add_const_right Filter.atTop 1 tendsto_natCast_atTop_atTop)
      have hcont : Continuous
          (fun t : ℝ => C * t * ∑ j : Fin 3, ∫ x, ‖ψ x • zc z j x‖) :=
        (continuous_const.mul continuous_id).mul continuous_const
      have htend := (hcont.tendsto 0).comp hcn0
      simpa only [Function.comp_def, mul_zero, zero_mul] using htend
  -- conclude by uniqueness of limits
  have hBlim0 : Filter.Tendsto
      (fun n => ∑ j : Fin 3, ∫ x, chic n x • ((∂_{coordinateVector j} ψ) x • zc z j x))
      Filter.atTop (nhds 0) := by
    have heq : (fun n => ∑ j : Fin 3, ∫ x, chic n x • ((∂_{coordinateVector j} ψ) x • zc z j x))
        = (fun n => -(∑ j : Fin 3, ∫ x, ψ x • ((fderiv ℝ (chic n) x (coordinateVector j)) • zc z j x))) := by
      funext n; exact eq_neg_of_add_eq_zero_left (hcancel n)
    rw [heq]
    simpa using hAlim.neg
  exact tendsto_nhds_unique hBlim hBlim0

end NSFormalization.Section4.D01.Cut
namespace NSFormalization.Section4.D01
open Cut
open NSFormalization.Source.RealSobolev
open NSFormalization.Paper3

variable {z : Space → Space}

/-- The distributional divergence of a pointwise-divergence-free smooth `L²` field is the zero
tempered distribution.  No integrability of the derivatives is used: integration by parts is done
against a compactly-supported cutoff (`physical_pairing_zero`). -/
theorem tempered_div_zero (hz : MemLp z 2 volume) (hsmooth : ContDiff ℝ ∞ z)
    (hdiv : ∀ x, ∑ j : Fin 3, partialDeriv j z x j = 0) :
    (∑ j : Fin 3, ∂_{coordinateVector j}
      ((componentLp hz j : FourierData) : 𝓢'(Space, ℂ))) = 0 := by
  ext ψ
  rw [sum_apply, IsZeroApply.zero_apply]
  have hstep : ∀ j : Fin 3,
      (∂_{coordinateVector j} ((componentLp hz j : FourierData) : 𝓢'(Space, ℂ))) ψ
        = -∫ x, (∂_{coordinateVector j} ψ) x • zc z j x := by
    intro j
    rw [TemperedDistribution.lineDerivOp_apply_apply, map_neg, Lp.toTemperedDistribution_apply]
    congr 1
    apply integral_congr_ae
    filter_upwards [componentLp_ae hz j] with x hx
    rw [hx]; rfl
  rw [Finset.sum_congr rfl (fun j _ => hstep j)]
  rw [Finset.sum_neg_distrib, physical_pairing_zero hz hsmooth hdiv ψ, neg_zero]

/-- **(★) — the frequency-transverse identity for the raw `L²` Fourier data.** -/
theorem fourier_transverse (hz : MemLp z 2 volume) (hsmooth : ContDiff ℝ ∞ z)
    (hdiv : ∀ x, ∑ j : Fin 3, partialDeriv j z x j = 0) :
    ∀ᵐ ξ : Space ∂volume,
      ∑ j : Fin 3, ((ξ j : ℝ) : ℂ) * (𝓕 (componentLp hz j) : FourierData) ξ = 0 := by
  have hD := tempered_div_zero hz hsmooth hdiv
  have hπ : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hlocterm : ∀ j : Fin 3, LocallyIntegrable
      (fun ξ => ((ξ j : ℝ) : ℂ) * (𝓕 (componentLp hz j) : FourierData) ξ) volume := by
    intro j
    have hg : LocallyIntegrableOn (⇑(𝓕 (componentLp hz j) : FourierData)) Set.univ volume :=
      locallyIntegrableOn_univ.mpr
        ((Lp.memLp (𝓕 (componentLp hz j))).locallyIntegrable (by norm_num))
    have hcoord : ContinuousOn (fun ξ : Space => ((ξ j : ℝ) : ℂ)) Set.univ :=
      (by fun_prop : Continuous (fun ξ : Space => ((ξ j : ℝ) : ℂ))).continuousOn
    have hmul := LocallyIntegrableOn.continuousOn_mul hg hcoord isOpen_univ.isLocallyClosed
    rwa [locallyIntegrableOn_univ] at hmul
  -- the pairing identity for every Schwartz test
  have hpair : ∀ ψ : SchwartzMap Space ℂ,
      (∑ j : Fin 3, ∫ ξ, ((ξ j : ℝ) : ℂ) * ψ ξ * (𝓕 (componentLp hz j) : FourierData) ξ) = 0 := by
    intro ψ
    have hz0 : fourierCLM ℂ 𝓢'(Space, ℂ)
        (∑ j : Fin 3, ∂_{coordinateVector j}
          ((componentLp hz j : FourierData) : 𝓢'(Space, ℂ))) = 0 := by
      rw [hD, map_zero]
    rw [map_sum] at hz0
    have happ := congrArg (fun U : 𝓢'(Space, ℂ) => U ψ) hz0
    simp only [sum_apply, IsZeroApply.zero_apply] at happ
    have hterm : ∀ j : Fin 3,
        (fourierCLM ℂ 𝓢'(Space, ℂ) (∂_{coordinateVector j}
          ((componentLp hz j : FourierData) : 𝓢'(Space, ℂ)))) ψ
        = (2 * (Real.pi : ℂ) * Complex.I) *
          ∫ ξ, ((ξ j : ℝ) : ℂ) * ψ ξ * (𝓕 (componentLp hz j) : FourierData) ξ := by
      intro j
      rw [fourierCLM_apply, TemperedDistribution.fourier_lineDerivOp_eq,
        Lp.fourier_toTemperedDistribution_eq, smul_apply,
        TemperedDistribution.smulLeftCLM_apply_apply, Lp.toTemperedDistribution_apply, smul_eq_mul]
      congr 1
      apply integral_congr_ae
      filter_upwards with ξ
      rw [SchwartzMap.smulLeftCLM_apply_apply (by fun_prop) ψ ξ,
        show (inner ℝ ξ (coordinateVector j) : ℝ) = ξ j from by
          rw [coordinateVector, real_inner_comm, EuclideanSpace.inner_single_left]; simp]
      push_cast
      ring
    rw [Finset.sum_congr rfl (fun j _ => hterm j), ← Finset.mul_sum] at happ
    exact (mul_eq_zero.mp happ).resolve_left hπ
  -- fundamental lemma of the calculus of variations
  apply ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (locallyIntegrable_finsetSum Finset.univ (fun j _ => hlocterm j))
  intro g hg hgc
  have hg1 : HasCompactSupport (Complex.ofRealCLM ∘ g) := hgc.comp_left rfl
  have hg2 : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
  have hpp := hpair (hg1.toSchwartzMap hg2)
  rw [show (fun ξ => g ξ • ∑ j : Fin 3, ((ξ j : ℝ) : ℂ) * (𝓕 (componentLp hz j) : FourierData) ξ)
        = (fun ξ => ∑ j : Fin 3, g ξ • (((ξ j : ℝ) : ℂ) * (𝓕 (componentLp hz j) : FourierData) ξ))
      from by funext ξ; rw [Finset.smul_sum]]
  rw [integral_finsetSum Finset.univ
      (f := fun j ξ => g ξ • (((ξ j : ℝ) : ℂ) * (𝓕 (componentLp hz j) : FourierData) ξ))
      (fun j _ => (hlocterm j).integrable_smul_left_of_hasCompactSupport hg.continuous hgc), ← hpp]
  apply Finset.sum_congr rfl
  intro j _
  apply integral_congr_ae
  filter_upwards with ξ
  have hψξ : (hg1.toSchwartzMap hg2) ξ = ((g ξ : ℝ) : ℂ) := rfl
  rw [hψξ, Complex.real_smul]
  ring

/-! ## The datum-level transverse identity (Lemma A) -/

theorem angularWeightSymbol_zero (ξ : Space) : angularWeightSymbol 0 ξ = 1 := by
  simp only [angularWeightSymbol, sobolevBesselWeight]; norm_num

theorem orderZeroDatum_coe (hz : MemLp z 2 volume) (j : Fin 3) :
    (orderZeroDatum hz j : FourierData) = cyclesToAngular 0 (𝓕 (componentLp hz j)) := by
  show cyclesToAngular 0 (realProjection (𝓕 (componentLp hz j))) = _
  rw [realProjection_eq_self (fourier_componentLp_mem hz j)]

theorem orderZeroDatum_symm_ae (hz : MemLp z 2 volume) (j : Fin 3) :
    (angularFrequencyDilation.symm (orderZeroDatum hz j : FourierData) : Space → ℂ)
      =ᵐ[volume] ⇑(𝓕 (componentLp hz j) : FourierData) := by
  have hcoe : angularFrequencyDilation.symm (orderZeroDatum hz j : FourierData)
      = angularWeightEquiv 0 (𝓕 (componentLp hz j)) := by
    rw [orderZeroDatum_coe hz j]
    show angularFrequencyDilation.symm
      (angularFrequencyDilation (angularWeightEquiv 0 (𝓕 (componentLp hz j)))) = _
    rw [LinearIsometryEquiv.symm_apply_apply]
  rw [hcoe]
  filter_upwards [angularWeightEquiv_coeFn 0 (𝓕 (componentLp hz j))] with ξ hξ
  rw [hξ, angularWeightSymbol_zero, one_mul]

/-- Cycles-convention transversality for the order-0 datum. -/
theorem orderZeroDatum_transverse_symm (hz : MemLp z 2 volume) (hsmooth : ContDiff ℝ ∞ z)
    (hdiv : ∀ x, ∑ j : Fin 3, partialDeriv j z x j = 0) :
    ∀ᵐ ξ : Space ∂volume,
      ∑ j : Fin 3, ((ξ j : ℝ) : ℂ) *
        (angularFrequencyDilation.symm (orderZeroDatum hz j : FourierData)) ξ = 0 := by
  filter_upwards [fourier_transverse hz hsmooth hdiv,
    orderZeroDatum_symm_ae hz 0, orderZeroDatum_symm_ae hz 1, orderZeroDatum_symm_ae hz 2]
    with ξ hf h0 h1 h2
  rw [Fin.sum_univ_three, h0, h1, h2]
  rw [Fin.sum_univ_three] at hf
  exact hf

/-- Moved to `Paper3/AngularFourierDilation.lean` (lane 109); alias kept for downstream.

**Shared cycles→angular dilation transport.** Transports a.e. transversality of the
pre-dilation data `g` to the post-dilation (angular) data. -/
alias transverse_of_transverse_symm := NSFormalization.Paper3.transverse_of_transverse_symm

/-- **SL7b-α, Lemma A — the order-0 transverse identity.**  For a smooth square-integrable field
that is pointwise divergence-free, the order-0 angular Sobolev datum is transverse at a.e.
frequency, with *no* integrability of the derivatives assumed.  This seeds `eq:Rpressure` at
order 0 non-circularly.  The cycles form (`orderZeroDatum_transverse_symm`) is carried to the
angular convention by the shared `transverse_of_transverse_symm`. -/
theorem orderZeroDatum_transverse_of_divergence_free (hz : MemLp z 2 volume)
    (hsmooth : ContDiff ℝ ∞ z) (hdiv : ∀ x, ∑ j : Fin 3, partialDeriv j z x j = 0) :
    ∀ᵐ ξ : Space ∂volume,
      ∑ j : Fin 3, ((ξ j : ℝ) : ℂ) * ((orderZeroDatum hz j : FourierData) ξ) = 0 :=
  transverse_of_transverse_symm (orderZeroDatum_transverse_symm hz hsmooth hdiv)
