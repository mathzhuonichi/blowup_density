import NSFormalization.Section4.D01.OrderZeroSymbol
import NSFormalization.Section4.D01.Longitudinal

/-!
# Order-0 longitudinal (curl-free) Fourier identity — D01 · P2 · sub-lemma SL7b-β

`research/D01/REVIEW_ORDER_ZERO.md` §5 (the Lemma B plan) and
`research/D01/ATTEMPTS_ORDER_ZERO_CURL.md`.

Lane 094 (`OrderZeroSymbol.lean`) proved the order-0 **transverse** identity for a smooth
square-integrable divergence-free field, seeded from `MemLp z 2` + smoothness only, with *no*
integrability of the derivatives.  This module is the curl-free companion (Lemma B): for a smooth
square-integrable field whose spatial Jacobian is symmetric (`∂ᵢ z_j = ∂ⱼ z_i`, the invariant of
`∇p`), the order-0 datum is a.e. **longitudinal** `ξᵢ Â_j(ξ) = ξⱼ Â_i(ξ)`, hence fixed by the Leray
complement at order 0.

The two cases (divergence and curl) are unified through one cutoff/DCT machine written once here:

* `Cut.physical_weighted_pairing_zero` — the constant weight-matrix generalization of 094's
  `Cut.physical_pairing_zero`: for a smooth `L²` field and any constant matrix `w` with
  `∑ᵢⱼ w i j (∂ᵢ z_j) = 0` pointwise, `∑ᵢⱼ w i j ∫ (∂ᵢψ) z_j = 0` for every Schwartz `ψ`.  The
  divergence case is `w = δ` (a SIMP lane can re-derive 094's `physical_pairing_zero` from it); the
  curl case for a pair `(p,q)` is the antisymmetric `w` (`Cut.wAnti`).  The cutoff/DCT/`C/R`
  machinery is index-independent (per-index dominated convergence then a finite weighted sum), so
  this is a mechanical generalization.
* `Cut.physical_antisym_pairing_zero` — the antisymmetric instance: `∫ (∂ₚψ) z_q = ∫ (∂_qψ) z_p`.
* `tempered_antisym_eq` — hence `∂ₚ(z_q : 𝓢') = ∂_q(z_p : 𝓢')` as tempered distributions.
* `fourier_antisym` — Fourier transform (Mathlib `TemperedDistribution.fourier_lineDerivOp_eq`,
  `MeasureTheory.Lp.fourier_toTemperedDistribution_eq`) turns this into `ξₚ 𝓕z_q = ξ_q 𝓕z_p` a.e.
  via the fundamental lemma `ae_eq_zero_of_integral_contDiff_smul_eq_zero`.
* `orderZeroDatum_longitudinal_of_curl_free` — **Lemma B**, the datum-level statement matching lane
  089's `longitudinal_of_curl_free` shape, but for the order-0 `orderZeroDatum hz`
  (`OrderZeroDatum.lean`) of a bare `MemLp` smooth field: `ξᵢ Â_j = ξⱼ Â_i` a.e.
* `Leray.lerayComplement_zero_orderZeroDatum_eq_self` — the corollary via lane 089's
  `Leray.lerayComplement_eq_self_of_longitudinal 0`: `(I−P) datum⁰ = datum⁰`.

The dilation transport `longitudinal_of_longitudinal_symm` is the pairwise analogue of 094's
`transverse_of_transverse_symm` (which is stated only for the divergence sum); its proof body is
089's `longitudinal_of_curl_free` §2 transport with the concrete `A` replaced by a bare family
`g : Fin 3 → FourierData`.  **TODO (SIMP lane):** promote it (and 094's
`transverse_of_transverse_symm`, 079's `angularFrequencyDilation_coeFn`) to
`Paper3/AngularFourierDilation.lean` and rewrite 079/089/094 to consume it; and re-derive 094's
`physical_pairing_zero` from `physical_weighted_pairing_zero` at `w = δ`.  Those modules are frozen,
so this lane does not edit them.

No `sorry`, no `axiom`; `#print axioms` is standard (`research/D01/axioms_order_zero_curl.lean`).
-/

noncomputable section
open Set MeasureTheory FourierTransform NavierStokes.ProblemStatement
open scoped ENNReal SchwartzMap ContDiff LineDeriv
open NSFormalization.Section4.A03 (partialDeriv)

namespace NSFormalization.Section4.D01.Cut

variable {z : Space → Space}

/-! ## 0. Two-index cutoff helpers (re-derived: 094 exposes only the `k = j` case) -/

/-- Two-index `fderiv` of the complex component field (094's `fderiv_zc_eq` is only `k = j`). -/
theorem fderiv_zc_eq' (hsmooth : ContDiff ℝ ∞ z) (j k : Fin 3) (x : Space) :
    fderiv ℝ (zc z j) x (coordinateVector k) = ((partialDeriv k z x j : ℝ) : ℂ) := by
  rw [(hasFDeriv_zc hsmooth j x).fderiv, ContinuousLinearMap.comp_apply, Pj,
    ContinuousLinearMap.comp_apply]
  simp only [Complex.ofRealCLM_apply, EuclideanSpace.coe_proj]; rfl

/-- Two-index compact-support IBP (094 inlines this only at `k = j` inside `cs_pairing_zero`). -/
theorem cs_ibp (hsmooth : ContDiff ℝ ∞ z) {φ : Space → ℂ}
    (hφs : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (j k : Fin 3) :
    (∫ x, φ x • fderiv ℝ (zc z j) x (coordinateVector k))
      = -∫ x, (fderiv ℝ φ x (coordinateVector k)) • zc z j x := by
  have hφcont := hφs.continuous
  have hφdcont : Continuous (fun x => fderiv ℝ φ x (coordinateVector k)) :=
    (hφs.continuous_fderiv (by simp)).clm_apply continuous_const
  have hzcont : Continuous (zc z j) := (zc_smooth hsmooth j).continuous
  have hzdcont : Continuous (fun x => fderiv ℝ (zc z j) x (coordinateVector k)) :=
    ((zc_smooth hsmooth j).continuous_fderiv (by simp)).clm_apply continuous_const
  apply integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
  · exact (hφdcont.smul hzcont).integrable_of_hasCompactSupport
      ((hφc.fderiv_apply ℝ (coordinateVector k)).smul_right)
  · exact (hφcont.smul hzdcont).integrable_of_hasCompactSupport hφc.smul_right
  · exact (hφcont.smul hzcont).integrable_of_hasCompactSupport hφc.smul_right
  · exact fun x _ => (hφs.differentiable (by simp)).differentiableAt
  · exact fun x _ => ((zc_smooth hsmooth j).differentiable (by simp)).differentiableAt

/-! ## 1. The constant weight-matrix cutoff pairing -/

/-- Compact-support weighted pairing: with `∑ᵢⱼ w i j (∂ᵢ z_j) = 0` pointwise and `φ` a
compactly-supported smooth test, `∑ᵢⱼ w i j ∫ (∂ᵢφ) z_j = 0`.  Two-index IBP moves each derivative
onto `z`, and the weighted sum of the pointwise derivatives is `0`. -/
theorem cs_weighted_pairing_zero (hsmooth : ContDiff ℝ ∞ z) (w : Fin 3 → Fin 3 → ℂ)
    (hw : ∀ x, ∑ i, ∑ j, w i j * ((partialDeriv i z x j : ℝ) : ℂ) = 0)
    {φ : Space → ℂ} (hφs : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    (∑ i, ∑ j, w i j * ∫ x, (fderiv ℝ φ x (coordinateVector i)) • zc z j x) = 0 := by
  have hφcont := hφs.continuous
  have hzdcont : ∀ i j : Fin 3, Continuous (fun x => fderiv ℝ (zc z j) x (coordinateVector i)) :=
    fun i j => ((zc_smooth hsmooth j).continuous_fderiv (by simp)).clm_apply continuous_const
  have hintφz : ∀ i j : Fin 3,
      Integrable (fun x => φ x • fderiv ℝ (zc z j) x (coordinateVector i)) volume :=
    fun i j => (hφcont.smul (hzdcont i j)).integrable_of_hasCompactSupport hφc.smul_right
  have hibp : ∀ i j : Fin 3, (∫ x, (fderiv ℝ φ x (coordinateVector i)) • zc z j x)
      = -∫ x, φ x • fderiv ℝ (zc z j) x (coordinateVector i) :=
    fun i j => by rw [cs_ibp hsmooth hφs hφc j i, neg_neg]
  simp only [hibp, mul_neg, Finset.sum_neg_distrib, neg_eq_zero]
  have h1 : ∀ i j : Fin 3, w i j * (∫ x, φ x • fderiv ℝ (zc z j) x (coordinateVector i))
      = ∫ x, w i j • (φ x • fderiv ℝ (zc z j) x (coordinateVector i)) :=
    fun i j => by rw [integral_smul, smul_eq_mul]
  rw [show (∑ i, ∑ j, w i j * ∫ x, φ x • fderiv ℝ (zc z j) x (coordinateVector i))
        = ∑ ij : Fin 3 × Fin 3,
            ∫ x, w ij.1 ij.2 • (φ x • fderiv ℝ (zc z ij.2) x (coordinateVector ij.1))
      from by
        rw [Fintype.sum_prod_type]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => h1 i j]
  have hInt : ∀ ij : Fin 3 × Fin 3,
      Integrable
        (fun x => w ij.1 ij.2 • (φ x • fderiv ℝ (zc z ij.2) x (coordinateVector ij.1))) volume :=
    fun ij => (hintφz ij.1 ij.2).smul (w ij.1 ij.2)
  rw [← integral_finsetSum Finset.univ (fun ij _ => hInt ij)]
  rw [show (fun x => ∑ ij : Fin 3 × Fin 3,
        w ij.1 ij.2 • (φ x • fderiv ℝ (zc z ij.2) x (coordinateVector ij.1)))
        = (fun _ => (0 : ℂ)) from by
        funext x
        rw [Fintype.sum_prod_type]
        have e2 : (∑ i, ∑ j, w i j • (φ x • fderiv ℝ (zc z j) x (coordinateVector i)))
            = φ x * (∑ i, ∑ j, w i j * fderiv ℝ (zc z j) x (coordinateVector i)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [smul_eq_mul]; ring
        rw [e2]
        have e3 : (∑ i, ∑ j, w i j * fderiv ℝ (zc z j) x (coordinateVector i)) = 0 := by
          rw [show (∑ i, ∑ j, w i j * fderiv ℝ (zc z j) x (coordinateVector i))
                = ∑ i, ∑ j, w i j * ((partialDeriv i z x j : ℝ) : ℂ)
              from Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
                rw [fderiv_zc_eq' hsmooth j i x]]
          exact hw x
        rw [e3, mul_zero]]
  simp

/-- **The constant weight-matrix cutoff pairing.**  For a smooth square-integrable field and any
constant matrix `w` with `∑ᵢⱼ w i j (∂ᵢ z_j x) = 0` for every `x`, the frequency-space pairing
`∑ᵢⱼ w i j ∫ (∂ᵢψ) z_j = 0` for every Schwartz `ψ`.  No integrability of the derivatives is used:
integration by parts is done against a compactly-supported cutoff `χ(·/R)` (Mathlib `ContDiffBump`),
and the boundary term vanishes as `R → ∞` (`‖∇χ_R‖ ≤ C/R`, dominated convergence).  This is 094's
`Cut.physical_pairing_zero` machine with the divergence sum `∑ⱼ` replaced by the constant weighted
double sum `∑ᵢⱼ w i j`; the per-index dominated-convergence and boundary limits are unchanged. -/
theorem physical_weighted_pairing_zero (hz : MemLp z 2 volume) (hsmooth : ContDiff ℝ ∞ z)
    (w : Fin 3 → Fin 3 → ℂ)
    (hw : ∀ x, ∑ i, ∑ j, w i j * ((partialDeriv i z x j : ℝ) : ℂ) = 0) (ψ : SchwartzMap Space ℂ) :
    (∑ i, ∑ j, w i j * ∫ x, (∂_{coordinateVector i} ψ) x • zc z j x) = 0 := by
  obtain ⟨C, hC0, hCbound⟩ := exists_deriv_bound
  set cn : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹ with hcn
  set chic : ℕ → Space → ℂ := fun n x => ((chi n x : ℝ) : ℂ) with hchic
  have hchic_smooth : ∀ n, ContDiff ℝ ∞ (chic n) := fun n =>
    Complex.ofRealCLM.contDiff.comp (chi_smooth n)
  have hchic_cs : ∀ n, HasCompactSupport (chic n) := fun n =>
    (chi_cs n).comp_left (g := fun r : ℝ => ((r : ℝ) : ℂ)) (by simp)
  have hchic_cont : ∀ n, Continuous (chic n) := fun n => (hchic_smooth n).continuous
  have hchic_le1 : ∀ n x, ‖chic n x‖ ≤ 1 := by
    intro n x; rw [hchic]; simp only [Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (chi_nonneg n x)]; exact chi_le1 n x
  have hchic_tendsto : ∀ x, Filter.Tendsto (fun n => chic n x) Filter.atTop (nhds 1) := by
    intro x; apply Filter.Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [chi_eventually_one x] with n hn; rw [hchic]; simp [hn]
  have hchic_deriv : ∀ n x (i : Fin 3), ‖fderiv ℝ (chic n) x (coordinateVector i)‖ ≤ C * cn n := by
    intro n x i
    have hhfd : HasFDerivAt (chic n) (Complex.ofRealCLM.comp (fderiv ℝ (chi n) x)) x :=
      Complex.ofRealCLM.hasFDerivAt.comp x
        ((chi_smooth n).differentiable (by simp)).differentiableAt.hasFDerivAt
    rw [hhfd.fderiv, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, Complex.norm_real,
      Real.norm_eq_abs, ← Real.norm_eq_abs]
    exact chi_deriv_bound hCbound n x i
  have hzcont : ∀ j : Fin 3, Continuous (zc z j) := fun j => (zc_smooth hsmooth j).continuous
  have hdψcont : ∀ i : Fin 3, Continuous (fun x => (∂_{coordinateVector i} ψ) x) :=
    fun i => (∂_{coordinateVector i} ψ).continuous
  have hchicdcont : ∀ n (i : Fin 3), Continuous (fun x => fderiv ℝ (chic n) x (coordinateVector i)) :=
    fun n i => ((hchic_smooth n).continuous_fderiv (by simp)).clm_apply continuous_const
  have hMψ : ∀ j : Fin 3, Integrable (fun x => ψ x • zc z j x) volume := fun j =>
    memLp_one_iff_integrable.mp ((memLp_component hz j).smul (ψ.memLp 2))
  have hMdψ : ∀ i j : Fin 3, Integrable (fun x => (∂_{coordinateVector i} ψ) x • zc z j x) volume :=
    fun i j => memLp_one_iff_integrable.mp
      ((memLp_component hz j).smul ((∂_{coordinateVector i} ψ).memLp 2))
  have hBint : ∀ n (i j : Fin 3),
      Integrable (fun x => chic n x • ((∂_{coordinateVector i} ψ) x • zc z j x)) volume :=
    fun n i j => ((hchic_cont n).smul ((hdψcont i).smul (hzcont j))).integrable_of_hasCompactSupport
      ((hchic_cs n).smul_right)
  have hAint : ∀ n (i j : Fin 3),
      Integrable (fun x => ψ x • ((fderiv ℝ (chic n) x (coordinateVector i)) • zc z j x)) volume :=
    fun n i j => (ψ.continuous.smul ((hchicdcont n i).smul (hzcont j))).integrable_of_hasCompactSupport
      (((hchic_cs n).fderiv_apply ℝ (coordinateVector i)).smul_right.smul_left)
  have hterm : ∀ n (i j : Fin 3),
      (∫ x, (fderiv ℝ (fun y => chic n y * ψ y) x (coordinateVector i)) • zc z j x)
        = (∫ x, chic n x • ((∂_{coordinateVector i} ψ) x • zc z j x))
          + (∫ x, ψ x • ((fderiv ℝ (chic n) x (coordinateVector i)) • zc z j x)) := by
    intro n i j
    rw [← integral_add (hBint n i j) (hAint n i j)]
    apply integral_congr_ae
    filter_upwards with x
    have hc_fd : HasFDerivAt (chic n) (fderiv ℝ (chic n) x) x :=
      ((hchic_smooth n).differentiable (by simp)).differentiableAt.hasFDerivAt
    have hd_fd : HasFDerivAt (⇑ψ) (fderiv ℝ (⇑ψ) x) x :=
      ((ψ.smooth ⊤).differentiable (by simp)).differentiableAt.hasFDerivAt
    rw [show fderiv ℝ (fun y => chic n y * ψ y) x
          = chic n x • fderiv ℝ (⇑ψ) x + ψ x • fderiv ℝ (chic n) x from (hc_fd.mul hd_fd).fderiv,
      add_apply, smul_apply, smul_apply, add_smul, smul_assoc, smul_assoc,
      ← SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have hcancel : ∀ n, (∑ i, ∑ j, w i j * ∫ x, chic n x • ((∂_{coordinateVector i} ψ) x • zc z j x))
      + (∑ i, ∑ j, w i j * ∫ x, ψ x • ((fderiv ℝ (chic n) x (coordinateVector i)) • zc z j x)) = 0 := by
    intro n
    have hcsn := cs_weighted_pairing_zero hsmooth w hw
      (φ := fun x => chic n x * ψ x)
      ((hchic_smooth n).mul (ψ.smooth ⊤)) ((hchic_cs n).mul_right)
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by
        rw [hterm n i j, mul_add]))] at hcsn
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_add_distrib), Finset.sum_add_distrib] at hcsn
    exact hcsn
  have hBlim_ij : ∀ i j : Fin 3, Filter.Tendsto
      (fun n => ∫ x, chic n x • ((∂_{coordinateVector i} ψ) x • zc z j x))
      Filter.atTop (nhds (∫ x, (∂_{coordinateVector i} ψ) x • zc z j x)) := by
    intro i j
    apply MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun x => ‖(∂_{coordinateVector i} ψ) x • zc z j x‖)
    · exact fun n => ((hchic_cont n).smul ((hdψcont i).smul (hzcont j))).aestronglyMeasurable
    · exact (hMdψ i j).norm
    · intro n; filter_upwards with x; rw [norm_smul]
      calc ‖chic n x‖ * ‖(∂_{coordinateVector i} ψ) x • zc z j x‖
          ≤ 1 * ‖(∂_{coordinateVector i} ψ) x • zc z j x‖ :=
            mul_le_mul_of_nonneg_right (hchic_le1 n x) (norm_nonneg _)
        _ = ‖(∂_{coordinateVector i} ψ) x • zc z j x‖ := one_mul _
    · filter_upwards with x
      have := (hchic_tendsto x).smul (tendsto_const_nhds
        (x := (∂_{coordinateVector i} ψ) x • zc z j x))
      simpa using this
  have hAlim_ij : ∀ i j : Fin 3, Filter.Tendsto
      (fun n => ∫ x, ψ x • ((fderiv ℝ (chic n) x (coordinateVector i)) • zc z j x))
      Filter.atTop (nhds 0) := by
    intro i j
    apply squeeze_zero_norm (a := fun n => C * cn n * ∫ x, ‖ψ x • zc z j x‖)
    · intro n
      have hbound : ∀ x, ‖ψ x • ((fderiv ℝ (chic n) x (coordinateVector i)) • zc z j x)‖
          ≤ C * cn n * ‖ψ x • zc z j x‖ := by
        intro x
        rw [norm_smul, norm_smul, norm_smul]
        have h1 : ‖fderiv ℝ (chic n) x (coordinateVector i)‖ ≤ C * cn n := hchic_deriv n x i
        nlinarith [h1, norm_nonneg (ψ x), norm_nonneg (zc z j x),
          mul_nonneg (norm_nonneg (ψ x)) (norm_nonneg (zc z j x))]
      calc ‖∫ x, ψ x • ((fderiv ℝ (chic n) x (coordinateVector i)) • zc z j x)‖
          ≤ ∫ x, C * cn n * ‖ψ x • zc z j x‖ :=
            norm_integral_le_of_norm_le ((hMψ j).norm.const_mul (C * cn n))
              (Filter.Eventually.of_forall hbound)
        _ = C * cn n * ∫ x, ‖ψ x • zc z j x‖ := integral_const_mul _ _
    · have hcn0 : Filter.Tendsto (fun n : ℕ => cn n) Filter.atTop (nhds 0) := by
        rw [hcn]
        exact tendsto_inv_atTop_zero.comp
          (Filter.tendsto_atTop_add_const_right Filter.atTop 1 tendsto_natCast_atTop_atTop)
      have hcont : Continuous (fun t : ℝ => C * t * ∫ x, ‖ψ x • zc z j x‖) :=
        (continuous_const.mul continuous_id).mul continuous_const
      have htend := (hcont.tendsto 0).comp hcn0
      simpa only [Function.comp_def, mul_zero, zero_mul] using htend
  have hlim : Filter.Tendsto
      (fun n => (∑ i, ∑ j, w i j * ((∫ x, chic n x • ((∂_{coordinateVector i} ψ) x • zc z j x))
          + (∫ x, ψ x • ((fderiv ℝ (chic n) x (coordinateVector i)) • zc z j x)))))
      Filter.atTop
      (nhds (∑ i, ∑ j, w i j * ((∫ x, (∂_{coordinateVector i} ψ) x • zc z j x) + 0))) := by
    apply tendsto_finsetSum
    intro i _
    apply tendsto_finsetSum
    intro j _
    exact ((hBlim_ij i j).add (hAlim_ij i j)).const_mul (w i j)
  have hzeroseq : ∀ n, (∑ i, ∑ j, w i j * ((∫ x, chic n x • ((∂_{coordinateVector i} ψ) x • zc z j x))
          + (∫ x, ψ x • ((fderiv ℝ (chic n) x (coordinateVector i)) • zc z j x)))) = 0 := by
    intro n
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by rw [mul_add]))]
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_add_distrib), Finset.sum_add_distrib]
    exact hcancel n
  have hlim0 : Filter.Tendsto (fun _ : ℕ => (0 : ℂ)) Filter.atTop
      (nhds (∑ i, ∑ j, w i j * ((∫ x, (∂_{coordinateVector i} ψ) x • zc z j x) + 0))) :=
    Filter.Tendsto.congr (fun n => hzeroseq n) hlim
  have hval := tendsto_nhds_unique tendsto_const_nhds hlim0
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by rw [add_zero]))] at hval
  exact hval.symm

/-! ## 2. The antisymmetric weight and its pairing -/

/-- The antisymmetric weight for a pair `(p, q)`: `w p q = 1`, `w q p = -1`, else `0` (the zero
matrix when `p = q`). -/
def wAnti (p q : Fin 3) : Fin 3 → Fin 3 → ℂ :=
  fun i j => (if i = p ∧ j = q then (1 : ℂ) else 0) - (if i = q ∧ j = p then (1 : ℂ) else 0)

/-- Contracting `wAnti p q` against any `Fin 3 × Fin 3`-indexed family reads off the antisymmetric
combination `a p q - a q p`. -/
theorem sum_wAntisym_mul (p q : Fin 3) (a : Fin 3 → Fin 3 → ℂ) :
    (∑ i, ∑ j, wAnti p q i j * a i j) = a p q - a q p := by
  simp only [wAnti]
  fin_cases p <;> fin_cases q <;> simp [Fin.sum_univ_three] <;> ring

/-- **The antisymmetric cutoff pairing.**  For a smooth square-integrable curl-free field
(`∂ᵢ z_j = ∂ⱼ z_i`) and a pair `(p, q)`, `∫ (∂ₚψ) z_q = ∫ (∂_qψ) z_p` for every Schwartz `ψ`.  The
instance `w = wAnti p q` of `physical_weighted_pairing_zero`: its pointwise hypothesis is
`∂ₚ z_q − ∂_q z_p = 0` (curl-freeness). -/
theorem physical_antisym_pairing_zero (hz : MemLp z 2 volume) (hsmooth : ContDiff ℝ ∞ z)
    (hcurl : ∀ (i j : Fin 3) (x : Space), partialDeriv i z x j = partialDeriv j z x i)
    (p q : Fin 3) (ψ : SchwartzMap Space ℂ) :
    (∫ x, (∂_{coordinateVector p} ψ) x • zc z q x)
      - (∫ x, (∂_{coordinateVector q} ψ) x • zc z p x) = 0 := by
  have hw : ∀ x, ∑ i, ∑ j, wAnti p q i j * ((partialDeriv i z x j : ℝ) : ℂ) = 0 := by
    intro x
    rw [sum_wAntisym_mul p q (fun i j => ((partialDeriv i z x j : ℝ) : ℂ))]
    rw [show ((partialDeriv p z x q : ℝ) : ℂ) = ((partialDeriv q z x p : ℝ) : ℂ) from by
      rw [hcurl p q x], sub_self]
  have hmain := physical_weighted_pairing_zero hz hsmooth (wAnti p q) hw ψ
  rw [sum_wAntisym_mul] at hmain
  exact hmain

end NSFormalization.Section4.D01.Cut

namespace NSFormalization.Section4.D01
open Cut
open NSFormalization.Source.RealSobolev
open NSFormalization.Source (frequencyUnit frequencyUnit_pos)
open NSFormalization.Paper3

variable {z : Space → Space}

/-! ## 3. The distributional and Fourier antisymmetric identities -/

/-- Single-component distributional-Fourier identity (094's `fourier_transverse` `hterm`,
generalized so the derivative direction `d` is independent of the component `c`). -/
theorem fourier_lineDeriv_apply (hz : MemLp z 2 volume) (d c : Fin 3) (ψ : SchwartzMap Space ℂ) :
    (fourierCLM ℂ 𝓢'(Space, ℂ) (∂_{coordinateVector d}
        ((componentLp hz c : FourierData) : 𝓢'(Space, ℂ)))) ψ
      = (2 * (Real.pi : ℂ) * Complex.I) *
        ∫ ξ, ((ξ d : ℝ) : ℂ) * ψ ξ * (𝓕 (componentLp hz c) : FourierData) ξ := by
  rw [fourierCLM_apply, TemperedDistribution.fourier_lineDerivOp_eq,
    Lp.fourier_toTemperedDistribution_eq, smul_apply,
    TemperedDistribution.smulLeftCLM_apply_apply, Lp.toTemperedDistribution_apply, smul_eq_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards with ξ
  rw [SchwartzMap.smulLeftCLM_apply_apply (by fun_prop) ψ ξ,
    show (inner ℝ ξ (coordinateVector d) : ℝ) = ξ d from by
      rw [coordinateVector, real_inner_comm, EuclideanSpace.inner_single_left]; simp]
  push_cast
  ring

/-- **The distributional curl identity.**  For a smooth square-integrable curl-free field, the
distributional partials commute: `∂ₚ(z_q : 𝓢') = ∂_q(z_p : 𝓢')`.  No integrability of the
derivatives is used (`physical_antisym_pairing_zero`). -/
theorem tempered_antisym_eq (hz : MemLp z 2 volume) (hsmooth : ContDiff ℝ ∞ z)
    (hcurl : ∀ (i j : Fin 3) (x : Space), partialDeriv i z x j = partialDeriv j z x i)
    (p q : Fin 3) :
    (∂_{coordinateVector p} ((componentLp hz q : FourierData) : 𝓢'(Space, ℂ)))
      = (∂_{coordinateVector q} ((componentLp hz p : FourierData) : 𝓢'(Space, ℂ))) := by
  ext ψ
  have hstep : ∀ (d c : Fin 3),
      (∂_{coordinateVector d} ((componentLp hz c : FourierData) : 𝓢'(Space, ℂ))) ψ
        = -∫ x, (∂_{coordinateVector d} ψ) x • zc z c x := by
    intro d c
    rw [TemperedDistribution.lineDerivOp_apply_apply, map_neg, Lp.toTemperedDistribution_apply]
    congr 1
    apply integral_congr_ae
    filter_upwards [componentLp_ae hz c] with x hx
    rw [hx]; rfl
  rw [hstep p q, hstep q p]
  have hpair := physical_antisym_pairing_zero hz hsmooth hcurl p q ψ
  rw [sub_eq_zero] at hpair
  rw [hpair]

/-- **The frequency-longitudinal identity for the raw `L²` Fourier data.**  For a smooth
square-integrable curl-free field, `ξₚ 𝓕z_q(ξ) = ξ_q 𝓕z_p(ξ)` a.e. (stated as difference `= 0`). -/
theorem fourier_antisym (hz : MemLp z 2 volume) (hsmooth : ContDiff ℝ ∞ z)
    (hcurl : ∀ (i j : Fin 3) (x : Space), partialDeriv i z x j = partialDeriv j z x i)
    (p q : Fin 3) :
    ∀ᵐ ξ : Space ∂volume,
      ((ξ p : ℝ) : ℂ) * (𝓕 (componentLp hz q) : FourierData) ξ
        - ((ξ q : ℝ) : ℂ) * (𝓕 (componentLp hz p) : FourierData) ξ = 0 := by
  have hπ : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hloc : ∀ d c : Fin 3, LocallyIntegrable
      (fun ξ => ((ξ d : ℝ) : ℂ) * (𝓕 (componentLp hz c) : FourierData) ξ) volume := by
    intro d c
    have hg : LocallyIntegrableOn (⇑(𝓕 (componentLp hz c) : FourierData)) Set.univ volume :=
      locallyIntegrableOn_univ.mpr
        ((Lp.memLp (𝓕 (componentLp hz c))).locallyIntegrable (by norm_num))
    have hcoord : ContinuousOn (fun ξ : Space => ((ξ d : ℝ) : ℂ)) Set.univ :=
      (by fun_prop : Continuous (fun ξ : Space => ((ξ d : ℝ) : ℂ))).continuousOn
    have hmul := LocallyIntegrableOn.continuousOn_mul hg hcoord isOpen_univ.isLocallyClosed
    rwa [locallyIntegrableOn_univ] at hmul
  have hpair : ∀ ψ : SchwartzMap Space ℂ,
      (∫ ξ, ((ξ p : ℝ) : ℂ) * ψ ξ * (𝓕 (componentLp hz q) : FourierData) ξ)
        = ∫ ξ, ((ξ q : ℝ) : ℂ) * ψ ξ * (𝓕 (componentLp hz p) : FourierData) ξ := by
    intro ψ
    have heq := congrArg (fun U : 𝓢'(Space, ℂ) => (fourierCLM ℂ 𝓢'(Space, ℂ) U) ψ)
      (tempered_antisym_eq hz hsmooth hcurl p q)
    simp only [fourier_lineDeriv_apply hz p q, fourier_lineDeriv_apply hz q p] at heq
    exact mul_left_cancel₀ hπ heq
  apply ae_eq_zero_of_integral_contDiff_smul_eq_zero ((hloc p q).sub (hloc q p))
  intro g hg hgc
  have hg1 : HasCompactSupport (Complex.ofRealCLM ∘ g) := hgc.comp_left rfl
  have hg2 : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
  have hpp := hpair (hg1.toSchwartzMap hg2)
  have hInt_pq := (hloc p q).integrable_smul_left_of_hasCompactSupport hg.continuous hgc
  have hInt_qp := (hloc q p).integrable_smul_left_of_hasCompactSupport hg.continuous hgc
  have hpull : ∀ d c : Fin 3,
      (∫ ξ, g ξ • (((ξ d : ℝ) : ℂ) * (𝓕 (componentLp hz c) : FourierData) ξ))
        = ∫ ξ, ((ξ d : ℝ) : ℂ) * (hg1.toSchwartzMap hg2) ξ * (𝓕 (componentLp hz c) : FourierData) ξ := by
    intro d c
    apply integral_congr_ae; filter_upwards with ξ
    have hψξ : (hg1.toSchwartzMap hg2) ξ = ((g ξ : ℝ) : ℂ) := rfl
    rw [hψξ, Complex.real_smul]; ring
  simp only [Pi.sub_apply, smul_sub]
  rw [integral_sub hInt_pq hInt_qp, hpull p q, hpull q p, hpp, sub_self]

/-! ## 4. The datum-level longitudinal identity (Lemma B) -/

/-- Cycles-convention longitudinality for the order-0 datum: `ξᵢ (D⁻¹ Â_j) ξ = ξⱼ (D⁻¹ Â_i) ξ`. -/
theorem orderZeroDatum_longitudinal_symm (hz : MemLp z 2 volume) (hsmooth : ContDiff ℝ ∞ z)
    (hcurl : ∀ (i j : Fin 3) (x : Space), partialDeriv i z x j = partialDeriv j z x i) :
    ∀ᵐ ξ : Space ∂volume, ∀ i j : Fin 3,
      ((ξ i : ℝ) : ℂ) * (angularFrequencyDilation.symm (orderZeroDatum hz j : FourierData)) ξ
        = ((ξ j : ℝ) : ℂ) * (angularFrequencyDilation.symm (orderZeroDatum hz i : FourierData)) ξ := by
  refine ae_all_iff.2 fun i => ae_all_iff.2 fun j => ?_
  filter_upwards [fourier_antisym hz hsmooth hcurl i j,
    orderZeroDatum_symm_ae hz i, orderZeroDatum_symm_ae hz j] with ξ hf hi hj
  rw [hi, hj]
  exact sub_eq_zero.mp hf

/-- **Shared cycles→angular dilation transport (pairwise/longitudinal form).**  Given any family
`g : Fin 3 → FourierData` whose pre-dilation data are longitudinal a.e., the post-dilation (angular)
data are longitudinal a.e.  This is the pairwise analogue of 094's `transverse_of_transverse_symm`
(stated only for the divergence sum); the proof body is 089's `longitudinal_of_curl_free` §2
transport with the concrete datum `A` replaced by a bare `g`.  **TODO (SIMP lane):** promote to
`Paper3/AngularFourierDilation.lean` alongside the transverse form and rewrite 079/089/094. -/
theorem longitudinal_of_longitudinal_symm {g : Fin 3 → FourierData}
    (hstar : ∀ᵐ ξ : Space ∂volume, ∀ i j : Fin 3,
      ((ξ i : ℝ) : ℂ) * (angularFrequencyDilation.symm (g j)) ξ
        = ((ξ j : ℝ) : ℂ) * (angularFrequencyDilation.symm (g i)) ξ) :
    ∀ᵐ ξ : Space ∂volume, ∀ i j : Fin 3,
      ((ξ i : ℝ) : ℂ) * ((g j) ξ) = ((ξ j : ℝ) : ℂ) * ((g i) ξ) := by
  have hc0 : (0 : ℝ) < frequencyUnit := frequencyUnit_pos
  set κ : ℝ≥0∞ := ENNReal.ofReal (|(frequencyUnit⁻¹ ^ (Module.finrank ℝ Space))⁻¹|) with hκ
  have hMP : MeasurePreserving (fun ξ : Space => frequencyUnit⁻¹ • ξ) volume (κ • volume) :=
    ⟨(continuous_const_smul _).measurable, Measure.map_addHaar_smul volume (inv_ne_zero hc0.ne')⟩
  have hfwd : ∀ k : Fin 3, ∀ᵐ ξ : Space ∂volume,
      ((g k) ξ) = (frequencyUnit ^ (-3/2 : ℝ) : ℝ) •
        (angularFrequencyDilation.symm (g k)) (frequencyUnit⁻¹ • ξ) := by
    intro k
    have h1 := angularFrequencyDilation_coeFn (angularFrequencyDilation.symm (g k))
    rw [LinearIsometryEquiv.apply_symm_apply] at h1
    exact h1
  refine ae_all_iff.2 fun i => ae_all_iff.2 fun j => ?_
  have hpair : ∀ᵐ ξ : Space ∂volume,
      ((ξ i : ℝ) : ℂ) * (angularFrequencyDilation.symm (g j)) ξ
        = ((ξ j : ℝ) : ℂ) * (angularFrequencyDilation.symm (g i)) ξ := by
    filter_upwards [hstar] with ξ hξ; exact hξ i j
  have htrans : ∀ᵐ ξ : Space ∂volume,
      (((frequencyUnit⁻¹ • ξ) i : ℝ) : ℂ)
          * (angularFrequencyDilation.symm (g j)) (frequencyUnit⁻¹ • ξ)
        = (((frequencyUnit⁻¹ • ξ) j : ℝ) : ℂ)
          * (angularFrequencyDilation.symm (g i)) (frequencyUnit⁻¹ • ξ) :=
    hMP.quasiMeasurePreserving.ae (Measure.ae_smul_measure hpair κ)
  filter_upwards [htrans, hfwd i, hfwd j] with ξ ht hi hj
  have hsmul : ∀ k : Fin 3, ((frequencyUnit⁻¹ • ξ) k : ℝ) = frequencyUnit⁻¹ * ξ k := fun k => rfl
  rw [hi, hj]
  simp only [hsmul, Complex.ofReal_mul, Complex.real_smul] at ht ⊢
  have hcinv : ((frequencyUnit⁻¹ : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; exact inv_ne_zero hc0.ne'
  have hgs : ((ξ i : ℝ) : ℂ) * (angularFrequencyDilation.symm (g j)) (frequencyUnit⁻¹ • ξ)
      = ((ξ j : ℝ) : ℂ) * (angularFrequencyDilation.symm (g i)) (frequencyUnit⁻¹ • ξ) := by
    have hh : ((frequencyUnit⁻¹ : ℝ) : ℂ)
        * (((ξ i : ℝ) : ℂ) * (angularFrequencyDilation.symm (g j)) (frequencyUnit⁻¹ • ξ)
          - ((ξ j : ℝ) : ℂ) * (angularFrequencyDilation.symm (g i)) (frequencyUnit⁻¹ • ξ)) = 0 := by
      linear_combination ht
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hcinv)
  linear_combination ((frequencyUnit ^ (-3/2 : ℝ) : ℝ) : ℂ) * hgs

/-- **SL7b-β, Lemma B — the order-0 longitudinal identity.**  For a smooth square-integrable field
that is pointwise curl-free (`∂ᵢ z_j = ∂ⱼ z_i`), the order-0 angular Sobolev datum is longitudinal
at a.e. frequency: `ξᵢ Â_j(ξ) = ξⱼ Â_i(ξ)`, with *no* integrability of the derivatives assumed. -/
theorem orderZeroDatum_longitudinal_of_curl_free (hz : MemLp z 2 volume)
    (hsmooth : ContDiff ℝ ∞ z)
    (hcurl : ∀ (i j : Fin 3) (x : Space), partialDeriv i z x j = partialDeriv j z x i) :
    ∀ᵐ ξ : Space ∂volume, ∀ i j : Fin 3,
      ((ξ i : ℝ) : ℂ) * ((orderZeroDatum hz j : FourierData) ξ)
        = ((ξ j : ℝ) : ℂ) * ((orderZeroDatum hz i : FourierData) ξ) :=
  longitudinal_of_longitudinal_symm (orderZeroDatum_longitudinal_symm hz hsmooth hcurl)

end NSFormalization.Section4.D01

namespace NSFormalization.Section4.D01.Leray

variable {z : Space → Space}

/-- **The SL7b-β corollary.**  The order-0 Leray complement fixes the datum of a smooth
square-integrable curl-free field: `(I−P) datum⁰(z) = datum⁰(z)`.  Combines Lemma B
(`orderZeroDatum_longitudinal_of_curl_free`) with lane 089's
`Leray.lerayComplement_eq_self_of_longitudinal 0`. -/
theorem lerayComplement_zero_orderZeroDatum_eq_self (hz : MemLp z 2 volume)
    (hsmooth : ContDiff ℝ ∞ z)
    (hcurl : ∀ (i j : Fin 3) (x : Space), partialDeriv i z x j = partialDeriv j z x i) :
    lerayComplement 0 (orderZeroDatum hz) = orderZeroDatum hz :=
  lerayComplement_eq_self_of_longitudinal 0 (orderZeroDatum hz)
    (orderZeroDatum_longitudinal_of_curl_free hz hsmooth hcurl)

end NSFormalization.Section4.D01.Leray
