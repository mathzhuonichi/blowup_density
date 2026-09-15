import NSFormalization.Section4.C01.Enstrophy
import NSFormalization.Section4.C01.EnergyBounds
import NSFormalization.Section4.C01.Trilinear
import NSFormalization.Section4.A04.Continuity
import NSFormalization.Section4.R43.Pieces

/-!
# Section 4 · C01 rows E6/E7 — the enstrophy identity and the local H² integral

This module continues `Enstrophy.lean`'s unconditional differentiation formula

`(‖∇u‖₂²)' = -2 ⟪Δu, ∂ₜu⟫`

by substituting the carrier-B momentum equation.  The pressure term vanishes because the
Laplacian of a smooth divergence-free field is again divergence free; the latter is proved
from `Δu = ∇ div u - curl curl u` and `div curl = 0`.  The resulting identity keeps the
nonlinear work, exactly as equation `RH1` requires before absorption.

The final section records the strongest presently unconditional H² time-integral precursor:
on every compact subinterval strictly inside the lifespan, the lower integral of the squared
order-two Sobolev norm is finite.  This follows directly from the continuous order-two datum
path carried by `ClassicalSolutionR`.  It does not claim the endpoint `S = T` estimate of
`research/C01/Spec.lean:h2TimeIntegral`; that endpoint needs the still-open physical
`sobolevTwoFourier` bridge and the integrated enstrophy estimate.
-/

noncomputable section

open Set MeasureTheory Filter Topology
open EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev
  EulerSmoothLimit EulerMeanVectorIdentities EulerMeanCutoffCurl EulerVectorCalculus
open NSFormalization.Source.OrdinaryViscousStability
open NSFormalization.Section4.D01 (sobolevENorm)
open scoped RealInnerProductSpace ContDiff ENNReal

namespace NSFormalization.Section4.C01

open NSFormalization.Section4.A02 (ClassicalSolutionR MemForceR)

variable {ν : ℝ} {a : A02.SpatialField} {f : A02.SpaceTimeField} {T : ℝ}

/-! ## E6 — the pressure pairing against the Laplacian -/

/-- The Laplacian of a smooth square-integrable divergence-free field is divergence free.

The proof uses the classical vector identity `curl (curl u) = ∇(div u) - Δu`.  Since
`div u = 0`, the Laplacian is the negative of a curl, whose divergence vanishes. -/
theorem laplacianField_divergence_zero (U : SmoothL2Field Space)
    (hdiv : ∀ x, divergence U.field x = 0) (x : Space) :
    divergence (laplacianField U).field x = 0 := by
  have hdivfun : divergence U.field = 0 := funext hdiv
  have hlap : (laplacianField U).field = -vectorCurl (vectorCurl U.field) := by
    rw [laplacianField_field]
    have hcurl := vectorCurl_vectorCurl U.field U.smooth
    rw [hdivfun] at hcurl
    have hgradzero : gradient (0 : Space → ℝ) = 0 := by
      funext y
      simp [gradient]
    rw [hgradzero, zero_sub] at hcurl
    simpa using (congrArg Neg.neg hcurl).symm
  rw [hlap]
  have hsmooth : ∀ i : Fin 3, ContDiff ℝ ∞ (fun y => vectorCurl U.field y i) :=
    (contDiff_piLp 2).mp (vectorCurl_smooth U.field U.smooth)
  have hcurl : divergence (vectorCurl (vectorCurl U.field)) x = 0 :=
    divergence_curl (fun i y => vectorCurl U.field y i) hsmooth x
  rw [divergence_eq_coordinate_sum] at hcurl ⊢
  simpa only [fderiv_neg, neg_apply, PiLp.neg_apply, Finset.sum_neg_distrib,
    neg_zero] using congrArg Neg.neg hcurl

/-- **Row E6.**  For an interior slice of a classical divergence-free solution,
`⟪Δu, ∇p⟫ = 0`. -/
theorem laplacian_pressure_pairing_zero
    (w : ClassicalSolutionR ν a f T) (hf : MemForceR f)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    @inner ℝ _ _
        (laplacianField (velocitySliceField w (Ioo_subset_Ico_self ht))).toLp
        (pressureGradientField w hf ht).toLp = 0 := by
  rw [real_inner_comm]
  exact gradient_pairing_zero
    (pressureGradientField w hf ht)
    (laplacianField (velocitySliceField w (Ioo_subset_Ico_self ht)))
    (fun z => w.pressure (t, z))
    (contDiff_pressureSlice w ht)
    (pressureGradientField_eq_gradient w hf ht)
    (laplacianField_divergence_zero _
      (velocitySliceField_divergence w (Ioo_subset_Ico_self ht)))

/-! ## E7 — the arithmetic core and the classical identity -/

/-- **Row E7, carrier-independent arithmetic core.**  Pairing
`Gt = νL - N - P + F` against `-2L`, with `⟪L,P⟫ = 0`, leaves the nonlinear
work and the force pairing with the manuscript's signs. -/
theorem inner_enstrophy_identity_deriv
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ν d : ℝ} (L N P F Gt : E)
    (hd : d = -2 * @inner ℝ E _ L Gt)
    (hmom : Gt = ν • L - N - P + F)
    (hpr : @inner ℝ E _ L P = 0) :
    d = 2 * @inner ℝ E _ N L - 2 * ν * ‖L‖ ^ 2 -
      2 * @inner ℝ E _ F L := by
  rw [hd, hmom, inner_add_right, inner_sub_right, inner_sub_right,
    real_inner_smul_right, hpr, real_inner_self_eq_norm_sq]
  rw [real_inner_comm L N, real_inner_comm L F]
  ring

/-- **E6/E7 assembled in carrier-B raw-integral vocabulary.**  At an interior time,
substitution of the momentum equation into `-2⟪Δu,∂ₜu⟫` gives

`2∫⟪(u·∇)u,Δu⟫ - 2ν∫‖Δu‖² - 2∫⟪f,Δu⟫`.
-/
theorem enstrophyDerivative_value_classical
    (w : ClassicalSolutionR ν a f T) (hf : MemForceR f)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    -2 * (@inner ℝ _ _
        (laplacianField (velocitySliceField w (Ioo_subset_Ico_self ht))).toLp
        (temporalSliceField w hf ht).toLp) =
      2 * (∫ x, (inner ℝ
          ((advectionField (velocitySliceField w (Ioo_subset_Ico_self ht))
            (velocitySliceField w (Ioo_subset_Ico_self ht))).field x)
          ((laplacianField (velocitySliceField w (Ioo_subset_Ico_self ht))).field x) : ℝ)) -
      2 * ν * (∫ x,
          ‖(laplacianField (velocitySliceField w (Ioo_subset_Ico_self ht))).field x‖ ^ 2) -
      2 * (∫ x, (inner ℝ ((forceSliceField hf (le_of_lt ht.1)).field x)
          ((laplacianField (velocitySliceField w (Ioo_subset_Ico_self ht))).field x) : ℝ)) := by
  let U := velocitySliceField w (Ioo_subset_Ico_self ht)
  let L := laplacianField U
  let N := advectionField U U
  let P := pressureGradientField w hf ht
  let F := forceSliceField hf (le_of_lt ht.1)
  let Gt := temporalSliceField w hf ht
  have hcore := inner_enstrophy_identity_deriv L.toLp N.toLp P.toLp F.toLp Gt.toLp
    (d := -2 * (@inner ℝ _ _ L.toLp Gt.toLp)) rfl
    (show Gt.toLp = ν • L.toLp - N.toLp - P.toLp + F.toLp from
      momentum_split_toLp w hf ht)
    (show @inner ℝ _ _ L.toLp P.toLp = 0 from laplacian_pressure_pairing_zero w hf ht)
  dsimp only [U, L, N, P, F, Gt] at hcore ⊢
  rw [norm_toLp_sq_eq_l2Sq] at hcore
  simpa only [pairing_eq_inner] using hcore

/-- **E6 / `enstrophyIdentity`, raw-integral form.**  At every interior time,

`d/dt ∫∑ᵢ‖∂ᵢu‖² = 2∫⟪(u·∇)u,Δu⟫ - 2ν∫‖Δu‖² - 2∫⟪f,Δu⟫`.
-/
theorem enstrophyIdentity_classical
    (w : ClassicalSolutionR ν a f T) (hf : MemForceR f)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt
      (fun s : ℝ => ∫ x, ∑ i : Fin 3,
        ‖fderiv ℝ (fun y : Space => w.velocity (s, y)) x (axis i)‖ ^ 2)
      (2 * (∫ x, (inner ℝ
          ((advectionField (velocitySliceField w (Ioo_subset_Ico_self ht))
            (velocitySliceField w (Ioo_subset_Ico_self ht))).field x)
          ((laplacianField (velocitySliceField w (Ioo_subset_Ico_self ht))).field x) : ℝ)) -
       2 * ν * (∫ x,
          ‖(laplacianField (velocitySliceField w (Ioo_subset_Ico_self ht))).field x‖ ^ 2) -
       2 * (∫ x, (inner ℝ ((forceSliceField hf (le_of_lt ht.1)).field x)
          ((laplacianField (velocitySliceField w (Ioo_subset_Ico_self ht))).field x) : ℝ))) t := by
  rw [← enstrophyDerivative_value_classical w hf ht]
  exact enstrophyDerivative_classical_unconditional w hf ht

/-- The enstrophy identity in the local copies of the specification vocabulary:
`gradientSq`, `advectionWork`, `laplacianSq`, `pairing`, and `A05.lap`.  Each term
is definitionally the corresponding raw carrier integral above after unfolding the slice
packagings. -/
theorem enstrophyIdentity_gradientSq
    (w : ClassicalSolutionR ν a f T) (hf : MemForceR f)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt (fun s => gradientSq (slice w.velocity s))
      (2 * advectionWork (slice w.velocity t) -
        2 * ν * laplacianSq (slice w.velocity t) -
        2 * pairing (slice f t) (NSFormalization.Section4.A05.lap (slice w.velocity t))) t := by
  have hlap :
      (laplacianField (velocitySliceField w (Ioo_subset_Ico_self ht))).field =
        NSFormalization.Section4.A05.lap (slice w.velocity t) := by
    funext x
    rw [laplacianField_velocitySlice_field w (Ioo_subset_Ico_self ht) x]
    rfl
  have hadv :
      (advectionField (velocitySliceField w (Ioo_subset_Ico_self ht))
        (velocitySliceField w (Ioo_subset_Ico_self ht))).field =
        fun x => NavierStokes.ProblemStatement.advection (lift (slice w.velocity t)) 0 x := by
    funext x
    rw [advectionField_velocitySlice_field w (Ioo_subset_Ico_self ht) x]
    rfl
  have hforce : (forceSliceField hf (le_of_lt ht.1)).field = slice f t := rfl
  have hslice (s : ℝ) : slice w.velocity s = fun y : Space => w.velocity (s, y) := rfl
  have h := enstrophyIdentity_classical w hf ht
  rw [hlap, hadv, hforce] at h
  simpa only [gradientSq, NSFormalization.Section4.C01.slice, EulerOrdinarySobolev.axis,
    NavierStokes.ProblemStatement.coordinateVector, advectionWork, laplacianSq, pairing,
    hslice] using h

/-! ## The strict-interior H² time integral -/

/-- The squared order-two Sobolev norm has finite lower integral on every compact time
interval strictly inside a classical solution's lifespan.  This is stronger than an
absorption-gated statement for `S < T`, but does not cover the endpoint `S = T` needed by
the quantitative `h2TimeIntegral` field in the draft specification. -/
theorem h2TimeIntegral_strict
    (w : ClassicalSolutionR ν a f T) {S : ℝ} (_hS : 0 < S) (hST : S < T) :
    (∫⁻ t in Ioo (0 : ℝ) S,
      sobolevENorm 2 (slice w.velocity t) ^ (2 : ℝ)) ≠ ⊤ := by
  obtain ⟨G, hGc, hGd⟩ := w.sobolev 2
  have hsub : Icc (0 : ℝ) S ⊆ Ico (0 : ℝ) T :=
    fun t ht => ⟨ht.1, lt_of_le_of_lt ht.2 hST⟩
  have hcont : ContinuousOn (fun t => ‖G t‖ ^ 2) (Icc (0 : ℝ) S) :=
    ((hGc.mono hsub).norm.pow 2)
  have hint : IntegrableOn (fun t => ‖G t‖ ^ 2) (Ioo (0 : ℝ) S) volume :=
    hcont.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hfin : (∫⁻ t in Ioo (0 : ℝ) S, ENNReal.ofReal (‖G t‖ ^ 2)) ≠ ⊤ := by
    apply (lintegral_ofReal_ne_top_iff_integrable hint.1
      (Filter.Eventually.of_forall fun _ => sq_nonneg _)).2
    exact hint
  have heq :
      (∫⁻ t in Ioo (0 : ℝ) S, sobolevENorm 2 (slice w.velocity t) ^ (2 : ℝ)) =
        ∫⁻ t in Ioo (0 : ℝ) S, ENNReal.ofReal (‖G t‖ ^ 2) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    change sobolevENorm 2 (fun x : Space => w.velocity (t, x)) ^ (2 : ℝ) =
      ENNReal.ofReal (‖G t‖ ^ 2)
    have hnorm : sobolevENorm 2 (fun x : Space => w.velocity (t, x)) = ‖G t‖ₑ := by
      exact A04.sobolevENorm_eq (hGd t ⟨ht.1.le, lt_trans ht.2 hST⟩)
    rw [hnorm, ENNReal.rpow_two, ← ofReal_norm]
    exact (ENNReal.ofReal_pow (norm_nonneg _) 2).symm
  rw [heq]
  exact hfin

/-- The exact A04 `squaredHTwoIntegral` integrand spelling, whose square is a natural-number
power.  Lane 159's `enorm_npow_two_eq_rpow_two` converts it pointwise to the preceding C01
real-power statement. -/
theorem squaredHTwoIntegral_strict
    (w : ClassicalSolutionR ν a f T) {S : ℝ} (hS : 0 < S) (hST : S < T) :
    (∫⁻ t in Ioo (0 : ℝ) S, sobolevENorm 2 (slice w.velocity t) ^ (2 : ℕ)) ≠ ⊤ := by
  have heq :
      (∫⁻ t in Ioo (0 : ℝ) S, sobolevENorm 2 (slice w.velocity t) ^ (2 : ℕ)) =
        ∫⁻ t in Ioo (0 : ℝ) S, sobolevENorm 2 (slice w.velocity t) ^ (2 : ℝ) := by
    apply lintegral_congr
    intro t
    exact R43.enorm_npow_two_eq_rpow_two _
  rw [heq]
  exact h2TimeIntegral_strict w hS hST

/-- The same strict-interior finiteness in the exact C01 absorption-gate shape.  The gate is
logically unnecessary for `S < T`; it is retained so R43/R44 can feed their registered
smallness hypothesis without reshaping it. -/
theorem h2TimeIntegral_of_absorption
    (_hν : 0 < ν) (_ha : a ∈ A02.initialClassR) (_hf : MemForceR f)
    (w : ClassicalSolutionR ν a f T) {S : ℝ}
    (hS : 0 < S) (hST : S < T)
    (_habs : ∀ t ∈ Ico (0 : ℝ) S,
      ENNReal.ofReal NSFormalization.Section4.A05.gradientL6Const *
        criticalL3 (slice w.velocity t) ≤ ENNReal.ofReal (ν / 4)) :
    (∫⁻ t in Ioo (0 : ℝ) S,
      sobolevENorm 2 (slice w.velocity t) ^ (2 : ℝ)) ≠ ⊤ :=
  h2TimeIntegral_strict w hS hST

end NSFormalization.Section4.C01
