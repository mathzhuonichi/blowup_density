import NSFormalization.Section4.R43.Pieces
import NSFormalization.Section4.D01.HomogeneousNorm
import NSFormalization.Section4.D01.RealPairing
import NSFormalization.Section4.A04.DerivNorm
import NSFormalization.Section4.A04.HighEnergy
import NSFormalization.Section4.A04.PressureDrop
import NSFormalization.Section4.C01.MomentumCarrierB

/-!
# R43 row S1: the critical homogeneous pairing identities

This module is the identity layer of `paper/sections/04-whole-space.tex:97-99`.
The missing carrier bridge is isolated in `CriticalDatumPath`: it asks for the
order-`1/2` and order-`3/2` homogeneous data of the classical velocity slice,
the order-`1/2` data of the four momentum terms, and their concrete Fourier
symbol relations.  It does not assume any of the pairing identities or the
critical scalar inequality proved below.
-/

noncomputable section

open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Paper3
open NSFormalization.Source.RealSobolev
open scoped ContDiff RealInnerProductSpace

namespace NSFormalization.Section4.R43

open NSFormalization.Section4.A02
  (SpatialField SpaceTimeField ClassicalSolutionR MemForceR)
open NSFormalization.Section4.D01
  (dotHomogeneousENorm SchwartzPairable)
open NSFormalization.Section4.D01.Homogeneous
  (IsHomogeneousSliceDatum)
open NSFormalization.Section4.D01.Leray
  (lerayComplement)

/-! ## 1. Norms and the datum-infimum realization -/

/-- The zero physical field is represented by the zero homogeneous datum at
every real order.  Besides being useful independently, this supplies the
concrete carrier for the zero-solution non-vacuity check of `CriticalDatumPath`. -/
theorem isHomogeneousSliceDatum_zero (s : ℝ) :
    IsHomogeneousSliceDatum s (0 : SpatialField) 0 := by
  refine ⟨0, ?_, ?_⟩
  · simp [NSFormalization.Section4.D01.Homogeneous.IsSliceDistribution]
  · simp [NSFormalization.Section4.D01.Homogeneous.IsHomogeneousVectorDatum,
      NSFormalization.Section4.D01.Homogeneous.IsHomogeneousDatum]

/-- The critical velocity norm `y(t) = ‖u(t)‖_{Ḣ^{1/2}}`, in real scalar form. -/
def criticalNormAt (u : SpaceTimeField) (t : ℝ) : ℝ :=
  (dotHomogeneousENorm (1 / 2) (fun x => u (t, x))).toReal

/-- The critical dissipation norm `z(t) = ‖u(t)‖_{Ḣ^{3/2}}`. -/
def criticalDissipationAt (u : SpaceTimeField) (t : ℝ) : ℝ :=
  (dotHomogeneousENorm (3 / 2) (fun x => u (t, x))).toReal

/-- The slicewise critical force norm `b(t) = ‖f(t)‖_{Ḣ^{1/2}}`. -/
def criticalForceAt (f : SpaceTimeField) (t : ℝ) : ℝ :=
  (dotHomogeneousENorm (1 / 2) (fun x => f (t, x))).toReal

/-- Since homogeneous slice data are unique, the datum-infimum is attained at
every supplied datum. -/
theorem dotHomogeneousENorm_eq_of_isHomogeneousSlice {s : ℝ} {z : SpatialField}
    {A : RealVectorSobolev s} (hA : IsHomogeneousSliceDatum s z A) :
    dotHomogeneousENorm s z = ‖A‖ₑ := by
  rw [dotHomogeneousENorm]
  refine le_antisymm ?_ (le_iInf fun B => ?_)
  · exact iInf_le_of_le ⟨A, hA⟩ le_rfl
  · rw [NSFormalization.Section4.D01.Homogeneous.isHomogeneousSliceDatum_unique B.2 hA]

/-- Real form of `dotHomogeneousENorm_eq_of_isHomogeneousSlice`. -/
theorem criticalNormAt_eq_norm {u : SpaceTimeField} {t : ℝ}
    {A : RealVectorSobolev (1 / 2)}
    (hA : IsHomogeneousSliceDatum (1 / 2) (fun x => u (t, x)) A) :
    criticalNormAt u t = ‖A‖ := by
  rw [criticalNormAt, dotHomogeneousENorm_eq_of_isHomogeneousSlice hA, toReal_enorm]

/-- Real form at the dissipative order `3/2`. -/
theorem criticalDissipationAt_eq_norm {u : SpaceTimeField} {t : ℝ}
    {Z : RealVectorSobolev (3 / 2)}
    (hZ : IsHomogeneousSliceDatum (3 / 2) (fun x => u (t, x)) Z) :
    criticalDissipationAt u t = ‖Z‖ := by
  rw [criticalDissipationAt, dotHomogeneousENorm_eq_of_isHomogeneousSlice hZ, toReal_enorm]

/-- Real form for the half-order datum of the force slice. -/
theorem criticalForceAt_eq_norm {f : SpaceTimeField} {t : ℝ}
    {F : RealVectorSobolev (1 / 2)}
    (hF : IsHomogeneousSliceDatum (1 / 2) (fun x => f (t, x)) F) :
    criticalForceAt f t = ‖F‖ := by
  rw [criticalForceAt, dotHomogeneousENorm_eq_of_isHomogeneousSlice hF, toReal_enorm]

/-! ## 2. Fourier-side pairing identities -/

/-- Datum-level Laplacian identity.  The hypotheses are exactly the two
homogeneous Fourier symbol relations

`Z(ξ) = |ξ| A(ξ)`, `L(ξ) = -|ξ|² A(ξ)`.

Thus `A`, `Z`, and `L` are respectively the order-`1/2` velocity datum, the
order-`3/2` velocity datum, and the order-`1/2` Laplacian datum. -/
theorem critical_laplacian_pairing
    (A : RealVectorSobolev (1 / 2)) (Z : RealVectorSobolev (3 / 2))
    (L : RealVectorSobolev (1 / 2))
    (hZ : ∀ i : Fin 3,
      (((Z i : RealSobolevHilbert (3 / 2)) : FourierData) : Space → ℂ) =ᵐ[volume]
        fun ξ => ((‖ξ‖ : ℝ) : ℂ) * (A i : FourierData) ξ)
    (hL : ∀ i : Fin 3,
      (((L i : RealSobolevHilbert (1 / 2)) : FourierData) : Space → ℂ) =ᵐ[volume]
        fun ξ => -(((‖ξ‖ ^ 2 : ℝ) : ℂ) * (A i : FourierData) ξ)) :
    ⟪L, A⟫ = -‖Z‖ ^ 2 := by
  rw [real_inner_comm A L]
  rw [PiLp.inner_apply, PiLp.norm_sq_eq_of_L2, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [realSobolev_inner_eq_ambient, real_inner_eq_re_complex]
  change RCLike.re (inner ℂ (A i : FourierData) (L i : FourierData)) =
    -‖(Z i : FourierData)‖ ^ 2
  rw [MeasureTheory.L2.inner_def,
    norm_sq_eq_re_inner (𝕜 := ℂ) (Z i : FourierData),
    MeasureTheory.L2.inner_def,
    ← integral_re (MeasureTheory.L2.integrable_inner
      (𝕜 := ℂ) (A i : FourierData) (L i : FourierData)),
    ← integral_re (MeasureTheory.L2.integrable_inner
      (𝕜 := ℂ) (Z i : FourierData) (Z i : FourierData)),
    ← MeasureTheory.integral_neg]
  apply integral_congr_ae
  filter_upwards [hZ i, hL i] with ξ hz hl
  simp only [RCLike.inner_apply, hz, hl, map_mul, Complex.conj_ofReal]
  push_cast
  ring_nf
  rw [map_neg]

/-- Datum-level pressure cancellation.  A transverse velocity datum is
orthogonal to every datum in the range of the Fourier-side Leray complement. -/
theorem critical_pressure_pairing
    (A P Q : RealVectorSobolev (1 / 2))
    (hA : lerayComplement (1 / 2) A = 0)
    (hP : P = lerayComplement (1 / 2) Q) :
    ⟪P, A⟫ = 0 := by
  rw [real_inner_comm A P]
  rw [hP]
  exact NSFormalization.Section4.A04.inner_lerayComplement_eq_zero_of_eq_zero
    (1 / 2) A Q hA

/-- Datum-level Cauchy--Schwarz for the force work. -/
theorem critical_force_pairing
    (A F : RealVectorSobolev (1 / 2)) :
    |⟪F, A⟫| ≤ ‖F‖ * ‖A‖ := by
  simpa using abs_real_inner_le_norm F A

/-! ## 3. The named missing critical carrier bridge -/

/-- `hcrit`, the exact carrier input left to the later homogeneous-path lane.

It supplies data, not estimates: the velocity at orders `1/2` and `3/2`, the
four order-`1/2` momentum terms, smoothness of the half-order velocity path, the
datum form of the momentum equation, and the three Fourier-symbol
compatibilities used by the identities above.  In particular, neither the
trilinear estimate nor any pairing conclusion is a field of this structure. -/
structure CriticalDatumPath
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (w : ClassicalSolutionR ν a f T) (hf : MemForceR f) where
  velocityHalf : ℝ → RealVectorSobolev (1 / 2)
  velocityThreeHalf : ℝ → RealVectorSobolev (3 / 2)
  laplacianHalf : ℝ → RealVectorSobolev (1 / 2)
  advectionHalf : ℝ → RealVectorSobolev (1 / 2)
  pressureHalf : ℝ → RealVectorSobolev (1 / 2)
  forceHalf : ℝ → RealVectorSobolev (1 / 2)
  velocityHalf_isDatum : ∀ t ∈ Ico (0 : ℝ) T,
    IsHomogeneousSliceDatum (1 / 2) (fun x => w.velocity (t, x)) (velocityHalf t)
  velocityThreeHalf_isDatum : ∀ t ∈ Ico (0 : ℝ) T,
    IsHomogeneousSliceDatum (3 / 2) (fun x => w.velocity (t, x)) (velocityThreeHalf t)
  laplacianHalf_isDatum : ∀ t ∈ Ioo (0 : ℝ) T,
    IsHomogeneousSliceDatum (1 / 2)
      (fun x => spatialLaplacian w.velocity t x) (laplacianHalf t)
  advectionHalf_isDatum : ∀ t ∈ Ioo (0 : ℝ) T,
    IsHomogeneousSliceDatum (1 / 2)
      (fun x => advection w.velocity t x) (advectionHalf t)
  pressureHalf_isDatum : ∀ t ∈ Ioo (0 : ℝ) T,
    IsHomogeneousSliceDatum (1 / 2)
      (fun x => pressureGradient w.pressure t x) (pressureHalf t)
  forceHalf_isDatum : ∀ t ∈ Ioo (0 : ℝ) T,
    IsHomogeneousSliceDatum (1 / 2) (fun x => f (t, x)) (forceHalf t)
  velocityHalf_smooth : ContDiffOn ℝ ∞ velocityHalf (Ico (0 : ℝ) T)
  momentum : ∀ t ∈ Ioo (0 : ℝ) T,
    deriv velocityHalf t =
      ν • laplacianHalf t - advectionHalf t - pressureHalf t + forceHalf t
  order_shift : ∀ t ∈ Ioo (0 : ℝ) T, ∀ i : Fin 3,
    ((((velocityThreeHalf t) i : RealSobolevHilbert (3 / 2)) : FourierData) :
        Space → ℂ) =ᵐ[volume]
      fun ξ => ((‖ξ‖ : ℝ) : ℂ) * ((velocityHalf t) i : FourierData) ξ
  laplacian_symbol : ∀ t ∈ Ioo (0 : ℝ) T, ∀ i : Fin 3,
    ((((laplacianHalf t) i : RealSobolevHilbert (1 / 2)) : FourierData) :
        Space → ℂ) =ᵐ[volume]
      fun ξ => -(((‖ξ‖ ^ 2 : ℝ) : ℂ) * ((velocityHalf t) i : FourierData) ξ)
  velocity_transverse : ∀ t ∈ Ioo (0 : ℝ) T,
    lerayComplement (1 / 2) (velocityHalf t) = 0
  pressure_longitudinal : ∀ t ∈ Ioo (0 : ℝ) T,
    ∃ Q : RealVectorSobolev (1 / 2),
      pressureHalf t = lerayComplement (1 / 2) Q

/-- The weighted energy path carried by the order-`1/2` velocity datum:
`t ↦ ‖A_{1/2}(t)‖²`. -/
def criticalEnergyPath
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    {w : ClassicalSolutionR ν a f T} {hf : MemForceR f}
    (hcrit : CriticalDatumPath w hf) (t : ℝ) : ℝ :=
  ‖hcrit.velocityHalf t‖ ^ 2

/-- The energy derivative selected by the half-order datum path. -/
def criticalEnergyDerivative
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    {w : ClassicalSolutionR ν a f T} {hf : MemForceR f}
    (hcrit : CriticalDatumPath w hf) (t : ℝ) : ℝ :=
  2 * ⟪hcrit.velocityHalf t, deriv hcrit.velocityHalf t⟫

/-- `htri`, the exact S1b input deliberately left to the separate trilinear
lane. -/
def CriticalTrilinearEstimate
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T C₀ : ℝ}
    {w : ClassicalSolutionR ν a f T} {hf : MemForceR f}
    (hcrit : CriticalDatumPath w hf) : Prop :=
  ∀ t ∈ Ioo (0 : ℝ) T,
    |⟪hcrit.advectionHalf t, hcrit.velocityHalf t⟫| ≤
      C₀ * ‖hcrit.velocityHalf t‖ * ‖hcrit.velocityThreeHalf t‖ ^ 2

/-! ## 4. Pathwise identities and the scalar consequence -/

/-- On the solution interval, the explicit datum energy path is exactly
`y(t)² = ‖u(t)‖_{Ḣ^{1/2}}²`. -/
theorem criticalEnergyPath_eq
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    {w : ClassicalSolutionR ν a f T} {hf : MemForceR f}
    (hcrit : CriticalDatumPath w hf) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    criticalEnergyPath hcrit t = criticalNormAt w.velocity t ^ 2 := by
  rw [criticalEnergyPath, criticalNormAt_eq_norm (hcrit.velocityHalf_isDatum t ht)]

/-- The datum energy path has derivative
`2⟪A_{1/2}(t), A'_{1/2}(t)⟫` at every interior time. -/
theorem criticalEnergyPath_hasDerivAt
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    {w : ClassicalSolutionR ν a f T} {hf : MemForceR f}
    (hcrit : CriticalDatumPath w hf) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt (criticalEnergyPath hcrit) (criticalEnergyDerivative hcrit t) t := by
  exact NSFormalization.Section4.A04.hasDerivAt_datumNormSq_of_contDiffOn
    hcrit.velocityHalf_smooth ht

/-- The critical norm is continuous on the solution half-open interval. -/
theorem criticalNormAt_continuousOn
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    {w : ClassicalSolutionR ν a f T} {hf : MemForceR f}
    (hcrit : CriticalDatumPath w hf) :
    ContinuousOn (criticalNormAt w.velocity) (Ico (0 : ℝ) T) := by
  refine hcrit.velocityHalf_smooth.continuousOn.norm.congr ?_
  intro t ht
  exact criticalNormAt_eq_norm (hcrit.velocityHalf_isDatum t ht)

/-- Weighted energy derivative shape:
`(y²)' = 2⟪A_{1/2}, A'_{1/2}⟫`. -/
theorem criticalEnergyDerivative_hasDerivAt
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    {w : ClassicalSolutionR ν a f T} {hf : MemForceR f}
    (hcrit : CriticalDatumPath w hf) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt (fun r => criticalNormAt w.velocity r ^ 2)
      (criticalEnergyDerivative hcrit t) t := by
  refine (criticalEnergyPath_hasDerivAt hcrit ht).congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
  exact (criticalEnergyPath_eq hcrit (Ioo_subset_Ico_self hr)).symm

/-- Pathwise form of `⟪Δu, Λu⟫ = -z²`. -/
theorem criticalLaplacianPairing_path
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    {w : ClassicalSolutionR ν a f T} {hf : MemForceR f}
    (hcrit : CriticalDatumPath w hf) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    ⟪hcrit.laplacianHalf t, hcrit.velocityHalf t⟫ =
      -(criticalDissipationAt w.velocity t) ^ 2 := by
  rw [criticalDissipationAt_eq_norm
    (hcrit.velocityThreeHalf_isDatum t (Ioo_subset_Ico_self ht))]
  exact critical_laplacian_pairing _ _ _ (hcrit.order_shift t ht)
    (hcrit.laplacian_symbol t ht)

/-- Pathwise form of `⟪∇p, Λu⟫ = 0`. -/
theorem criticalPressurePairing_path
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    {w : ClassicalSolutionR ν a f T} {hf : MemForceR f}
    (hcrit : CriticalDatumPath w hf) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    ⟪hcrit.pressureHalf t, hcrit.velocityHalf t⟫ = 0 := by
  obtain ⟨Q, hQ⟩ := hcrit.pressure_longitudinal t ht
  exact critical_pressure_pairing _ _ Q (hcrit.velocity_transverse t ht) hQ

/-- Pathwise form of `|⟪f, Λu⟫| ≤ b y`. -/
theorem criticalForcePairing_path
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    {w : ClassicalSolutionR ν a f T} {hf : MemForceR f}
    (hcrit : CriticalDatumPath w hf) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    |⟪hcrit.forceHalf t, hcrit.velocityHalf t⟫| ≤
      criticalForceAt f t * criticalNormAt w.velocity t := by
  rw [criticalForceAt_eq_norm (hcrit.forceHalf_isDatum t ht),
    criticalNormAt_eq_norm
      (hcrit.velocityHalf_isDatum t (Ioo_subset_Ico_self ht))]
  exact critical_force_pairing _ _

/-- **eq:Rcritical1, conditional only on `hcrit` and `htri`.**  This has the
literal scalar `henergy` shape consumed by `criticalNormBound_radius`. -/
theorem rcritical1_of_trilinear
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T C₀ : ℝ}
    {w : ClassicalSolutionR ν a f T} (hf : MemForceR f)
    (hcrit : CriticalDatumPath w hf)
    (htri : CriticalTrilinearEstimate (C₀ := C₀) hcrit) :
    (∀ t ∈ Ioo (0 : ℝ) T,
      HasDerivAt (fun r => criticalNormAt w.velocity r ^ 2)
        (criticalEnergyDerivative hcrit t) t) ∧
      ∀ t ∈ Ioo (0 : ℝ) T,
        criticalEnergyDerivative hcrit t / 2 +
            (ν - C₀ * criticalNormAt w.velocity t) *
              criticalDissipationAt w.velocity t ^ 2
          ≤ criticalForceAt f t * criticalNormAt w.velocity t := by
  refine ⟨fun t ht => criticalEnergyDerivative_hasDerivAt hcrit ht, ?_⟩
  intro t ht
  have hmom := hcrit.momentum t ht
  have hlap := criticalLaplacianPairing_path hcrit ht
  have hpressure := criticalPressurePairing_path hcrit ht
  have hforce := criticalForcePairing_path hcrit ht
  have htri' :
      |⟪hcrit.velocityHalf t, hcrit.advectionHalf t⟫| ≤
        C₀ * ‖hcrit.velocityHalf t‖ * ‖hcrit.velocityThreeHalf t‖ ^ 2 := by
    simpa [real_inner_comm] using htri t ht
  have hnonlinear :
      -⟪hcrit.velocityHalf t, hcrit.advectionHalf t⟫ ≤
        C₀ * ‖hcrit.velocityHalf t‖ * ‖hcrit.velocityThreeHalf t‖ ^ 2 :=
    (neg_le_abs _).trans htri'
  have hforce' :
      ⟪hcrit.velocityHalf t, hcrit.forceHalf t⟫ ≤
        criticalForceAt f t * criticalNormAt w.velocity t :=
    (le_abs_self _).trans (by simpa [real_inner_comm] using hforce)
  have hforceNorm :
      ⟪hcrit.velocityHalf t, hcrit.forceHalf t⟫ ≤
        ‖hcrit.forceHalf t‖ * ‖hcrit.velocityHalf t‖ := by
    rw [← criticalForceAt_eq_norm (hcrit.forceHalf_isDatum t ht),
      ← criticalNormAt_eq_norm
        (hcrit.velocityHalf_isDatum t (Ioo_subset_Ico_self ht))]
    exact hforce'
  have hexpand :
      ⟪hcrit.velocityHalf t, deriv hcrit.velocityHalf t⟫ =
        ν * ⟪hcrit.velocityHalf t, hcrit.laplacianHalf t⟫ -
          ⟪hcrit.velocityHalf t, hcrit.advectionHalf t⟫ +
            ⟪hcrit.velocityHalf t, hcrit.forceHalf t⟫ := by
    rw [hmom]
    simp only [inner_add_right, inner_sub_right, real_inner_smul_right,
      show ⟪hcrit.velocityHalf t, hcrit.pressureHalf t⟫ = 0 by
        simpa [real_inner_comm] using hpressure]
    ring
  have hlap' : ⟪hcrit.velocityHalf t, hcrit.laplacianHalf t⟫ =
      -(criticalDissipationAt w.velocity t) ^ 2 := by
    simpa [real_inner_comm] using hlap
  rw [criticalEnergyDerivative, hexpand, hlap',
    criticalNormAt_eq_norm
      (hcrit.velocityHalf_isDatum t (Ioo_subset_Ico_self ht)),
    criticalDissipationAt_eq_norm
      (hcrit.velocityThreeHalf_isDatum t (Ioo_subset_Ico_self ht)),
    criticalForceAt_eq_norm (hcrit.forceHalf_isDatum t ht)]
  ring_nf at hnonlinear hforceNorm ⊢
  nlinarith

end NSFormalization.Section4.R43
