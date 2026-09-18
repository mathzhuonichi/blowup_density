import NSFormalization.Section3.T13.Assembly
import NSFormalization.Section3.T15.Scaling
import NSFormalization.Section3.T16.Assembly
import NSFormalization.Section3.T17.CorrectionProfile
import NSFormalization.Section3.T17.ForceProfile
import NSFormalization.Section3.T17.Transport
import NSFormalization.Section3.T17.CorrectionDeriv
import NSFormalization.Section3.T17.ForceDeriv

/-!
# T17 U-CAN: the canonical correction API

This is the formalization-side statement layer for
`research/T17/Spec.lean:752-980`.  The packet parameter of the Spec is
eliminated exactly as in T15 U-CAN: `place` is the raw-field
`NSFormalization.Section3.T15.PlacementData u p f K`, and every occurrence of
the packet velocity, chart center, and target time is replaced by `u`,
`place.x₀`, and `place.T`.  The T16/T13 records are the canonical records from
their Section 3 modules.

The profile vocabulary is restated with the canonical bare `(x₀,T)` spelling
because lane 375's force-profile module is not an ancestor of this lane.
The U3/U4/U5/U6 proof units remain separate from this statement module; their
`hv : ContDiff ℝ ∞ v` premise is discharged by the eventual T17 assembly (by
a chart truncation or by an explicit assembly hypothesis).  In particular,
the Spec's field list is intentionally unchanged: no `reference_smooth` field
is added here.  This is the still-open G1 issue recorded in
`research/T17/SPEC_ISSUES.md`.
-/

noncomputable section

namespace NSFormalization.Section3.T17

open Set MeasureTheory
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Section3.T13
open NSFormalization.Section3.T15
open NSFormalization.Section3.T16
open NSFormalization.Section4.I02
open NSFormalization.Section4.A02 (SpaceTimeField SpatialField)
open scoped ContDiff ENNReal Topology BigOperators

/-! ## Fixed-cylinder force-profile vocabulary (Spec.lean:689-723) -/

/- `rescaledReference` and `rescaledForceProfile` are supplied by the
   canonical U4 vocabulary in `ForceProfile.lean`. -/

/-- `03-torus.tex:225`: the torus-lifted spacetime field used to measure one
periodic copy of the force support. -/
def torusSpaceTimeLift (f : SpaceTimeField) : ℝ × PeriodicTorus → Space :=
  fun z => torusLift (fun x => f (z.1, x)) z.2

/-- `03-torus.tex:225`: spatial projection of the lifted support. -/
def torusSpatialSupport (f : SpaceTimeField) : Set PeriodicTorus :=
  Prod.snd '' tsupport (torusSpaceTimeLift f)

/-- `03-torus.tex:225`: temporal projection of the same lifted support. -/
def torusTemporalSupport (f : SpaceTimeField) : Set ℝ :=
  Prod.fst '' tsupport (torusSpaceTimeLift f)

/-! ## The canonical record -/

/-- Reconciled Type-valued API for `lem:correction`,
`paper/sections/03-torus.tex:218-285`, over T15's raw packet fields.

The field list is token-for-token the Spec list.  Only the namespace and the
packet projections change: `P.velocity` becomes `u`, while `place.x₀` and
`place.T` supply the bare chart spelling. -/
structure CorrectionAPI (ν : ℝ) {u : VelocityField} {p : PressureField}
    {f : VelocityField} {K : Set Space}
    (place : PlacementData u p f K)
    (v : SpaceTimeField) (r δ : ℝ) (D : CutoffData) : Type where
  /-- `03-torus.tex:176-217`: a T16 local-potential witness for the same
  reference, enlarged set, chart center, radius, time, margin, and cutoffs.
  Non-vacuity: this field carries the concrete potential and correction family
  used by every later field. -/
  potential : LocalPotentialAPI v u place.Kstar place.x₀ r place.T δ D
  /-- `03-torus.tex:22-98`: the T13 localization witness used for the fractional
  torus estimate.  Non-vacuity: its six concrete integral identities and
  endpoint transfers are available to the `H^s` consumer. -/
  localization : LocalizationAPI
  /-- `03-torus.tex:219-223`: positive viscosity.  Non-vacuity: excludes the
  degenerate zero-viscosity force formula. -/
  viscosity_pos : 0 < ν
  /-- `03-torus.tex:102-105`: positive chart radius.  Non-vacuity: the local
  ball used by the potential is nonempty. -/
  radius_pos : 0 < r
  /-- `03-torus.tex:102-105`: `ball x₀ r ⊆ ball chartCenter chartRadius`.
  Non-vacuity: this is the chart inclusion consumed by T13's localization
  witness together with `place.chartBall_in_cube`. -/
  ball_in_chart : Metric.ball place.x₀ r ⊆ Metric.ball place.chartCenter place.chartRadius
  /-- `03-torus.tex:103,242`: the T16 threshold is within the shared placement
  threshold.  Non-vacuity: all scale clauses use one common interval. -/
  eps_le_placement : D.ε₀ ≤ place.ε₀
  /-- `03-torus.tex:2-4`: the reference velocity is unit-periodic.
  Non-vacuity: this is the actual periodicity hypothesis used by every chart
  and torus norm. -/
  reference_periodic : IsPeriodicOn univ v

  /-- `03-torus.tex:256-260`: the correction profile is smooth on the fixed
  cylinder.  Non-vacuity: this is regularity of the displayed `W_ε`, not an
  unspecified profile. -/
  correction_profile_smooth : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    ContDiffOn ℝ ∞ (rescaledCorrectionProfile v place.x₀ place.T ε D)
      (fixedProfileCylinder D)
  /-- `03-torus.tex:256-260`: `W_ε` is supported in the fixed cylinder.
  Non-vacuity: the topological support of the concrete profile is bounded. -/
  correction_profile_support : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    tsupport (rescaledCorrectionProfile v place.x₀ place.T ε D) ⊆ fixedProfileCylinder D
  /-- `03-torus.tex:254-260`: data constants for every full derivative order.
  Non-vacuity: the constants are selected before `ε`. -/
  correctionProfileConst : ℕ → ℝ
  /-- `03-torus.tex:254-260`: nonnegative profile constants.  Non-vacuity:
  excludes a negative real witness collapsed by `ENNReal.ofReal`. -/
  correctionProfileConst_nonneg : ∀ k, 0 ≤ correctionProfileConst k
  /-- `03-torus.tex:254-260`: uniform derivative bounds for `W_ε`.
  Non-vacuity: each fixed order has one bound on every admissible scale. -/
  correction_profile_uniform : ∀ k : ℕ, ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    ∀ z ∈ fixedProfileCylinder D,
      ‖iteratedFDeriv ℝ k (rescaledCorrectionProfile v place.x₀ place.T ε D) z‖ ≤
        correctionProfileConst k
  /-- `03-torus.tex:262-273`: the force profile is smooth on the fixed
  cylinder.  Non-vacuity: this regularity applies to the displayed bracket. -/
  force_profile_smooth : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    ContDiffOn ℝ ∞ (rescaledForceProfile ν v place.x₀ place.T ε D)
      (fixedProfileCylinder D)
  /-- `03-torus.tex:262-273`: the bracketed force profile is supported in the
  fixed cylinder.  Non-vacuity: no unbounded rescaled support is admitted. -/
  force_profile_support : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    tsupport (rescaledForceProfile ν v place.x₀ place.T ε D) ⊆ fixedProfileCylinder D
  /-- `03-torus.tex:262-273`: data constants for force-profile derivatives.
  Non-vacuity: the constants are fixed before `ε`. -/
  forceProfileConst : ℕ → ℝ
  /-- `03-torus.tex:262-273`: nonnegative force-profile constants.
  Non-vacuity: excludes a negative witness collapsed by `ENNReal.ofReal`. -/
  forceProfileConst_nonneg : ∀ k, 0 ≤ forceProfileConst k
  /-- `03-torus.tex:262-273`: uniform derivative bounds for the bracket.
  Non-vacuity: every fixed order is controlled throughout the cylinder. -/
  force_profile_uniform : ∀ k : ℕ, ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    ∀ z ∈ fixedProfileCylinder D,
      ‖iteratedFDeriv ℝ k (rescaledForceProfile ν v place.x₀ place.T ε D) z‖ ≤
        forceProfileConst k
  /-- `03-torus.tex:256-259`: physical correction equals `W_ε` in the chart.
  Non-vacuity: this links the bound-bearing family `D.correction` to the
  profile family rather than leaving them independent. -/
  correction_profile_identity : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    ∀ z ∈ fixedProfileCylinder D,
      D.correction ε (correctionChartPoint place.x₀ place.T ε z) =
        rescaledCorrectionProfile v place.x₀ place.T ε D z
  /-- `03-torus.tex:264-272`: physical force equals `ε⁻²` times the bracket.
  Non-vacuity: this is the exact affine rescaling identity with all three
  interior powers present in the profile definition. -/
  force_profile_identity : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    ∀ z ∈ fixedProfileCylinder D,
      correctionForce ν v D ε (correctionChartPoint place.x₀ place.T ε z) =
        (ε ^ 2)⁻¹ • rescaledForceProfile ν v place.x₀ place.T ε D z
  /-- `03-torus.tex:225`: global smoothness across `T` and zero extension.
  Non-vacuity: this is a regularity property of the concrete `H_ε`. -/
  force_smooth : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    ContDiff ℝ ∞ (correctionForce ν v D ε)
  /-- `03-torus.tex:225,235-240`: unit periodicity of `H_ε`.
  Non-vacuity: it makes the torus lift represent the physical force. -/
  force_periodic : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    IsPeriodicOn univ (correctionForce ν v D ε)
  /-- `03-torus.tex:225`: force support on the torus lift uses the manuscript's
  open spatial ball.  Non-vacuity: no closed-ball weakening is allowed. -/
  force_support : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    tsupport (correctionForce ν v D ε) ⊆
      Ioo (place.T - 2 * ε ^ 2) (place.T + 2 * ε ^ 2) ×ˢ
        periodicSet (Metric.ball place.x₀ (ε * D.θRadius))
  /-- `03-torus.tex:225`: real spatial-volume constant.  Non-vacuity:
  nonnegativity below makes its `ENNReal.ofReal` bound meaningful. -/
  spatialVolumeConst : ℝ
  /-- `03-torus.tex:225`: spatial-volume constant is nonnegative.
  Non-vacuity: this rules out a negative constant erased by `ENNReal.ofReal`. -/
  spatialVolumeConst_nonneg : 0 ≤ spatialVolumeConst
  /-- `03-torus.tex:225`: one-copy torus spatial support has volume `O(ε³)`.
  Non-vacuity: the support is measured after the torus lift, not in periodic
  Euclidean space where it would have infinite volume. -/
  force_spatial_volume : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    periodicTorusMeasure (torusSpatialSupport (correctionForce ν v D ε)) ≤
      ENNReal.ofReal (spatialVolumeConst * ε ^ 3)
  /-- `03-torus.tex:225`: temporal projection has length at most `4ε²`.
  Non-vacuity: the same lifted support is used for both projections. -/
  force_time_length : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    volume (torusTemporalSupport (correctionForce ν v D ε)) ≤
      ENNReal.ofReal (4 * ε ^ 2)
  /-- `03-torus.tex:226-229`: derivative constants for `w_ε`.
  Non-vacuity: these are concrete data fixed before `ε`. -/
  correctionDerivConst : ℕ → ℕ → ℝ
  /-- `03-torus.tex:226-229`: nonnegative correction derivative constants.
  Non-vacuity: each displayed rate has a nonnegative real coefficient. -/
  correctionDerivConst_nonneg : ∀ j m, 0 ≤ correctionDerivConst j m
  /-- `03-torus.tex:226-229`: arbitrary unit time/spatial directions give
  `C_{j,m} ε^{-2j-m}`.  Non-vacuity: the guard `(∀ i, ‖u i‖≤1)` makes
  the iterated Fréchet derivative a genuine directional derivative bound. -/
  correction_derivative_bound : ∀ j m : ℕ,
    ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ z : SpaceTime,
      ∀ u : Fin m → Space, (∀ i, ‖u i‖ ≤ 1) →
        ‖iteratedFDeriv ℝ (j + m) (D.correction ε) z
            (Fin.append (fun _ : Fin j => ((1 : ℝ), (0 : Space)))
              (fun i => ((0 : ℝ), u i)))‖ ≤
          correctionDerivConst j m * (ε⁻¹) ^ (2 * j + m)
  /-- `03-torus.tex:229-232`: force derivative constants.
  Non-vacuity: these coefficients are selected before `ε`. -/
  forceDerivConst : ℕ → ℝ
  /-- `03-torus.tex:229-232`: nonnegative force derivative constants.
  Non-vacuity: no negative coefficient is hidden by `ENNReal.ofReal`. -/
  forceDerivConst_nonneg : ∀ m, 0 ≤ forceDerivConst m
  /-- `03-torus.tex:229-232`: spatial directional bound including `m=0`.
  Non-vacuity: the unit-direction guard makes the derivative tensor honest. -/
  force_derivative_bound : ∀ m : ℕ,
    ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ z : SpaceTime,
      ∀ u : Fin m → Space, (∀ i, ‖u i‖ ≤ 1) →
        ‖iteratedFDeriv ℝ m (correctionForce ν v D ε) z
            (fun i => ((0 : ℝ), u i))‖ ≤
          forceDerivConst m * (ε⁻¹) ^ (2 + m)
  /-- `01-introduction.tex:143-145,03-torus.tex:234`: Haar-`L²` slices of
  `w_ε`.  Non-vacuity: these guards make both Bochner integrals in
  `energyENormT` honest rather than junk-small. -/
  correction_slice_memLp : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ t : ℝ,
    MemLp (torusLift (fun x => D.correction ε (t, x))) 2 periodicTorusMeasure
  /-- `01-introduction.tex:143-145,03-torus.tex:234`: Haar-`L²` full-gradient
  slices.  Non-vacuity: this is the second honesty guard for `energyENormT`. -/
  correction_gradient_memLp : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ t : ℝ,
    MemLp (torusLift (fun x => spatialGradient (D.correction ε) t x)) 2
      periodicTorusMeasure
  /-- `03-torus.tex:234,242`: real energy constant fixed before `ε`.
  Non-vacuity: its nonnegative field prevents a collapsed negative witness. -/
  energyConst : ℝ
  /-- `03-torus.tex:234,242`: energy constant nonnegative.
  Non-vacuity: the real coefficient cannot collapse to zero through `ofReal`. -/
  energyConst_nonneg : 0 ≤ energyConst
  /-- `03-torus.tex:234-280`: `‖w_ε‖_{E_T}≤Cε^{3/2}` with T10's torus
  energy norm.  Non-vacuity: the two preceding `MemLp` fields make the
  ess-supremum and lower Bochner integral honest. -/
  correction_energy_bound : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    energyENormT place.T (D.correction ε) ≤
      ENNReal.ofReal (energyConst * ε ^ ((3 : ℝ) / 2))
  /-- `03-torus.tex:235-237`: every force slice has an honest Haar-`L^p`
  representative.  Non-vacuity: this is the slice guard for the mixed norm. -/
  force_spatial_memLp : ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)],
    ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ t : ℝ,
      MemLp (torusLift (fun x => correctionForce ν v D ε (t, x))) p
        periodicTorusMeasure
  /-- `03-torus.tex:235-237,242`: real mixed constants fixed before `ε`.
  Non-vacuity: nonnegativity below prevents `ENNReal.ofReal` collapse. -/
  mixedConst : ℝ≥0∞ → ℝ≥0∞ → ℝ
  /-- `03-torus.tex:235-237,242`: mixed constants are nonnegative.
  Non-vacuity: this applies on the exact `1≤p,q` range of the bound. -/
  mixedConst_nonneg : ∀ (p q : ℝ≥0∞), 1 ≤ p → 1 ≤ q → 0 ≤ mixedConst p q
  /-- `03-torus.tex:235-237,281-282`: for `[Fact (1≤p)]` and `1≤q`,
  `‖H_ε‖_{L^q_tL^p_x}≤C_{p,q} ε^{alpha(p,q)+1}`.  The slice `MemLp`
  field above is the hygiene guard making each representing path honest. -/
  force_mixed_bound : ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)], 1 ≤ q →
    ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
      mixedLebesgueENormT q p (correctionForce ν v D ε) ≤
        ENNReal.ofReal
          (mixedConst p q * ε ^ (alphaT p q + 1))
  /-- `03-torus.tex:239-242`: real Sobolev constants fixed before `ε`.
  Non-vacuity: strict positivity below makes the displayed finite bound
  meaningful on the full `[0,1]` range. -/
  sobolevConst : ℝ → ℝ
  /-- `03-torus.tex:239-242`: `C_s>0` on `0≤s≤1`.
  Non-vacuity: strict positivity excludes a collapsed Sobolev coefficient. -/
  sobolevConst_pos : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → 0 < sobolevConst s
  /-- `03-torus.tex:239-242`: an honest `L¹_tH^s_x` Fourier-data path.
  Non-vacuity: `MemLp` makes the Bochner infimum in `forceSobolevENormT` honest. -/
  forceSobolev_memLp : ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
    ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
      MemForceSobolevT 1 s (correctionForce ν v D ε)
  /-- `03-torus.tex:239-242,284`: the `H^s` estimate, with its honest
  `MemForceSobolevT 1 s` guard and `0≤s≤1` quantifiers. -/
  force_sobolev_bound : ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
    ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
      forceSobolevENormT 1 s (correctionForce ν v D ε) ≤
        ENNReal.ofReal
          (sobolevConst s *
            (ε ^ ((3 : ℝ) / 2) + ε ^ ((3 : ℝ) / 2 - s)))

/-! ## Drift checks kept outside the API -/

example (p q : ℝ≥0∞) :
    -2 + 3 / p.toReal + 2 / q.toReal = alphaT p q + 1 := by
  simp [alphaT]
  ring

example (q p : ℝ≥0∞) [Fact (1 ≤ p)] (f : SpaceTimeField) :
    mixedLebesgueENormT q p f = NSFormalization.Section3.T15.mixedLebesgueENormT q p f := rfl

/-! The canonical existential shape corresponding to Spec.lean:980. -/
def correctionStatement : Prop :=
  ∀ (ν : ℝ) (u : VelocityField) (p : PressureField) (f : VelocityField)
    (K : Set Space) (place : PlacementData u p f K)
    (v : SpaceTimeField) (r δ : ℝ),
    ∃ D : CutoffData,
      LocalPotentialAPI v u place.Kstar place.x₀ r place.T δ D ∧
        Nonempty (CorrectionAPI ν place v r δ D)

end NSFormalization.Section3.T17
