import NSFormalization.Section3.T11.EnergyIdentity

/-!
# U12a probe — `eq:Rhigh` and the `higherOrderBound` target close

Two statements are copied **verbatim**:

* `hRhigh`, the exact hypothesis binder of
  `HighOrder.higherOrderBound_of_energyInequality` (lane 322), and
* the `higherOrderBound` field of `PeriodicContinuationAPI`
  (`research/T11/probes/api_on_canonical.lean:111-120`).

Both close from `EnergyIdentity.hRhigh_of_pairingBound` with the single U12b
pairing estimate as an explicit hypothesis.  The last section is the non-vacuity
witness: at the spatially homogeneous forced solution `u(t,x) = eᵗ c` with
`c ≠ 0` the energy identity determines a **strictly positive** derivative, so
neither the identity nor its hypotheses are vacuous.
-/

noncomputable section

namespace NSFormalization.Section3.T11.EnergyIdentityProbe

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField SpaceTimeScalar)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T11
open scoped ContDiff ENNReal BigOperators ComplexConjugate

local instance energyProbeNormedGroup (s : ℝ) : NormedAddCommGroup (PeriodicSobolev s) :=
  realPeriodicSubmodule.normedAddCommGroup
local instance energyProbeNormedSpace (s : ℝ) : NormedSpace ℝ (PeriodicSobolev s) :=
  realPeriodicSubmodule.normedSpace

/-- The U12b pairing estimate, as an explicit hypothesis (not a named input). -/
abbrev PairingBoundHypothesis (Chigh : ℕ → ℝ) : Prop :=
  ∀ (ν : ℝ), 0 < ν → ∀ (a : SpatialField), a ∈ initialClassT →
    ∀ (f : SpaceTimeField), f ∈ forceClassT →
      ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T) (m : ℕ), 3 ≤ m →
        ∀ t ∈ Ioo (0 : ℝ) T, ∀ Gm Nm : PeriodicSobolev (m : ℝ),
          IsPeriodicDatum (m : ℝ) (fun x ↦ w.velocity (t, x)) Gm →
          IsPeriodicDatum (m : ℝ) (fun x ↦ convectionFieldT w.velocity (t, x)) Nm →
          |torusRealPairing Gm Nm| ≤
            Chigh m * torusSobolevNormAt 2 w.velocity t *
              torusSobolevNormAt (m : ℝ) w.velocity t *
              torusGradientNormAt (m : ℝ) w.velocity t

/-- **`eq:Rhigh` closes**, in exactly the binder lane 322 consumes. -/
theorem hRhigh_closes (Chigh : ℕ → ℝ) (hpair : PairingBoundHypothesis Chigh) :
    ∀ (ν : ℝ), 0 < ν → ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T) (m : ℕ), 3 ≤ m →
          ∀ t ∈ Ioo (0 : ℝ) T, ∃ d g : ℝ, 0 ≤ g ∧
            HasDerivAt (fun r ↦ torusSobolevNormAt (m : ℝ) w.velocity r ^ 2) d t ∧
            (1 / 2) * d + ν * g ^ 2 ≤
              Chigh m * torusSobolevNormAt 2 w.velocity t *
                  torusSobolevNormAt (m : ℝ) w.velocity t * g +
                torusSobolevNormAt (m : ℝ) f t * torusSobolevNormAt (m : ℝ) w.velocity t :=
  hRhigh_of_pairingBound Chigh hpair

/-- **The `higherOrderBound` target field closes**, verbatim. -/
theorem higherOrderBound_closes (Chigh : ℕ → ℝ) (hpair : PairingBoundHypothesis Chigh) :
    ∀ (ν : ℝ), 0 < ν →
      ∀ (a : SpatialField), a ∈ initialClassT →
        ∀ (f : SpaceTimeField), f ∈ forceClassT →
          ∀ (S : ℝ), 0 < S →
            ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
              SolvesBelowT ν a f S u p → squaredHTwoIntegralT S u ≠ ⊤ →
                ∀ m : ℕ, ∃ M : ℝ≥0∞, M ≠ ⊤ ∧
                  ∀ t ∈ Ico (0 : ℝ) S,
                    periodicSobolevENorm (m : ℝ) (fun x ↦ u (t, x)) ≤ M :=
  higherOrderBound_of_pairingBound Chigh hpair

/-! ## Non-vacuity at a nonzero, genuinely forced classical solution -/

/-- `u(t,x) = eᵗc`, `p = 0`, `f(t,x) = eᵗc`: a genuine `ClassicalSolutionT`. -/
def expSolution (ν T : ℝ) (hT : 0 < T) (c : Space) :
    ClassicalSolutionT ν (fun _ ↦ c) (fun z ↦ Real.exp z.1 • c) T :=
  torusHomogeneousSolution ν T hT c Real.exp Real.exp Real.contDiff_exp Real.exp_zero
    Real.hasDerivAt_exp

theorem expSolution_force_contDiff (c : Space) :
    ContDiff ℝ ∞ (fun z : SpaceTime ↦ Real.exp z.1 • c) :=
  (Real.contDiff_exp.comp contDiff_fst).smul contDiff_const

/-- A nonzero constant vector has a nonzero zero-mode datum. -/
theorem norm_torusConstantDatum_pos (s : ℝ) {c : Space} (hc : c ≠ 0) :
    0 < ‖torusConstantDatum s c‖ := by
  obtain ⟨i, hi⟩ : ∃ i : Fin 3, c i ≠ 0 := by
    by_contra h
    exact hc (by ext i; exact not_not.mp fun hni ↦ h ⟨i, hni⟩)
  have hentry : (torusConstantDatum s c).1 i 0 = ((c i : ℝ) : ℂ) := by
    change (lp.single 2 (0 : PeriodicFrequency) ((c i : ℝ) : ℂ) : PeriodicScalarData) 0 = _
    simp
  have hle : ‖((c i : ℝ) : ℂ)‖ ≤ ‖torusConstantDatum s c‖ := by
    rw [← hentry]
    exact norm_coeff_le_norm _ i 0
  have hpos : 0 < ‖((c i : ℝ) : ℂ)‖ := by
    simpa using abs_pos.mpr hi
  linarith

/-- The `H^m` profile of the homogeneous solution is `e^{2r}‖K‖²`. -/
theorem expSolution_profile (ν T : ℝ) (hT : 0 < T) (c : Space) (m : ℕ) (r : ℝ) :
    torusSobolevNormAt (m : ℝ) (expSolution ν T hT c).velocity r ^ 2 =
      Real.exp r ^ 2 * ‖torusConstantDatum (m : ℝ) c‖ ^ 2 := by
  have hd : IsPeriodicDatum (m : ℝ)
      (fun x ↦ (expSolution ν T hT c).velocity (r, x))
      (Real.exp r • torusConstantDatum (m : ℝ) c) :=
    torusConstantDatum_smul (m : ℝ) (Real.exp r) c
  rw [torusSobolevNormAt_eq hd, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos r), mul_pow]

/-- **Non-vacuity.**  At `c ≠ 0` the energy identity of `expSolution` fixes a
strictly positive value for `−2ν‖∇u‖²_{H^m} − 2⟪(u·∇)u,u⟫_{H^m} + 2⟪f,u⟫_{H^m}`,
namely `2e^{2t}‖K‖² > 0`.  Nothing here is vacuous: the solution is nonzero, the
force is nonzero, and the three data hypotheses are satisfied. -/
theorem energyIdentity_positive (ν T : ℝ) (hT : 0 < T) {c : Space} (hc : c ≠ 0) (m : ℕ)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) {Gm Fm Nm : PeriodicSobolev (m : ℝ)}
    (hGm : IsPeriodicDatum (m : ℝ)
      (fun x ↦ (expSolution ν T hT c).velocity (t, x)) Gm)
    (hFm : IsPeriodicDatum (m : ℝ) (fun _ : Space ↦ Real.exp t • c) Fm)
    (hNm : IsPeriodicDatum (m : ℝ)
      (fun x ↦ convectionFieldT (expSolution ν T hT c).velocity (t, x)) Nm) :
    -2 * ν * torusGradientNormAt (m : ℝ) (expSolution ν T hT c).velocity t ^ 2 +
        2 * torusRealPairing Gm Fm - 2 * torusRealPairing Gm Nm =
      2 * Real.exp t ^ 2 * ‖torusConstantDatum (m : ℝ) c‖ ^ 2 ∧
    0 < 2 * Real.exp t ^ 2 * ‖torusConstantDatum (m : ℝ) c‖ ^ 2 := by
  have hid := energyIdentity_of_classical (expSolution ν T hT c)
    (expSolution_force_contDiff c) m ht hGm hFm hNm
  have hprof : (fun r ↦ torusSobolevNormAt (m : ℝ) (expSolution ν T hT c).velocity r ^ 2) =
      fun r ↦ Real.exp r ^ 2 * ‖torusConstantDatum (m : ℝ) c‖ ^ 2 :=
    funext fun r ↦ expSolution_profile ν T hT c m r
  rw [hprof] at hid
  have hexp : HasDerivAt (fun r ↦ Real.exp r ^ 2 * ‖torusConstantDatum (m : ℝ) c‖ ^ 2)
      (2 * Real.exp t ^ 2 * ‖torusConstantDatum (m : ℝ) c‖ ^ 2) t := by
    have h := ((Real.hasDerivAt_exp t).pow 2).mul_const
      (‖torusConstantDatum (m : ℝ) c‖ ^ 2)
    refine h.congr_deriv ?_
    push_cast
    ring
  refine ⟨hid.unique hexp, ?_⟩
  have h1 : 0 < Real.exp t ^ 2 := pow_pos (Real.exp_pos t) 2
  have h2 : 0 < ‖torusConstantDatum (m : ℝ) c‖ ^ 2 :=
    pow_pos (norm_torusConstantDatum_pos (m : ℝ) hc) 2
  positivity

/-! ## The projected coefficient equation, and the Leray identification -/

/-- `lerayAt` is exactly `T10.Leray`'s `periodicLeray` symbol at each frequency
(`MildMomentum.periodicLeray_eq_lerayAt`, a `rfl` bridge). -/
example (s : ℝ) (A : PeriodicSobolev s) (i : Fin 3) (k : PeriodicFrequency) :
    periodicLeray s A i k = lerayAt k (fun j ↦ A.1 j k) i := rfl

/-- **The brief's projected coefficient equation closes**, verbatim:
`d/dt û(t)(k) = −ν·4π²|k|²·û(t)(k) + (P̂(f̂(t) − Q̂(t)))(k)`. -/
theorem projected_momentum_closes {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionT ν a f T) (hf : ContDiff ℝ ∞ f) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) T) (i : Fin 3) (k : PeriodicFrequency) :
    velocityDerivCoeffT w.velocity i k t =
      ((-(ν * (4 * Real.pi ^ 2 * ∑ j : Fin 3, (k j : ℝ) ^ 2)) : ℝ) : ℂ) *
          velocityCoeffT w.velocity i k t +
        lerayAt k (fun j ↦ velocityCoeffT f j k t -
          velocityCoeffT (convectionFieldT w.velocity) j k t) i :=
  velocityDerivCoeffT_momentum_projected w hf ht i k

/-! ## Definitional checks -/

/-- The convection field is `(u·∇)u` at every point. -/
example (u : SpaceTimeField) (t : ℝ) (x : Space) :
    convectionFieldT u (t, x) = advection u t x := rfl

/-- `torusGradientNormAt` is the square root of the weighted dissipation sum. -/
example (s : ℝ) (u : SpaceTimeField) (t : ℝ) :
    torusGradientNormAt s u t =
      Real.sqrt (∑' k, periodicFrequencyWeight k ^ s * periodicAngularFrequencySq k *
        ∑ i : Fin 3, ‖velocityCoeffT u i k t‖ ^ 2) := rfl

end NSFormalization.Section3.T11.EnergyIdentityProbe
