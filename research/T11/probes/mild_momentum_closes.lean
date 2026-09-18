import NSFormalization.Section3.T11.MildMomentum

/-! # U9d2b probe: which momentum/time-regularity targets close

Every `example` below copies a target statement verbatim — either a field of
`Section3/T10/PeriodicData.lean`'s `ClassicalSolutionT`, a field of
`Section3/T11/LocalTheory.lean`'s `PeriodicLocalRegularity`, or the
differentiation goal of the U9d2b brief — with
`velocity := torusPhysicalVelocity u` and (where a pressure is needed) either an
arbitrary pressure with the required gradient data or lane 326's
`mildPressure g u`.

**Not closed here** (exact residuals in `REPORT_327.md` §3 and
`ATTEMPTS_MILD_MOMENTUM.md` §3):

```
velocity_smooth : ContDiffOn ℝ ∞ (torusPhysicalVelocity u) (Ico (0:ℝ) T ×ˢ (univ : Set Space))
pressure_smooth : ContDiffOn ℝ ∞ (mildPressure g u)          (Ico (0:ℝ) T ×ˢ (univ : Set Space))
```

i.e. the *joint* `C^∞` fields.  The first time derivative exists and is
identified (`torusPhysicalVelocity_hasDerivAt`), but iterating it needs the
Duhamel formula at every Sobolev order, which `TorusForcedMildOn` (an `H³`
statement) does not supply.
-/
noncomputable section
open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField SpaceTimeScalar)
open NSFormalization.Section3.T10 NSFormalization.Section3.T11
open scoped ContDiff BigOperators

local instance probeNormedGroup (s : ℝ) : NormedAddCommGroup (PeriodicSobolev s) :=
  realPeriodicSubmodule.normedAddCommGroup
local instance probeNormedSpace (s : ℝ) : NormedSpace ℝ (PeriodicSobolev s) :=
  realPeriodicSubmodule.normedSpace

variable {ν T : ℝ} {C : TorusTwoSpaceContract ν} {Ad : PeriodicSobolev 3}
  {g : SpaceTimeField} {F P u : ℝ → PeriodicSobolev 3} {p : SpaceTimeScalar}

/-! ## (i) Time differentiability of the coefficient paths (weighted form) -/

example (hmild : TorusForcedMildOn C Ad P T u) (hPc : ContinuousOn P (Icc (0 : ℝ) T))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) (i : Fin 3) (k : PeriodicFrequency) :
    HasDerivAt (fun r : ℝ ↦ (u r).1 i k)
      ((-(ν * periodicAngularFrequencySq k) : ℝ) * (u t).1 i k +
        ((P t).1 i k -
          (Real.sqrt (periodicFrequencyWeight k) : ℂ) *
            (mildNonlinearDatum C u t).1 i k)) t :=
  mild_coeff_hasDerivAt hmild hPc ht i k

/-! ## (i) Time differentiability of the coefficient paths (physical form) -/

example (hmild : TorusForcedMildOn C Ad P T u) (hPc : ContinuousOn P (Icc (0 : ℝ) T))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) (i : Fin 3) (k : PeriodicFrequency) :
    HasDerivAt (fun r : ℝ ↦ torusPhysicalCoeff 3 (u r) i k)
      ((-(ν * periodicAngularFrequencySq k) : ℝ) * torusPhysicalCoeff 3 (u t) i k +
        (torusPhysicalCoeff 3 (P t) i k -
          torusPhysicalCoeff 2 (mildNonlinearDatum C u t) i k)) t :=
  mild_physicalCoeff_hasDerivAt hmild hPc ht i k

/-! ## (ii) The first time derivative of the physical velocity -/

example (hmild : TorusForcedMildOn C Ad P T u) (hPc : ContinuousOn P (Icc (0 : ℝ) T))
    (hu : PersistenceInput T u) (hg : ContDiff ℝ ∞ g) (hgp : IsPeriodicOn univ g)
    (hFg : IsPeriodicSobolevPath 3 g F)
    (hPL : ∀ t : ℝ, 0 ≤ t → IsPeriodicLerayDatum (F t) (P t))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) (x : Space) :
    HasDerivAt (fun r : ℝ ↦ torusPhysicalVelocity u (r, x))
      (mildTimeDerivative C P u t x) t := by
  have hab : Icc (t / 2) ((t + T) / 2) ⊆ Ico (0 : ℝ) T := fun r hr ↦
    ⟨le_trans (by linarith [ht.1]) hr.1, lt_of_le_of_lt hr.2 (by linarith [ht.2])⟩
  exact torusPhysicalVelocity_hasDerivAt hmild hPc hu hg hgp hFg hPL hab
    (by linarith [ht.1, ht.2]) ⟨by linarith [ht.1], by linarith [ht.2]⟩ x

/-! ## The force side of `PersistenceInput` is discharged, not assumed -/

example (hg : ContDiff ℝ ∞ g) (hgp : IsPeriodicOn univ g)
    (hFg : IsPeriodicSobolevPath 3 g F) : PersistenceInput T F :=
  persistenceInput_force_of_smooth hg hgp hFg

/-! ## (ii) Continuity of the physical velocity up to `t = 0` -/

example (hmild : TorusForcedMildOn C Ad P T u) :
    ContinuousOn (torusPhysicalVelocity u) (Icc (0 : ℝ) T ×ˢ (univ : Set Space)) :=
  torusForcedMildOn_physical_continuous hmild

/-! ## The Leray form of the contract's nonlinearity

(The convection identity itself — the physical tensor divergence is the
canonical `torusConvectionDatum` — is lane 326's
`periodicFourierCoeff_convection_eq_torusConvectionDatum`; this lane adds the
projected form.) -/

example {ν : ℝ} (C : TorusTwoSpaceContract ν) (A B : PeriodicSobolev 3)
    (i : Fin 3) (k : PeriodicFrequency) :
    torusPhysicalCoeff 2 (C.analytic.bilinear A B) i k =
      lerayAt k (fun j ↦ torusPhysicalCoeff 2 (torusConvectionDatum A B) j k) i :=
  torusPhysicalCoeff_bilinear C A B i k

/-! ## `ClassicalSolutionT.momentum`, verbatim, for a qualifying pressure -/

example (hmild : TorusForcedMildOn C Ad P T u) (hPc : ContinuousOn P (Icc (0 : ℝ) T))
    (hu : PersistenceInput T u)
    (hPL : ∀ t : ℝ, 0 ≤ t → IsPeriodicLerayDatum (F t) (P t))
    (hg : ContDiff ℝ ∞ g) (hgp : IsPeriodicOn univ g)
    (hFg : IsPeriodicSobolevPath 3 g F)
    (hps : ∀ t ∈ Ico (0 : ℝ) T, ContDiff ℝ ∞ (fun x : Space ↦ p (t, x)))
    (hpp : IsPeriodicOn univ p)
    (hpgrad : ∀ t ∈ Ico (0 : ℝ) T, ∀ (i : Fin 3) (k : PeriodicFrequency),
      periodicFourierCoeff (fun x ↦ ((pressureGradient p t x i : ℝ) : ℂ)) k =
        sourceComponentCoeff (fun x ↦ mildPressureSource g u (t, x)) i k -
          lerayAt k
            (fun j ↦ sourceComponentCoeff (fun x ↦ mildPressureSource g u (t, x)) j k) i)
    (hdivfree : ∀ t ∈ Ico (0 : ℝ) T, ∀ y : Space,
      spatialDivergence (torusPhysicalVelocity u) t y = 0) :
    ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : Space,
      NavierStokesR3.ProblemStatement.navierStokesResidual ν (torusPhysicalVelocity u) p t x =
        g (t, x) :=
  fun _ ht x ↦ momentum_of_pressure hmild hPc hu hPL hg hgp hFg hps hpp hpgrad hdivfree ht x

/-! ## `ClassicalSolutionT.momentum`, verbatim, for lane 326's `mildPressure` -/

example (hmild : TorusForcedMildOn C Ad P T u) (hPc : ContinuousOn P (Icc (0 : ℝ) T))
    (hu : PersistenceInput T u)
    (hPL : ∀ t : ℝ, 0 ≤ t → IsPeriodicLerayDatum (F t) (P t))
    (hg : ContDiff ℝ ∞ g) (hgp : IsPeriodicOn univ g)
    (hFg : IsPeriodicSobolevPath 3 g F)
    (hdivfree : ∀ t ∈ Ico (0 : ℝ) T, ∀ y : Space,
      spatialDivergence (torusPhysicalVelocity u) t y = 0) :
    ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : Space,
      NavierStokesR3.ProblemStatement.navierStokesResidual ν (torusPhysicalVelocity u)
        (mildPressure g u) t x = g (t, x) :=
  fun _ ht x ↦ momentum_of_mildPressure hmild hPc hu hPL hg hgp hFg hdivfree ht x

/-! ## `PeriodicLocalRegularity.projected`, verbatim -/

example (hmild : TorusForcedMildOn C Ad P T u) (hPc : ContinuousOn P (Icc (0 : ℝ) T))
    (hu : PersistenceInput T u)
    (hPL : ∀ t : ℝ, 0 ≤ t → IsPeriodicLerayDatum (F t) (P t))
    (hg : ContDiff ℝ ∞ g) (hgp : IsPeriodicOn univ g)
    (hFg : IsPeriodicSobolevPath 3 g F)
    (hdivfree : ∀ t ∈ Ico (0 : ℝ) T, ∀ y : Space,
      spatialDivergence (torusPhysicalVelocity u) t y = 0) :
    ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : Space,
      temporalDerivative (torusPhysicalVelocity u) t x -
          ν • spatialLaplacian (torusPhysicalVelocity u) t x =
        (g (t, x) - convectionDivergenceT (torusPhysicalVelocity u) t x) -
          pressureGradient (mildPressure g u) t x :=
  fun _ ht x ↦ projected_of_mildPressure hmild hPc hu hPL hg hgp hFg hdivfree ht x

/-! ## Non-vacuity of the whole differentiation package -/

example : ∃ (C : TorusTwoSpaceContract 1) (u : ℝ → PeriodicSobolev 3),
    TorusForcedMildOn C (torusConstantDatum 3 (coordinateVector 0))
      (fun _ ↦ torusConstantDatum 3 (coordinateVector 0)) 1 u ∧
    PersistenceInput 1 u ∧
    (∀ t ∈ Ioo (0 : ℝ) 1, ∀ (i : Fin 3) (k : PeriodicFrequency),
      HasDerivAt (fun r : ℝ ↦ (u r).1 i k)
        ((-(1 * periodicAngularFrequencySq k) : ℝ) * (u t).1 i k +
          ((torusConstantDatum 3 (coordinateVector 0)).1 i k -
            (Real.sqrt (periodicFrequencyWeight k) : ℂ) *
              (mildNonlinearDatum C u t).1 i k)) t) ∧
    u 0 ≠ 0 :=
  mildMomentum_nonzero_instance

end
