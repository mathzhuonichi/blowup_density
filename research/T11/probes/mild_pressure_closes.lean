import NSFormalization.Section3.T11.MildPressure

/-! # U9d2a probe: which pressure fields of `ClassicalSolutionT` close

Every `example` below copies a field statement of
`Section3/T10/PeriodicData.lean`'s `ClassicalSolutionT` (or of
`Section3/T11/LocalTheory.lean`'s `PeriodicLocalRegularity`) verbatim, with
`pressure := mildPressure g u` and `velocity := torusPhysicalVelocity u`, under
the U9d hypotheses plus the single named input `PersistenceInput T u`.

**Not closed here** (recorded as the exact residual in `REPORT_326.md` and
`ATTEMPTS_MILD_PRESSURE.md`): the joint slab field

```
pressure_smooth : ContDiffOn ℝ ∞ (mildPressure g u) (Ico (0 : ℝ) T ×ˢ (univ : Set Space))
```

Only the spatial slices are proved `C^∞`; joint regularity in `(t, x)` needs
time regularity of `t ↦ p̂(t)(k)`, which is not available from
`PersistenceInput` alone.  The name of this file is the requested artifact name,
**not** a claim that the whole pressure package closes.
-/
noncomputable section
open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField SpaceTimeScalar)
open NSFormalization.Section3.T10 NSFormalization.Section3.T11
open scoped ContDiff BigOperators

variable {g : SpaceTimeField} {u : ℝ → PeriodicSobolev 3} {T : ℝ}

/-! ## `ClassicalSolutionT.pressure_periodic` -/

example : IsPeriodicOn (Ico (0 : ℝ) T) (mildPressure g u) :=
  fun t _ x j ↦ mildPressure_periodic g u t (mem_univ t) x j

/-! ## `ClassicalSolutionT.pressure_gauge` -/

example (hg : ContDiff ℝ ∞ g) (hgp : IsPeriodicOn univ g) (hu : PersistenceInput T u) :
    PressureGaugeT (Ico (0 : ℝ) T) (mildPressure g u) :=
  mildPressure_gauge hg hgp hu

/-! ## `ClassicalSolutionT.pressure_gradient` -/

example (hg : ContDiff ℝ ∞ g) (hgp : IsPeriodicOn univ g) (hu : PersistenceInput T u) :
    ∀ t ∈ Ico (0 : ℝ) T,
      MemLp (torusLift (fun x ↦ pressureGradient (mildPressure g u) t x)) 2
        periodicTorusMeasure :=
  mildPressure_gradient_memLp hg hgp hu

/-! ## Spatial half of `ClassicalSolutionT.pressure_smooth` -/

example (hg : ContDiff ℝ ∞ g) (hgp : IsPeriodicOn univ g) (hu : PersistenceInput T u)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    ContDiff ℝ ∞ (fun x : Space ↦ mildPressure g u (t, x)) :=
  mildPressure_spatial_contDiff hg hgp hu ht

/-! ## `PeriodicLocalRegularity.pressure_poisson` -/

example (hg : ContDiff ℝ ∞ g) (hgp : IsPeriodicOn univ g) (hu : PersistenceInput T u) :
    ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space,
      scalarSpatialLaplacianT (mildPressure g u) t x =
        spatialDivergence g t x -
          spatialDivergence
            (fun z : SpaceTime ↦
              convectionDivergenceT (torusPhysicalVelocity u) z.1 z.2) t x :=
  mildPressure_poisson hg hgp hu

/-! ## The Leray-complement construction, at the level of the T10 symbol -/

-- `2πi k p̂(k)` is exactly `(I - P) Ŝ(k)` for every datum `B` of the source.
example (S : SpatialField) {s : ℝ} {B : PeriodicSobolev s}
    (hB : IsPeriodicDatum s S B) {k : PeriodicFrequency} (hk : k ≠ 0) (i : Fin 3) :
    periodicDerivativeSymbol i k * lerayPotentialCoeff S k =
      torusPhysicalCoeff s B i k -
        ((periodicFrequencyWeight k ^ (-s / 2) : ℝ) : ℂ) * periodicLeray s B i k :=
  lerayPotentialCoeff_leray_complement hB hk i

-- `∇p` has the Leray-complement datum of `F - Q`.
example (hg : ContDiff ℝ ∞ g) (hgp : IsPeriodicOn univ g) (hu : PersistenceInput T u)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) {s : ℝ} {B : PeriodicSobolev s}
    (hB : IsPeriodicDatum s (fun x ↦ mildPressureSource g u (t, x)) B)
    {k : PeriodicFrequency} (hk : k ≠ 0) (i : Fin 3) :
    periodicFourierCoeff
      (fun x ↦ ((pressureGradient (mildPressure g u) t x i : ℝ) : ℂ)) k =
      torusPhysicalCoeff s B i k -
        ((periodicFrequencyWeight k ^ (-s / 2) : ℝ) : ℂ) * periodicLeray s B i k :=
  mildPressure_gradient_leray_complement hg hgp hu ht hB hk i

-- The source coefficient is `F(t) - Q(u(t), u(t))` in physical Fourier data.
example {F : ℝ → PeriodicSobolev 3} (hu : PersistenceInput T u)
    (hF : IsPeriodicSobolevPath 3 g F) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T)
    (j : Fin 3) (k : PeriodicFrequency) :
    sourceComponentCoeff (fun x ↦ mildPressureSource g u (t, x)) j k =
      torusPhysicalCoeff 3 (F t) j k -
        periodicFourierCoeff (fun x ↦
          ((convectionDivergenceT (torusPhysicalVelocity u) t x j : ℝ) : ℂ)) k :=
  mildPressureSourceCoeff_eq_force_sub_convection hu hF ht j k

/-! ## The bundle handed to the assembly lane, and non-vacuity -/

example (hg : ContDiff ℝ ∞ g) (hgp : IsPeriodicOn univ g) (hu : PersistenceInput T u) :
    MildPressureFields g u T :=
  mildPressure_fields hg hgp hu

/-- The concrete lattice mode used by the non-vacuity witnesses.  It lives here
rather than in the module so that every module declaration's transitive axiom
set is exactly `[propext, Classical.choice, Quot.sound]`; this plain datum and
the decidable inequality below need only `propext`. -/
def testFrequency : PeriodicFrequency := fun i ↦ if i = 0 then 1 else 0

theorem testFrequency_ne_zero : testFrequency ≠ 0 := by
  intro h
  have hc := congrFun h 0
  simp [testFrequency] at hc

theorem testFrequency_ne_neg : ¬ testFrequency = -testFrequency := by
  intro h
  have hc := congrFun h 0
  simp [testFrequency] at hc

theorem testFrequency_zero_ne_zero : testFrequency 0 ≠ 0 := by
  simp [testFrequency]

example : lerayPotential (testPressureSource testFrequency) ≠ 0 :=
  lerayPotential_testPressureSource_ne_zero testFrequency_ne_zero testFrequency_ne_neg
    testFrequency_zero_ne_zero

example :
    MildPressureFields (fun z : SpaceTime ↦ testPressureSource testFrequency z.2)
        (fun t : ℝ ↦ (1 + t) • torusConstantDatum 3 (coordinateVector 0)) 1 ∧
      (fun x : Space ↦ mildPressure (fun z : SpaceTime ↦ testPressureSource testFrequency z.2)
        (fun t : ℝ ↦ (1 + t) • torusConstantDatum 3 (coordinateVector 0)) (0, x)) ≠ 0 :=
  mildPressure_nonzero_instance testFrequency_ne_zero testFrequency_ne_neg
    testFrequency_zero_ne_zero (coordinateVector 0)

example : MildPressureFields (fun z : SpaceTime ↦ testPressureSource testFrequency z.2)
    (fun t : ℝ ↦ (1 + t) • torusConstantDatum 3 (coordinateVector 0)) 1 :=
  (mildPressure_nonzero_instance testFrequency_ne_zero testFrequency_ne_neg
    testFrequency_zero_ne_zero (coordinateVector 0)).1

/-! ## Canonical coefficient-side `F - Q` (review finding 1) -/

-- The periodic convolution theorem, proved in this lane.
example {f h : Space → ℂ} (hpf : IsPeriodicSpatial f) (hsf : ContDiff ℝ ∞ f)
    (hph : IsPeriodicSpatial h) (hsh : ContDiff ℝ ∞ h) (k : PeriodicFrequency) :
    periodicFourierCoeff (fun x ↦ f x * h x) k =
      ∑' l, periodicFourierCoeff f l * periodicFourierCoeff h (k - l) :=
  periodicFourierCoeff_mul hpf hsf hph hsh k

-- The physical convection coefficient IS the canonical `torusConvectionDatum`.
example (hu : PersistenceInput T u) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T)
    (i : Fin 3) (k : PeriodicFrequency) :
    periodicFourierCoeff
      (fun x ↦ ((convectionDivergenceT (torusPhysicalVelocity u) t x i : ℝ) : ℂ)) k =
      torusPhysicalCoeff 2 (torusConvectionDatum (u t) (u t)) i k :=
  periodicFourierCoeff_convection_eq_torusConvectionDatum hu ht i k

-- The reviewer's exact requested statement (`rev326_canonical_q_gap.lean`).
example {F : ℝ → PeriodicSobolev 3} (hu : PersistenceInput T u)
    (hF : IsPeriodicSobolevPath 3 g F) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T)
    (j : Fin 3) (k : PeriodicFrequency) :
    sourceComponentCoeff (fun x ↦ mildPressureSource g u (t, x)) j k =
      torusPhysicalCoeff 3 (F t) j k -
        torusPhysicalCoeff 2 (torusConvectionDatum (u t) (u t)) j k :=
  mildPressureSourceCoeff_eq_canonical hu hF ht j k

-- `∇p = (I − P)(F − Q)`, written out in canonical coefficient data.
example {F : ℝ → PeriodicSobolev 3} (hg : ContDiff ℝ ∞ g) (hgp : IsPeriodicOn univ g)
    (hu : PersistenceInput T u) (hF : IsPeriodicSobolevPath 3 g F)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) {k : PeriodicFrequency} (hk : k ≠ 0) (i : Fin 3) :
    periodicFourierCoeff
      (fun x ↦ ((pressureGradient (mildPressure g u) t x i : ℝ) : ℂ)) k =
      ((k i : ℂ) / ((∑ j : Fin 3, (k j : ℝ) ^ 2 : ℝ) : ℂ)) *
        ∑ j : Fin 3, (k j : ℂ) *
          (torusPhysicalCoeff 3 (F t) j k -
            torusPhysicalCoeff 2 (torusConvectionDatum (u t) (u t)) j k) :=
  mildPressure_gradient_canonical hg hgp hu hF ht hk i

-- The canonical order-two datum `G₂ - Q` of the source exists and is a datum.
example (hg : ContDiff ℝ ∞ g) (hgp : IsPeriodicOn univ g) (hu : PersistenceInput T u)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    ∃ G₂ : PeriodicSobolev 2, IsPeriodicDatum 2 (fun x : Space ↦ g (t, x)) G₂ ∧
      IsPeriodicDatum 2 (fun x ↦ mildPressureSource g u (t, x))
        (G₂ - torusConvectionDatum (u t) (u t)) :=
  mildPressureSource_exists_canonical_datum hg hgp hu ht

-- and the T10 Leray complement is taken literally at `G₂ - Q`.
example (hg : ContDiff ℝ ∞ g) (hgp : IsPeriodicOn univ g) (hu : PersistenceInput T u)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) {G₂ : PeriodicSobolev 2}
    (hG : IsPeriodicDatum 2 (fun x : Space ↦ g (t, x)) G₂)
    {k : PeriodicFrequency} (hk : k ≠ 0) (i : Fin 3) :
    periodicFourierCoeff
      (fun x ↦ ((pressureGradient (mildPressure g u) t x i : ℝ) : ℂ)) k =
      torusPhysicalCoeff 2 (G₂ - torusConvectionDatum (u t) (u t)) i k -
        ((periodicFrequencyWeight k ^ (-(2 : ℝ) / 2) : ℝ) : ℂ) *
          periodicLeray 2 (G₂ - torusConvectionDatum (u t) (u t)) i k :=
  mildPressure_gradient_leray_canonical hg hgp hu ht hG hk i

/-! ## The coefficient pressure is in every `H^m` (review finding 2) -/

example (hg : ContDiff ℝ ∞ g) (hgp : IsPeriodicOn univ g) (hu : PersistenceInput T u)
    (m : ℕ) : ∀ t ∈ Ico (0 : ℝ) T,
      NSFormalization.Section3.T12.MemPeriodicHmScalar m
        (fun x : Space ↦ mildPressure g u (t, x)) :=
  mildPressure_memPeriodicHm hg hgp hu m

example (hg : ContDiff ℝ ∞ g) (hgp : IsPeriodicOn univ g) (hu : PersistenceInput T u)
    (m : ℕ) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    ∃ A : PeriodicScalarData,
      NSFormalization.Section3.T12.IsPeriodicScalarDatum (m : ℝ)
        (fun x : Space ↦ mildPressure g u (t, x)) A ∧
        ∀ k, A k = (periodicFrequencyWeight k ^ ((m : ℝ) / 2) : ℝ) •
          mildPressureCoeff g u t k :=
  mildPressure_scalar_datum hg hgp hu m ht

