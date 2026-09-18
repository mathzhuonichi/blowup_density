import NSFormalization.Section3.T11.MildPressure

/-! Reviewer conformance probe (finding 1): the reported `F - Q` identity needs
the canonical coefficient convection datum, not an unevaluated physical Fourier
coefficient.

**Resolved by the review fix.**  The original line
`exact mildPressureSourceCoeff_eq_force_sub_convection hu hF ht j k` failed with
a type mismatch (quoted in `REVIEW_326-T11-U9d2a-pressure.md` §3.1); the lane now
proves the periodic convolution theorem `periodicFourierCoeff_mul`, hence
`periodicFourierCoeff_convection_eq_torusConvectionDatum`, hence the exact
statement below via `mildPressureSourceCoeff_eq_canonical`. -/
noncomputable section

open Set
open NSFormalization.Section4.A02 (SpaceTimeField)
open NSFormalization.Section3.T10 NSFormalization.Section3.T11

variable {g : SpaceTimeField} {u F : ℝ → PeriodicSobolev 3} {T : ℝ}

example (hu : PersistenceInput T u) (hF : IsPeriodicSobolevPath 3 g F)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) (j : Fin 3) (k : PeriodicFrequency) :
    sourceComponentCoeff (fun x ↦ mildPressureSource g u (t, x)) j k =
      torusPhysicalCoeff 3 (F t) j k -
        torusPhysicalCoeff 2 (torusConvectionDatum (u t) (u t)) j k := by
  exact mildPressureSourceCoeff_eq_canonical hu hF ht j k
