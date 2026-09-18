import NSFormalization.Section3.T22.CutoffMultiplierField

/-!
# Probe for `cutoffMultiplier` (T22 · U-A3b)

(a) `cutoffMultiplier` inhabits the `BoundedDomainNormAPI.cutoffMultiplier` field
    type verbatim (both directions: the projection has that type, and the theorem
    closes it by `exact`).
(b) Non-vacuity at a concrete **nonzero** cutoff and a concrete **nonzero** datum:
    the cutoff is a `ContDiffBump` with `χ 0 = 1`, the datum is the angular datum of
    the (real, hence conjugate-reflection symmetric) complexified bump, it is
    nonzero, and its extended norm is nonzero and finite — so the produced bound
    `‖B‖ₑ ≤ ofReal C * ‖A‖ₑ` is a genuine finite inequality, not `x ≤ ⊤` or `0 ≤ 0`.
-/

noncomputable section
namespace T22ProbeA3b

open MeasureTheory NavierStokes.ProblemStatement Metric
open NSFormalization.Paper3
open NSFormalization.Source.RealSobolev
  (FourierData RealSobolevHilbert realSymmetry realSubspace mem_realSubspace_iff
    conjugateSchwartz conjugateSchwartz_apply)
open NSFormalization.Section3.T22
open scoped ContDiff ENNReal SchwartzMap

/-! ## (a) the field type -/

example : BoundedDomainNormAPI →
    (∀ (s : ℝ) (χ : Space → ℝ), ContDiff ℝ ∞ χ → HasCompactSupport χ →
      ∃ C : ℝ, 0 < C ∧ ∀ A : RealVectorSobolev s,
        ∃ B : RealVectorSobolev s,
          IsCutoffDatum s χ A B ∧ ‖B‖ₑ ≤ ENNReal.ofReal C * ‖A‖ₑ) :=
  BoundedDomainNormAPI.cutoffMultiplier

example : ∀ (s : ℝ) (χ : Space → ℝ), ContDiff ℝ ∞ χ → HasCompactSupport χ →
    ∃ C : ℝ, 0 < C ∧ ∀ A : RealVectorSobolev s,
      ∃ B : RealVectorSobolev s,
        IsCutoffDatum s χ A B ∧ ‖B‖ₑ ≤ ENNReal.ofReal C * ‖A‖ₑ :=
  cutoffMultiplier

/-! ## (b) a concrete nonzero cutoff and a concrete nonzero datum -/

def bump : ContDiffBump (0 : Space) := ⟨1, 2, one_pos, one_lt_two⟩

def chi : Space → ℝ := fun x => bump x

theorem chi_contDiff : ContDiff ℝ ∞ chi := bump.contDiff

theorem chi_compact : HasCompactSupport chi := bump.hasCompactSupport

theorem chi_zero : chi 0 = 1 :=
  bump.one_of_mem_closedBall (mem_closedBall_self zero_le_one)

/-- The complexified bump, as a Schwartz function. -/
def psi : SchwartzMap Space ℂ := cutoffSchwartz chi_contDiff chi_compact

theorem psi_conj : conjugateSchwartz psi = psi := by
  ext x
  rw [conjugateSchwartz_apply, psi, cutoffSchwartz_apply, Complex.conj_ofReal]

theorem psi_ne_zero : psi ≠ 0 := by
  intro h
  have h0 : psi 0 = 0 := by rw [h]; rfl
  rw [psi, cutoffSchwartz_apply, chi_zero, Complex.ofReal_one] at h0
  exact one_ne_zero h0

theorem angularDatum_psi_mem (s : ℝ) : angularDatum s psi ∈ realSubspace s := by
  rw [mem_realSubspace_iff, realSymmetry_angularDatum, psi_conj]

theorem angularDatum_psi_ne_zero (s : ℝ) : angularDatum s psi ≠ 0 := by
  intro h
  have h1 : (psi : 𝓢'(Space, ℂ)) = 0 := by
    have := angularRealization_datum s psi
    rw [h, map_zero] at this
    exact this.symm
  have h2 : ((psi.toLp 2 (volume : Measure Space) : Lp ℂ 2 (volume : Measure Space)) :
      𝓢'(Space, ℂ)) = 0 := by
    rw [MeasureTheory.Lp.toTemperedDistribution_toLp_eq]
    exact h1
  have h3 : psi.toLp 2 (volume : Measure Space) = 0 := by
    have hinj : Function.Injective (Lp.toTemperedDistributionCLM ℂ (volume : Measure Space) 2) :=
      LinearMap.ker_eq_bot.mp Lp.ker_toTemperedDistributionCLM_eq_bot
    apply hinj
    rw [map_zero]
    exact h2
  have hz : (0 : SchwartzMap Space ℂ).toLp 2 (volume : Measure Space) = 0 := by
    simpa using (SchwartzMap.toLpCLM ℝ ℂ 2 (volume : Measure Space)).map_zero
  have h4 : psi = 0 := by
    apply SchwartzMap.injective_toLp 2 (volume : Measure Space)
    show psi.toLp 2 (volume : Measure Space) = (0 : SchwartzMap Space ℂ).toLp 2 volume
    rw [h3, hz]
  exact psi_ne_zero h4

/-- The concrete nonzero datum: three copies of the angular datum of the bump. -/
def datum (s : ℝ) : RealVectorSobolev s :=
  WithLp.toLp 2 (fun _ : Fin 3 => (⟨angularDatum s psi, angularDatum_psi_mem s⟩ :
    RealSobolevHilbert s))

theorem datum_ne_zero (s : ℝ) : datum s ≠ 0 := by
  intro h
  have h0 : (datum s) 0 = 0 := by rw [h]; rfl
  have h1 : ((datum s) 0 : FourierData) = angularDatum s psi := rfl
  rw [h0] at h1
  exact angularDatum_psi_ne_zero s h1.symm

/-- **Non-vacuity.**  For every real order `s` the field's conclusion holds at the
concrete nonzero cutoff `chi` and the concrete nonzero datum `datum s`, with a
positive constant and a datum norm that is neither `0` nor `⊤`. -/
theorem probe_closes (s : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∃ B : RealVectorSobolev s,
      IsCutoffDatum s chi (datum s) B ∧
        ‖B‖ₑ ≤ ENNReal.ofReal C * ‖datum s‖ₑ ∧
        ‖datum s‖ₑ ≠ 0 ∧ ‖datum s‖ₑ < ⊤ ∧ chi 0 ≠ 0 := by
  obtain ⟨C, hC, hall⟩ := cutoffMultiplier s chi chi_contDiff chi_compact
  obtain ⟨B, hgraph, hnorm⟩ := hall (datum s)
  refine ⟨C, hC, B, hgraph, hnorm, ?_, ?_, ?_⟩
  · exact enorm_ne_zero.mpr (datum_ne_zero s)
  · exact enorm_lt_top
  · rw [chi_zero]; exact one_ne_zero

end T22ProbeA3b
