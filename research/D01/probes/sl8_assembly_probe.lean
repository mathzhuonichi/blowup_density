/-
  SL8 end-to-end assembly probe — recipe for the P2 assembly lane.

  Written by the lane-111 reviewer (`research/D01/REVIEW_SL8_PREP.md` §6); preserved here per the
  coordinator's ACCEPT-WITH-NOTES follow-up.  It re-derives the whole `SL8_SPLIT.md` table
  (rows i.1 … iii.3) and terminates in `row_iii3`, producing P2:
  `SmoothSquareIntegrableJets (fun x => pressureGradient u.pressure t x)`.

  Stand-ins (this worktree predates lanes 106/108, which have since merged into
  origin/erenup/integration and are NOT present here):
    * lane 108's merged corollary is carried as the hypothesis `H108`, a character-for-character
      transcription of
      `NSFormalization.Section4.D01.Leray.lerayComplement_zero_orderZeroDatum_eq_self`
      (`OrderZeroCurl.lean:510`).  After rebase, delete `H108`/`h108` and call that lemma directly.
    * the `hcurl` input to i.6 uses 111's `partialDeriv_pressureGradient_symm`; after rebase prefer
      lane 106's `A01.PressureGauge.hasSymmetricJacobian_pressureGradient … .2 x i j` (reviewer-
      verified `rfl`-equal, strictly more general).

  The assembly lane (see `SL8_SPLIT.md` "Status summary") should rebase, import `OrderZeroCurl` (108)
  and `A01/PressureGauge` (106), drop the two stand-ins, and register `row_iii3` as the P2 contract
  field.  Compiles standalone here with `cd verification && lake env lean ../research/D01/probes/sl8_assembly_probe.lean` (silent).
-/

import NSFormalization.Section4.D01.OrderZeroAlgebra
import NSFormalization.Section4.D01.MomentumSlice
import NSFormalization.Section4.D01.OrderZeroSymbol
import NSFormalization.Section4.D01.Longitudinal
import NSFormalization.Section4.D01.LerayLowering

open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Section4.D01
open NSFormalization.Section4.A02 (ClassicalSolutionR)
open NSFormalization.Section4.A03 (partialDeriv)
open NSFormalization.Paper3 (RealVectorSobolev)
open NSFormalization.Source.RealSobolev (FourierData)
open scoped ContDiff

namespace Rev111Asm

variable {ν : ℝ} {a : Space → Space} {f : VelocityField} {T : ℝ}

/-- 108's corollary, transcribed verbatim, carried as a hypothesis. -/
abbrev H108 : Prop := ∀ {z : Space → Space} (hz : MemLp z 2 volume) (_hs : ContDiff ℝ ∞ z)
  (_hc : ∀ (i j : Fin 3) (x : Space), partialDeriv i z x j = partialDeriv j z x i),
  Leray.lerayComplement 0 (orderZeroDatum hz) = orderZeroDatum hz

/-! ### Row i.1 for `h` — NOT exported by lane 111, re-derived here. -/
theorem smoothL2_residual (u : ClassicalSolutionR ν a f T)
    (hf : NSFormalization.Section4.D01.MemForceR f) {t : ℝ} (ht : t ∈ Ioo (0:ℝ) T) :
    NSFormalization.Section4.A05.SmoothL2 (fun x : Space => f (t, x) - advection u.velocity t x
      + ν • spatialLaplacian u.velocity t x) :=
  smoothL2_add
    (smoothL2_sub (forceSlice_smoothL2_of_memForceR hf (le_of_lt ht.1))
      (advection_slice_smoothL2 u ht))
    (smoothL2_const_smul (laplacian_slice_smoothL2 u ht) ν)

/-! ### Row i.2: `datum⁰ ∂ₜu = datum⁰ h − datum⁰ ∇p`. -/
theorem row_i2 (u : ClassicalSolutionR ν a f T)
    (hf : NSFormalization.Section4.D01.MemForceR f) {t : ℝ} (ht : t ∈ Ioo (0:ℝ) T) :
    orderZeroDatum (memLp_temporalDerivative_slice u hf ht)
      = orderZeroDatum (smoothL2_residual u hf ht).memLp
        - orderZeroDatum (memLp_pressureGradient_slice u ht) := by
  rw [← orderZeroDatum_sub]
  exact isSobolevDatum_unique
    (isSobolevDatum_orderZeroDatum (memLp_temporalDerivative_slice u hf ht))
    (by
      have hcongr : (fun x : Space => f (t, x) - advection u.velocity t x
            + ν • spatialLaplacian u.velocity t x) - (fun x : Space => pressureGradient u.pressure t x)
          = fun x : Space => temporalDerivative u.velocity t x := by
        funext x; exact (temporalDerivative_slice_eq u ht x).symm
      exact hcongr ▸ isSobolevDatum_orderZeroDatum
        ((smoothL2_residual u hf ht).memLp.sub (memLp_pressureGradient_slice u ht)))

/-! ### Row i.4: `(I−P)₀ (datum⁰ ∂ₜu) = 0`. -/
theorem row_i4 (u : ClassicalSolutionR ν a f T)
    (hf : NSFormalization.Section4.D01.MemForceR f) {t : ℝ} (ht : t ∈ Ioo (0:ℝ) T) :
    Leray.lerayComplement 0 (orderZeroDatum (memLp_temporalDerivative_slice u hf ht)) = 0 :=
  Leray.lerayComplement_eq_zero_of_transverse 0 _
    (orderZeroDatum_transverse_of_divergence_free
      (memLp_temporalDerivative_slice u hf ht)
      (contDiff_temporalDerivative_slice u hf ht)
      (fun x => sum_partialDeriv_temporalDerivative_eq_zero u ht x))

/-! ### Row i.6 + i.7: `datum⁰ ∇p = (I−P)₀ (datum⁰ h)`. -/
theorem row_i7 (h108 : H108) (u : ClassicalSolutionR ν a f T)
    (hf : NSFormalization.Section4.D01.MemForceR f) {t : ℝ} (ht : t ∈ Ioo (0:ℝ) T) :
    orderZeroDatum (memLp_pressureGradient_slice u ht)
      = Leray.lerayComplement 0 (orderZeroDatum (smoothL2_residual u hf ht).memLp) := by
  have hi6 : Leray.lerayComplement 0 (orderZeroDatum (memLp_pressureGradient_slice u ht))
      = orderZeroDatum (memLp_pressureGradient_slice u ht) :=
    h108 _ (contDiff_pressureGradient_slice u.pressure_smooth ⟨le_of_lt ht.1, ht.2⟩)
      (fun i j x => partialDeriv_pressureGradient_symm u ht i j x)
  have := congrArg (Leray.lerayComplement 0) (row_i2 u hf ht)
  rw [map_sub, row_i4 u hf ht, hi6] at this
  exact (sub_eq_zero.mp this.symm).symm

/-! ### Rows (ii) + (iii): bootstrap to all orders, i.e. P2. -/
theorem row_iii3 (h108 : H108) (u : ClassicalSolutionR ν a f T)
    (hf : NSFormalization.Section4.D01.MemForceR f) {t : ℝ} (ht : t ∈ Ioo (0:ℝ) T) :
    SmoothSquareIntegrableJets (fun x : Space => pressureGradient u.pressure t x) := by
  refine memHInfty_iff_smoothSquareIntegrableJets.mp
    ⟨contDiff_pressureGradient_slice u.pressure_smooth ⟨le_of_lt ht.1, ht.2⟩, fun m => ?_⟩
  obtain ⟨_, hjets⟩ := memHInfty_iff_smoothSquareIntegrableJets.mpr (smoothL2_residual u hf ht)
  obtain ⟨Am, hAm⟩ := hjets m
  have h0m : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
  refine ⟨Leray.lerayComplement (m:ℝ) Am, ?_⟩
  refine (Leray.isSobolevDatum_lower_iff h0m).mp ?_
  have hii1 : lowerVectorL (m:ℝ) 0 h0m Am
      = orderZeroDatum (smoothL2_residual u hf ht).memLp :=
    isSobolevDatum_unique (Leray.isSobolevDatum_lower h0m hAm)
      (isSobolevDatum_orderZeroDatum _)
  have hii2 : lowerVectorL (m:ℝ) 0 h0m (Leray.lerayComplement (m:ℝ) Am)
      = Leray.lerayComplement 0 (orderZeroDatum (smoothL2_residual u hf ht).memLp) := by
    rw [← Leray.lerayComplement_lowerVectorL, hii1]
  rw [hii2, ← row_i7 h108 u hf ht]
  exact isSobolevDatum_orderZeroDatum _

end Rev111Asm
