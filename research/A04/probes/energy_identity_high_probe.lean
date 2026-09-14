/-
# eq:Rhigh (`energyIdentityHigh`) assembly probe — reconstructed by the lane-121 reviewer

Preserved verbatim from the lane-121 review (`research/A04/REVIEW_HPR.md` §5 + appendix D,
`/tmp/rev121/assembly.lean`).  With lane 121's `pressure_drop` filling the last `hpr` slot, the
whole of `research/A04/Spec.lean:424-434` `energyIdentityHigh` assembles from in-tree lemmas —
the reviewer compiled this **first try**, standard axioms only, sizing the assembly lane at **S**.

This is a PROBE (namespace `Rev121Asm`), not the finished contract: the finished
`energyIdentityHigh` lane still needs `def Chigh (m : ℕ) := A03.outerTameConst m` + `Chigh_pos`,
the spec's exact ∀-prefix (its `a ∈ initialClassR` hypothesis is simply unused), and the
contract V1 field + binding + test.  No new mathematics remains.

## Lemma-per-slot recipe (`inner_energy_Rhigh` at `E = RealVectorSobolev (m:ℝ)`,
`C := Chigh m := A03.outerTameConst m`)

| slot | lemma(s) | file |
|---|---|---|
| datum path `G` | `hpath m` (`HasSmoothSobolevPath`, the spec's own hypothesis) | `A04/DerivNorm.lean:87` |
| `hd`  (`d = 2⟪G t, deriv G t⟫`) | `rfl` + `hasDerivAt_datumNormSq_of_contDiffOn` `.congr_of_eventuallyEq` through `sobolevNormAt_eq` | `A04/DerivNorm.lean:119,141`, `A04/Continuity.lean:84` |
| `hmom` | `momentum_datum` | `A04/MomentumDatum.lean:140` |
| `hlap` | `inner_datum_laplacian_le'` | `A04/LaplacianAssembly.lean:354` |
| `hpr`  | **`pressure_drop` (lane 121)** | `A04/PressureDrop.lean:216` |
| `hnl`  | `inner_advection_bound_slice` + `outerNormAt_le` (chained, `nlinarith`) | `A04/NonlinearBound.lean:186`, `A04/HighEnergy.lean:187` |
| `hG` / `hF` | `sobolevNormAt_eq` (`.symm`) | `A04/Continuity.lean:84` |

Higher-order velocity data (`hA'`/`hA` for the Laplacian) come from
`C01.velocity_slice_memHInfty` via `isSobolevDatum_castOrder`; `hL`/`hN` from
`laplacian_slice_smoothL2` / `advection_slice_smoothL2` (`A05.SmoothL2` defeq
`SmoothSquareIntegrableJets`); `hP` from lane 117's `exists_isSobolevDatum_pressureGradient_slice`;
`hF` from `hf.2 m`.  Verified: `#print axioms → [propext, Classical.choice, Quot.sound]`.
-/

import NSFormalization.Section4.A04.PressureDrop
import NSFormalization.Section4.A04.NonlinearBound
import NSFormalization.Section4.A04.LaplacianAssembly
import NSFormalization.Section4.A04.DerivNorm
import NSFormalization.Section4.C01.VelocityJets

open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Section4.A04
open NSFormalization.Section4.A02 (SpaceTimeField SpatialField ClassicalSolutionR MemHInfty)
open NSFormalization.Section4.D01
open NSFormalization.Paper3 (RealVectorSobolev)
open NSFormalization.Section4.A03 (outerTameConst MemHmVector)
open scoped ContDiff RealInnerProductSpace

namespace Rev121Asm

/-- Reviewer's reconstruction of `Spec.lean:424-434` `energyIdentityHigh`, with
`Chigh m := A03.outerTameConst m`. -/
theorem energyIdentityHigh_core
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (hν : 0 < ν) (hf : MemForceR f) (w : ClassicalSolutionR ν a f T)
    (hpath : HasSmoothSobolevPath T w.velocity)
    (m : ℕ) (hm : 3 ≤ m) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    ∃ d : ℝ,
      HasDerivAt (fun r : ℝ => sobolevNormAt (m : ℝ) w.velocity r ^ 2) d t ∧
        (1 / 2) * d + ν * gradientSobolevNormAt (m : ℝ) w.velocity t ^ 2 ≤
          outerTameConst m * sobolevNormAt 2 w.velocity t *
              sobolevNormAt (m : ℝ) w.velocity t *
              gradientSobolevNormAt (m : ℝ) w.velocity t +
            sobolevNormAt (m : ℝ) f t * sobolevNormAt (m : ℝ) w.velocity t := by
  have hm2 : 2 ≤ m := by omega
  have ht' : t ∈ Ico (0 : ℝ) T := ⟨le_of_lt ht.1, ht.2⟩
  obtain ⟨G, hGd, hGc⟩ := hpath m
  have hsl := NSFormalization.Section4.C01.velocity_slice_smoothL2 w ht'
  have hinf := NSFormalization.Section4.C01.velocity_slice_memHInfty w ht'
  -- higher-order data of the velocity slice (for the Laplacian dissipation)
  obtain ⟨A1, hA1⟩ := hinf.2 (m + 1)
  have hA' := isSobolevDatum_castOrder (cast_mid_order m) hA1
  obtain ⟨A2, hA2⟩ := hinf.2 (m + 2)
  have hA := isSobolevDatum_castOrder
    (show (((m + 2 : ℕ) : ℝ)) = ((m : ℝ) + 2) by push_cast; ring) hA2
  -- the four physical slice data
  obtain ⟨L, hL⟩ :=
    (memHInfty_iff_smoothSquareIntegrableJets.mpr (laplacian_slice_smoothL2 w ht)).2 m
  obtain ⟨N, hN⟩ :=
    (memHInfty_iff_smoothSquareIntegrableJets.mpr (advection_slice_smoothL2 w ht)).2 m
  obtain ⟨P, hP⟩ := exists_isSobolevDatum_pressureGradient_slice w hf ht m
  obtain ⟨Gf, hFpath, -, -, -⟩ := hf.2 m
  have hF : IsSobolevDatum (m : ℝ) (fun x : Space => f (t, x)) (Gf t) :=
    hFpath t (le_of_lt ht.1)
  refine ⟨2 * ⟪G t, deriv G t⟫, ?_, ?_⟩
  · refine (hasDerivAt_datumNormSq_of_contDiffOn hGc ht).congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
    rw [sobolevNormAt_eq (hGd r (Ioo_subset_Ico_self hr))]
  · -- hnl: chain the advection bound with the tame transport
    have hgrad0 : 0 ≤ gradientSobolevNormAt (m : ℝ) w.velocity t := ENNReal.toReal_nonneg
    have hadv := inner_advection_bound_slice w hm2 ht (hGd t ht') hN
    have htame := outerNormAt_le (u := w.velocity) (t := t) hm2
      (NSFormalization.Section4.A03.SmoothL2.memHmVector hsl m)
      (by simpa using sobolevENorm_velocity_ne_top w 2 ht')
      (sobolevENorm_velocity_ne_top w m ht')
    have hnl : - ⟪G t, N⟫ ≤ outerTameConst m * sobolevNormAt 2 w.velocity t *
        sobolevNormAt (m : ℝ) w.velocity t * gradientSobolevNormAt (m : ℝ) w.velocity t := by
      refine hadv.trans ?_
      have := mul_le_mul_of_nonneg_left htame hgrad0
      nlinarith [this]
    exact inner_energy_Rhigh (le_of_lt hν) rfl
      (momentum_datum w hf hm2 hGd hGc ht hL hN hP hF)
      (inner_datum_laplacian_le' m hsl (hGd t ht') hA' hA hL)
      (pressure_drop w hf ht (hGd t ht') hP)
      hnl
      (sobolevNormAt_eq (hGd t ht')).symm
      (sobolevNormAt_eq hF).symm

#print axioms energyIdentityHigh_core

end Rev121Asm
