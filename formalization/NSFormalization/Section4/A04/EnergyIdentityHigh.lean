import NSFormalization.Section4.A04.PressureDrop
import NSFormalization.Section4.A04.NonlinearBound
import NSFormalization.Section4.A04.LaplacianAssembly
import NSFormalization.Section4.A04.DerivNorm
import NSFormalization.Section4.A03.OuterTameProduct
import NSFormalization.Section4.C01.VelocityJets

/-!
# eq:Rhigh (`energyIdentityHigh`) — the all-order energy inequality, assembled

`paper/sections/appendix-a-local-theory.tex:132-137` (eq:Rhigh):

```
½ (d/dt)‖u‖²_{H^m} + ν‖∇u‖²_{H^m}
   ≤ C_m ‖u‖_{H²} ‖u‖_{H^m} ‖∇u‖_{H^m} + ‖f‖_{H^m} ‖u‖_{H^m}   (m ≥ 3, t ∈ (0,T))
```

This is the **assembly** unit G1 of A04.  Every sub-lemma (`momentum_datum`,
`inner_datum_laplacian_le'`, `pressure_drop`, `inner_advection_bound_slice`,
`outerNormAt_le`, `inner_energy_Rhigh`, the datum path `HasSmoothSobolevPath`) is
already in tree; this module only chains them behind the manuscript's constant
`C_m` and the spec's `∀`-prefix.

* `Chigh m := A03.outerTameConst m` is eq:Rhigh's constant `C_m` (eq:tame's
  `6 · vectorTameConst`), with `Chigh_pos` from `A03.outerTameConst_pos`.
* `energyIdentityHigh_core` is the lane-121 reviewer's reconstruction, promoted
  **verbatim** from `research/A04/probes/energy_identity_high_probe.lean` (that
  probe = `research/A04/REVIEW_HPR.md` §5 + appendix D, `/tmp/rev121/assembly.lean`,
  which compiled first try, standard axioms).  Credit: lane-121 reviewer.
* `energyIdentityHigh` is the spec field `research/A04/Spec.lean:424-434`
  token-for-token, in the formalization vocabulary; it is `energyIdentityHigh_core`
  with the spec's unused `a ∈ initialClassR` hypothesis carried for fidelity
  (see `research/A04/ATTEMPTS_ENERGY_HIGH.md` for which hypotheses are load-bearing
  in the core).

"The pressure term vanishes by solenoidality" (`:137-138`) is discharged inside
`pressure_drop` by `ClassicalSolutionR.divergence`, which is why no pressure
appears on either side.
-/

noncomputable section

open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpaceTimeField SpatialField ClassicalSolutionR MemHInfty initialClassR)
open NSFormalization.Section4.D01
open NSFormalization.Paper3 (RealVectorSobolev)
open NSFormalization.Section4.A03 (outerTameConst MemHmVector)
open scoped ContDiff RealInnerProductSpace

namespace NSFormalization.Section4.A04

/-- eq:Rhigh's constant `C_m` (`appendix-a-local-theory.tex:132`), taken to be
eq:tame's `A03.outerTameConst m` (`= 6 · vectorTameConst m`), the constant of the
outer-product transport `outerNormAt_le` that supplies the nonlinear slot. -/
def Chigh (m : ℕ) : ℝ := NSFormalization.Section4.A03.outerTameConst m

/-- `Chigh` is strictly positive at every order, from `A03.outerTameConst_pos`. -/
theorem Chigh_pos (m : ℕ) : 0 < Chigh m :=
  NSFormalization.Section4.A03.outerTameConst_pos m

/-- **eq:Rhigh core** (`appendix-a-local-theory.tex:132-137`), the all-order energy
inequality on an interior time of a smooth-Sobolev-path solution, stated with the
explicit constant `outerTameConst m`.

Promoted **verbatim** from `research/A04/probes/energy_identity_high_probe.lean`
(the lane-121 reviewer's reconstruction, `research/A04/REVIEW_HPR.md` §5 +
appendix D).  Credit: lane-121 reviewer.  The chain:

* datum path `G` from `hpath m` (`HasSmoothSobolevPath`);
* `hd`  — `hasDerivAt_datumNormSq_of_contDiffOn` `.congr_of_eventuallyEq` through `sobolevNormAt_eq`;
* `hmom` — `momentum_datum`;
* `hlap` — `inner_datum_laplacian_le'`;
* `hpr`  — `pressure_drop` (lane 121);
* `hnl`  — `inner_advection_bound_slice` chained with `outerNormAt_le`;
* `hG`/`hF` — `sobolevNormAt_eq`;

fed into `inner_energy_Rhigh`. -/
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

/-- **eq:Rhigh** (`appendix-a-local-theory.tex:132-137`), the spec field
`research/A04/Spec.lean:424-434` `energyIdentityHigh` **token-for-token**, in the
formalization vocabulary (`Chigh m = A03.outerTameConst m`).

The hypotheses `0 < ν`, `a ∈ initialClassR`, and `HasSmoothSobolevPath T w.velocity`
are kept exactly as the spec states them.  Of these only `HasSmoothSobolevPath`
(the differentiability input) and `0 < ν` are load-bearing in the core; the
initial-class membership `a ∈ initialClassR` is unused by this route and is carried
solely for statement fidelity (recorded in `research/A04/ATTEMPTS_ENERGY_HIGH.md`).
`Chigh m` unfolds to `outerTameConst m`, so `energyIdentityHigh_core` discharges the
bound directly. -/
theorem energyIdentityHigh : ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ),
    0 < ν → a ∈ initialClassR → MemForceR f →
      ∀ w : ClassicalSolutionR ν a f T, HasSmoothSobolevPath T w.velocity →
        ∀ m : ℕ, 3 ≤ m → ∀ t ∈ Ioo (0 : ℝ) T,
          ∃ d : ℝ,
            HasDerivAt (fun r : ℝ => sobolevNormAt (m : ℝ) w.velocity r ^ 2) d t ∧
              (1 / 2) * d + ν * gradientSobolevNormAt (m : ℝ) w.velocity t ^ 2 ≤
                Chigh m * sobolevNormAt 2 w.velocity t *
                    sobolevNormAt (m : ℝ) w.velocity t *
                    gradientSobolevNormAt (m : ℝ) w.velocity t +
                  sobolevNormAt (m : ℝ) f t * sobolevNormAt (m : ℝ) w.velocity t := by
  intro ν a f T hν _ha hf w hpath m hm t ht
  exact energyIdentityHigh_core hν hf w hpath m hm ht

end NSFormalization.Section4.A04
