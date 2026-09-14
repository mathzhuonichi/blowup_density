import NSFormalization.Section4.D01.OrderZeroAlgebra
import NSFormalization.Section4.D01.MomentumSlice
import NSFormalization.Section4.D01.OrderZeroCurl
import NSFormalization.Section4.D01.OrderZeroSymbol
import NSFormalization.Section4.D01.LerayLowering

/-!
# eq:Rpressure at every order: `SmoothSquareIntegrableJets (∇p(t,·))` (unit D01 / P2 = SL8)

`research/D01/P2_SPLIT.md` obligation **P2**, sub-lemma **SL8** (`research/D01/SL8_SPLIT.md`).  The
final assembly of `paper/sections/02-preliminaries.tex:89-94` (eq:Rpressure): for a classical
solution `u : ClassicalSolutionR ν a f T` with real admissible force `hf : MemForceR f` and interior
time `t ∈ Ioo 0 T`, the pressure-gradient slice `∇p(t,·)` lies in `Contracts.V1.SmoothSquareIntegrableJets`.

Notation.  `h := f − (u·∇)u + νΔu` is the `H^∞` momentum residual
(`smoothL2_momentumResidual_slice`); `∂ₜu = h − ∇p` pointwise; `(I−P)₀ := Leray.lerayComplement 0`;
`datum⁰ z := orderZeroDatum hz`.  What is proved:

* `orderZeroDatum_pressureGradient_eq` — order-0 identity `datum⁰ ∇p = (I−P)₀ (datum⁰ h)` (SL8 row
  i.7), from the transverse fact for `∂ₜu` (rows i.2/i.4), the curl-free fixing of `∇p` (row i.6,
  lane 108's `lerayComplement_zero_orderZeroDatum_eq_self` + lane 111's curl symmetry), and linearity.
* `pressureGradient_slice_smoothSquareIntegrableJets_of_memForceR` — **P2, unconditional**: bootstraps
  the order-0 identity to every order via `lowerVectorL` / `Leray.isSobolevDatum_lower_iff` (rows
  ii/iii), then closes with `memHInfty_iff_smoothSquareIntegrableJets`.
* `isSobolevDatum_pressureGradient_lerayComplement` — the order-`m` step exposed as a datum identity
  `datumᵐ ∇p = (I−P)ₘ (datumᵐ h)`, with `exists_isSobolevDatum_pressureGradient_slice` its `∃`-form
  (the `hP` slot A04 consumes) and `pin_pressureGradient_datum` the uniqueness pin.  These three are
  lifted verbatim from the lane-117 reviewer's appendix B (`research/D01/REVIEW_SL8_ASSEMBLY.md`).
* `temporalDerivative_slice_smoothSquareIntegrableJets_of_memForceR` — corollary `∂ₜu(t,·) ∈ H^∞`.

No `sorry`, no `axiom`; axioms standard (`research/D01/axioms_sl8_assembly.lean`).  `hcurl` uses lane
111's in-tree `partialDeriv_pressureGradient_symm` (not lane 106's `A01.PressureGauge`), so this
upstream D01 module does not import A01.
-/

noncomputable section

namespace NSFormalization.Section4.D01

open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (ClassicalSolutionR MemForceR)
open NSFormalization.Paper3 (RealVectorSobolev)

variable {ν : ℝ} {a : Space → Space} {f : VelocityField} {T : ℝ}

/-- **SL8 row i.7 — the order-0 identity.**  `datum⁰ ∇p = (I−P)₀ (datum⁰ h)`, where `h` is the
momentum residual.  Apply `(I−P)₀` to `datum⁰ ∂ₜu = datum⁰ h − datum⁰ ∇p` (row i.2) and substitute
`(I−P)₀ (datum⁰ ∂ₜu) = 0` (row i.4, `∂ₜu` divergence-free) and
`(I−P)₀ (datum⁰ ∇p) = datum⁰ ∇p` (row i.6, `∇p` curl-free). -/
theorem orderZeroDatum_pressureGradient_eq (u : ClassicalSolutionR ν a f T)
    (hf : MemForceR f) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    orderZeroDatum (memLp_pressureGradient_slice u ht)
      = Leray.lerayComplement 0
          (orderZeroDatum (smoothL2_momentumResidual_slice u hf ht).memLp) := by
  -- Row i.2: `datum⁰ ∂ₜu = datum⁰ h − datum⁰ ∇p` (via `orderZeroDatum_sub` + uniqueness on `∂ₜu = h − ∇p`).
  have hi2 : orderZeroDatum (memLp_temporalDerivative_slice u hf ht)
      = orderZeroDatum (smoothL2_momentumResidual_slice u hf ht).memLp
        - orderZeroDatum (memLp_pressureGradient_slice u ht) := by
    rw [← orderZeroDatum_sub]
    refine isSobolevDatum_unique
      (isSobolevDatum_orderZeroDatum (memLp_temporalDerivative_slice u hf ht)) ?_
    have hcongr : (fun x : Space => f (t, x) - advection u.velocity t x
            + ν • spatialLaplacian u.velocity t x)
              - (fun x : Space => pressureGradient u.pressure t x)
          = fun x : Space => temporalDerivative u.velocity t x := by
      funext x; exact (temporalDerivative_slice_eq u ht x).symm
    exact hcongr ▸ isSobolevDatum_orderZeroDatum
      ((smoothL2_momentumResidual_slice u hf ht).memLp.sub (memLp_pressureGradient_slice u ht))
  -- Row i.4: `(I−P)₀ (datum⁰ ∂ₜu) = 0` (transverse fibre fact + `div ∂ₜu = 0`).
  have hi4 : Leray.lerayComplement 0
      (orderZeroDatum (memLp_temporalDerivative_slice u hf ht)) = 0 :=
    Leray.lerayComplement_eq_zero_of_transverse 0 _
      (orderZeroDatum_transverse_of_divergence_free
        (memLp_temporalDerivative_slice u hf ht)
        (contDiff_temporalDerivative_slice u hf ht)
        (fun x => sum_partialDeriv_temporalDerivative_eq_zero u ht x))
  -- Row i.6: `(I−P)₀ (datum⁰ ∇p) = datum⁰ ∇p` (lane 108, with `∇p` curl-free from lane 111).
  have hi6 : Leray.lerayComplement 0 (orderZeroDatum (memLp_pressureGradient_slice u ht))
      = orderZeroDatum (memLp_pressureGradient_slice u ht) :=
    Leray.lerayComplement_zero_orderZeroDatum_eq_self (memLp_pressureGradient_slice u ht)
      (contDiff_pressureGradient_slice u.pressure_smooth ⟨le_of_lt ht.1, ht.2⟩)
      (fun i j x => partialDeriv_pressureGradient_symm u ht i j x)
  have hcong := congrArg (Leray.lerayComplement 0) hi2
  rw [map_sub, hi4, hi6] at hcong
  exact (sub_eq_zero.mp hcong.symm).symm

/-- **eq:Rpressure at order `m`, as an identity of data.**  For any order-`m` datum `Am` of the
momentum residual `h`, the order-`m` datum of `∇p(t,·)` is `(I−P)ₘ Am`.  This is the order-`m`
bootstrap the main theorem uses; exported for A04's datum consumers (`hP` slot).  Lifted verbatim
from the lane-117 reviewer's appendix B (`research/D01/REVIEW_SL8_ASSEMBLY.md`). -/
theorem isSobolevDatum_pressureGradient_lerayComplement (u : ClassicalSolutionR ν a f T)
    (hf : MemForceR f) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) {m : ℕ} {Am : RealVectorSobolev (m : ℝ)}
    (hAm : IsSobolevDatum (m : ℝ) (fun x : Space => f (t, x) - advection u.velocity t x
      + ν • spatialLaplacian u.velocity t x) Am) :
    IsSobolevDatum (m : ℝ) (fun x : Space => pressureGradient u.pressure t x)
      (Leray.lerayComplement (m : ℝ) Am) := by
  have h0m : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  refine (Leray.isSobolevDatum_lower_iff h0m).mp ?_
  have hii1 : lowerVectorL (m : ℝ) 0 h0m Am
      = orderZeroDatum (smoothL2_momentumResidual_slice u hf ht).memLp :=
    isSobolevDatum_unique (Leray.isSobolevDatum_lower h0m hAm)
      (isSobolevDatum_orderZeroDatum _)
  have hii2 : lowerVectorL (m : ℝ) 0 h0m (Leray.lerayComplement (m : ℝ) Am)
      = Leray.lerayComplement 0
          (orderZeroDatum (smoothL2_momentumResidual_slice u hf ht).memLp) := by
    rw [← Leray.lerayComplement_lowerVectorL, hii1]
  rw [hii2, ← orderZeroDatum_pressureGradient_eq u hf ht]
  exact isSobolevDatum_orderZeroDatum _

/-- **The datum of `∇p(t,·)` is pinned.**  Any order-`m` datum `P` a consumer holds for `∇p(t,·)`
equals `(I−P)ₘ Am` by uniqueness of Sobolev data.  Reviewer appendix B. -/
theorem pin_pressureGradient_datum (u : ClassicalSolutionR ν a f T)
    (hf : MemForceR f) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) {m : ℕ}
    {Am P : RealVectorSobolev (m : ℝ)}
    (hAm : IsSobolevDatum (m : ℝ) (fun x : Space => f (t, x) - advection u.velocity t x
      + ν • spatialLaplacian u.velocity t x) Am)
    (hP : IsSobolevDatum (m : ℝ) (fun x : Space => pressureGradient u.pressure t x) P) :
    P = Leray.lerayComplement (m : ℝ) Am :=
  isSobolevDatum_unique hP (isSobolevDatum_pressureGradient_lerayComplement u hf ht hAm)

/-- **P2 (eq:Rpressure) — unconditional.**  `SmoothSquareIntegrableJets (∇p(t,·))`.  `h ∈ H^∞`
gives an order-`m` datum `Am` of `h` for every `m`; the witness `(I−P)ₘ Am` lowers to
`(I−P)₀ (datum⁰ h) = datum⁰ ∇p` (row i.7) at order 0, and `Leray.isSobolevDatum_lower_iff` promotes
that back to an order-`m` datum of `∇p`.  All orders + smoothness feed
`memHInfty_iff_smoothSquareIntegrableJets`. -/
theorem pressureGradient_slice_smoothSquareIntegrableJets_of_memForceR
    (u : ClassicalSolutionR ν a f T) (hf : MemForceR f) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    SmoothSquareIntegrableJets (fun x : Space => pressureGradient u.pressure t x) := by
  refine memHInfty_iff_smoothSquareIntegrableJets.mp
    ⟨contDiff_pressureGradient_slice u.pressure_smooth ⟨le_of_lt ht.1, ht.2⟩, fun m => ?_⟩
  obtain ⟨_, hjets⟩ :=
    memHInfty_iff_smoothSquareIntegrableJets.mpr (smoothL2_momentumResidual_slice u hf ht)
  obtain ⟨Am, hAm⟩ := hjets m
  exact ⟨Leray.lerayComplement (m : ℝ) Am,
    isSobolevDatum_pressureGradient_lerayComplement u hf ht hAm⟩

/-- **The order-`m` datum of `∇p(t,·)`, existence form.**  The `hP` slot of `A04.momentum_datum`:
`∇p(t,·)` has a Sobolev datum at every integer order.  Reviewer appendix B. -/
theorem exists_isSobolevDatum_pressureGradient_slice (u : ClassicalSolutionR ν a f T)
    (hf : MemForceR f) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) (m : ℕ) :
    ∃ P : RealVectorSobolev (m : ℝ),
      IsSobolevDatum (m : ℝ) (fun x : Space => pressureGradient u.pressure t x) P :=
  (memHInfty_iff_smoothSquareIntegrableJets.mpr
    (pressureGradient_slice_smoothSquareIntegrableJets_of_memForceR u hf ht)).2 m

/-- **Corollary — `∂ₜu(t,·) ∈ H^∞`.**  The `∂ₜu ↔ ∇p` equivalence
(`Pressure.pressureGradient_slice_smoothL2_iff_temporalDerivative`) run backwards from P2. -/
theorem temporalDerivative_slice_smoothSquareIntegrableJets_of_memForceR
    (u : ClassicalSolutionR ν a f T) (hf : MemForceR f) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    SmoothSquareIntegrableJets (fun x : Space => temporalDerivative u.velocity t x) :=
  (pressureGradient_slice_smoothL2_iff_temporalDerivative u hf ht).mpr
    (pressureGradient_slice_smoothSquareIntegrableJets_of_memForceR u hf ht)

end NSFormalization.Section4.D01
