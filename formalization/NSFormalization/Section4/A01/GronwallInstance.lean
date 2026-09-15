import NSFormalization.Section4.A01.ForceCap
import NSFormalization.Section4.A04.HighContinuationIntegral

/-!
# A01 unit A3 row **A3-M2** — the `gronwall_bddAbove_Ico` instantiation on a classical solution

`research/A01/A3_SPLIT.md` §3.5.  This module plugs A04's continuation machinery into
`Section4/A01/Propagation.lean`'s abstract Grönwall skeleton, on a `ClassicalSolutionR`, and
so turns the order-independent-horizon arithmetic into an explicit high-order bound depending
on **one** remaining hypothesis, the order-2 integral cap `Kbnd` (row **A3-L1·k**).

## The slot-by-slot instantiation (the review-§3.5 table)

`gronwall_bddAbove_Ico` (`Propagation.lean`) has, after lanes 137 (`ForceCap.lean`) and 138
(`A04.HighContinuationIntegral`), every hypothesis discharged **except** the order-2 integral
cap.  With `y := ‖u(·)‖_{H^m}`, `k := ‖u(·)‖²_{H²}`, `b := ‖f(·)‖_{H^m}`,
`Cgron := A04.Cgron m ν`:

| Grönwall slot | supplied by |
|---|---|
| `hCgron : 0 ≤ Cgron` | `A04.Cgron_pos m ν hν |>.le` (135) |
| `hy0 : 0 ≤ y 0` | `A01.sobolevNormAt_nonneg` (137) |
| `hy`, `hk` continuity | `A04.continuousOn_sobolevNormAt_velocity` (`Continuity.lean:105`), `.pow 2` for `k` |
| `hknn` | `sq_nonneg` |
| `hb`, `hbnn`, `hbbnd` | `A01.forceCap_L1` (137), with `Bbnd := ‖f‖_{L¹_tH^m}.toReal` |
| `hstep` | `A04.highContinuationIntegral` at `t₀ := 0` (138) |
| `hkbnd : ∫₀ᵗ ‖u‖²_{H²} ≤ Kbnd` | **the single remaining hole** (row A3-L1·k) — an explicit hypothesis here |

**No adapter is needed for `hstep`.**  `A04.highContinuationIntegral`'s conclusion at `t₀ := 0`
is, token for token,
`‖u(t)‖_{H^m} ≤ ‖u(0)‖_{H^m} + ∫₀ᵗ (Cgron m ν · ‖u(s)‖²_{H²} · ‖u(s)‖_{H^m} + ‖f(s)‖_{H^m})`,
which is exactly `gronwall_bddAbove_Ico`'s `hstep` with the above `y`, `k`, `b`, `Cgron`
(products left-associate identically, the integrand matches up to `β`).  So the `hstep` slot is
`(highContinuationIntegral … 0 t …).2`, no `intervalIntegral.integral_congr`/`ring_nf`.

## Interval bookkeeping

`highContinuationIntegral` needs `0 ≤ t₀ ≤ t < T`; we take `t₀ := 0` and require
`0 < T₀ ≤ T`, so every `t ∈ Ico 0 T₀` has `0 ≤ t` and `t < T₀ ≤ T`, covering `Ico 0 T₀`.

## What remains (row A3-L1·k)

The consumer's exact expected shape of the single hole is
`hkbnd : ∀ t ∈ Ico 0 T₀, (∫ s in 0..t, sobolevNormAt 2 w.velocity s ^ 2) ≤ Kbnd`,
i.e. a uniform cap on the running `L²_t H²` energy of the velocity on the horizon.  Once
`exists_local`'s quantitative clause `‖u‖ ≤ ‖u₀‖+1` (cylinder sup-norm) is transferred to the
order-2 datum norm (the still-open `D-euler-pairing` step), `Kbnd := c²·(‖u₀‖+1)²·T₀` is the
value it delivers; here it is an input, so this module is route-robust.
-/

noncomputable section

open Set MeasureTheory intervalIntegral
open NSFormalization.Section4.A04
open NSFormalization.Section4.A02 (SpaceTimeField SpatialField ClassicalSolutionR initialClassR)
open NSFormalization.Section4.D01 (MemForceR)

namespace NSFormalization.Section4.A01

/-- **A3-M2, one order.**  For a classical solution `w` with `L¹_t H^m` forcing and a smooth
Sobolev path, at every integer order `m ≥ 3`, on a horizon `0 < T₀ ≤ T`, given the single
order-2 integral cap `hkbnd`, the high-order norm is bounded on `[0,T₀)` by the explicit
constant `(‖u(0)‖_{H^m} + ‖f‖_{L¹_tH^m}) · exp(C_{m,ν}·Kbnd)`.

This is `gronwall_bddAbove_Ico` instantiated slot by slot (module docstring):
`hstep ← A04.highContinuationIntegral` at `t₀ := 0` (no adapter), forcing data ← `forceCap_L1`
(so `Bbnd := (forceSobolevENormL1 m f).toReal`), `hkbnd` the only remaining input. -/
theorem highOrder_bddAbove_of_kbnd
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (hν : 0 < ν) (ha : a ∈ initialClassR) (hf : MemForceR f) (hf1 : MemL1Hm f)
    (w : ClassicalSolutionR ν a f T) (hpath : HasSmoothSobolevPath T w.velocity)
    {m : ℕ} (hm : 3 ≤ m) {T₀ Kbnd : ℝ} (_hT₀ : 0 < T₀) (hT₀T : T₀ ≤ T)
    (hkbnd : ∀ t ∈ Ico (0 : ℝ) T₀,
        (∫ s in (0 : ℝ)..t, sobolevNormAt 2 w.velocity s ^ 2) ≤ Kbnd) :
    ∀ t ∈ Ico (0 : ℝ) T₀,
      sobolevNormAt (m : ℝ) w.velocity t ≤
        (sobolevNormAt (m : ℝ) w.velocity 0 + (forceSobolevENormL1 (m : ℝ) f).toReal)
          * Real.exp (A04.Cgron m ν * Kbnd) := by
  obtain ⟨hbc, hbnn, hbbnd⟩ := forceCap_L1 hf m T₀
  have hIcoSub : Ico (0 : ℝ) T₀ ⊆ Ico (0 : ℝ) T :=
    fun x hx => ⟨hx.1, lt_of_lt_of_le hx.2 hT₀T⟩
  -- `hstep` is `highContinuationIntegral` at `t₀ := 0`, verbatim — no adapter.
  have hstep : ∀ t ∈ Ico (0 : ℝ) T₀,
      sobolevNormAt (m : ℝ) w.velocity t ≤
        sobolevNormAt (m : ℝ) w.velocity 0 +
          ∫ s in (0 : ℝ)..t,
            (A04.Cgron m ν * sobolevNormAt 2 w.velocity s ^ 2 *
                sobolevNormAt (m : ℝ) w.velocity s + sobolevNormAt (m : ℝ) f s) :=
    fun t ht =>
      (highContinuationIntegral ν a f T hν ha hf hf1 w hpath m hm 0 t le_rfl ht.1
        (lt_of_lt_of_le ht.2 hT₀T)).2
  exact gronwall_bddAbove_Ico
    (Cgron := A04.Cgron m ν) (Kbnd := Kbnd)
    (Bbnd := (forceSobolevENormL1 (m : ℝ) f).toReal)
    (y := fun t => sobolevNormAt (m : ℝ) w.velocity t)
    (k := fun s => sobolevNormAt 2 w.velocity s ^ 2)
    (b := fun s => sobolevNormAt (m : ℝ) f s)
    (A04.Cgron_pos m ν hν).le
    (sobolevNormAt_nonneg (m : ℝ) w.velocity 0)
    ((continuousOn_sobolevNormAt_velocity w m).mono hIcoSub)
    (((continuousOn_sobolevNormAt_velocity w 2).mono hIcoSub).pow 2)
    hbc
    (fun _ _ => sq_nonneg _)
    hbnn
    hkbnd
    hbbnd
    hstep

/-- **A3-M2, all orders on one horizon.**  Packaging via
`higherOrder_bddAbove_fixedDriverSq` (`Propagation.lean`): the manuscript's fixed order-2
driver `k = ‖u‖²_{H²}` (eq:criterion), one cap `Kbnd` and one horizon `T₀` for **every** order
`m ≥ 3`.  This is "the same local interval for every order"
(`appendix-a-local-theory.tex:66-67`) on a classical solution, modulo the single order-2 cap
hole. -/
theorem highOrder_bddAbove_all_orders_of_kbnd
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (hν : 0 < ν) (ha : a ∈ initialClassR) (hf : MemForceR f) (hf1 : MemL1Hm f)
    (w : ClassicalSolutionR ν a f T) (hpath : HasSmoothSobolevPath T w.velocity)
    {T₀ Kbnd : ℝ} (_hT₀ : 0 < T₀) (hT₀T : T₀ ≤ T)
    (hkbnd : ∀ t ∈ Ico (0 : ℝ) T₀,
        (∫ s in (0 : ℝ)..t, sobolevNormAt 2 w.velocity s ^ 2) ≤ Kbnd) :
    ∀ m : ℕ, 3 ≤ m →
      BddAbove ((fun t => sobolevNormAt (m : ℝ) w.velocity t) '' Ico (0 : ℝ) T₀) := by
  have hIcoSub : Ico (0 : ℝ) T₀ ⊆ Ico (0 : ℝ) T :=
    fun x hx => ⟨hx.1, lt_of_lt_of_le hx.2 hT₀T⟩
  refine higherOrder_bddAbove_fixedDriverSq
    (m₀ := 3) (m_drive := 2)
    (C := fun m => A04.Cgron m ν)
    (B := fun m => (forceSobolevENormL1 (m : ℝ) f).toReal)
    (y := fun m t => sobolevNormAt (m : ℝ) w.velocity t)
    (b := fun m s => sobolevNormAt (m : ℝ) f s)
    ((continuousOn_sobolevNormAt_velocity w 2).mono hIcoSub) hkbnd ?_
  intro m hm
  obtain ⟨hbc, hbnn, hbbnd⟩ := forceCap_L1 hf m T₀
  refine ⟨(A04.Cgron_pos m ν hν).le, sobolevNormAt_nonneg (m : ℝ) w.velocity 0,
    (continuousOn_sobolevNormAt_velocity w m).mono hIcoSub, hbc, hbnn, hbbnd, ?_⟩
  intro t ht
  exact (highContinuationIntegral ν a f T hν ha hf hf1 w hpath m hm 0 t le_rfl ht.1
    (lt_of_lt_of_le ht.2 hT₀T)).2

end NSFormalization.Section4.A01
