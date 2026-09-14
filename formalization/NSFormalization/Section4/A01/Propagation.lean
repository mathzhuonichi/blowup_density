import NSFormalization.Section4.A04.Gronwall

/-!
# A01 unit A3 — the abstract order-independent horizon skeleton

This module supplies the **route-independent arithmetic core of A01 unit A3**
(`research/A01/A01_SPLIT.md` row A3, `paper/sections/appendix-a-local-theory.tex:66-67`
["the higher-order bounds in part (ii) hold on the same local interval for every
order"] with the Grönwall consequence at `:146-147`; `:148-152` is the restart
passage, which is A2b, not A3):
once the manuscript's higher-order energy estimate has been reduced, order by
order, to a Grönwall step inequality of the form

```
y_m t ≤ y_m 0 + ∫₀ᵗ (C_m · k s · y_m s + b_m s)      (0 ≤ t < T₀)
```

on **one** interval `[0, T₀)` — with the coupling coefficient `k` the *same*
function for every order (in the application `k = ‖u(·)‖²_{H²}`, controlled by the
lowest order because `‖u‖_{H²} ≤ ‖u‖_{H^{m₀}}`), and `C_m ≥ 0` a viscosity/tame
constant that **does not depend on `T₀`** — then every `y_m` is bounded on the
whole half-open interval `[0, T₀)` by an explicit constant, and hence the family
`{y_m}` is uniformly (in `t`) bounded on the *single shared* `T₀`.

## What is pure arithmetic here and what is not

This is entirely real analysis: `y, k, b : ℝ → ℝ`, no PDE object.  It is the last
assembly step of the propagation spine, sitting on top of the A04 machinery that
produces the Grönwall step from the energy identity:

* `A04.inner_energy_Rhigh` (`Section4/A04/HighEnergy.lean:136`) delivers eq:Rhigh
  `½ E' + ν‖∇u‖²_{H^m} ≤ C·‖u‖_{H²}·‖u‖_{H^m}·‖∇u‖_{H^m} + ‖f‖_{H^m}·‖u‖_{H^m}`
  with `E = ‖u‖²_{H^m}`;
* Young's inequality absorbs `‖∇u‖_{H^m}` into the dissipation, leaving
  `E' ≤ 2(K·E + b·√E)` with `K = (C²/4ν)‖u‖²_{H²}` and `b = ‖f‖_{H^m}`;
* `A04.sqrt_le_primitive_linear` (`Section4/A04/Regularized.lean:134`, the ζ↓0
  regularized square-root device) turns that into the integral step
  `√E t ≤ √E 0 + ∫₀ᵗ (K·√E + b)`, i.e. exactly the `hstep` hypothesis below with
  `y = √E = ‖u‖_{H^m}`, `c = K = C_gron·k`, `k = ‖u‖²_{H²}`;
* the coefficient integrand is `IntervalIntegrable` and its integrals are finite
  on `[0, T₀)` by `A04.intervalIntegrable_highContinuationIntegrand`
  (`Section4/A04/Continuity.lean:132`) plus low-order membership in the mild
  solution space `X` — which is what supplies the uniform integral bounds
  `Kbnd`, `Bbnd` below.

`gronwall_bddAbove_Ico` reuses `A04.gronwall_integral_mul` verbatim on each compact
`[0, t] ⊆ [0, T₀)`, then cashes the per-`t` Grönwall bound into a single `t`-free
constant using the uniform integral caps.  `higherOrder_bddAbove` packages the
*same `T₀` for every order*: because `T₀` is one shared variable, one hypothesis
per order gives `∀ m ≥ m₀, BddAbove (y_m '' [0,T₀))`.

None of `Kbnd`, `Bbnd`, `C_m` depends on `t`, and `C_m` does not depend on `T₀`
(it is the tame/viscosity constant), so the bound `(y_m 0 + Bbnd)·exp (C_m·Kbnd)`
is a genuine order-`m` constant on the half-open interval.
-/

open Set intervalIntegral MeasureTheory
open NSFormalization.Section4.A04

namespace NSFormalization.Section4.A01

/-- **A3 skeleton, one order.**  Given the Grönwall step inequality
`y t ≤ y 0 + ∫₀ᵗ (C_gron·k·y + b)` on `[0, T₀)`, with `C_gron ≥ 0`, `y 0 ≥ 0`,
`k, b ≥ 0`, `k, b` continuous, and *uniform* integral caps
`∫₀ᵗ k ≤ Kbnd`, `∫₀ᵗ b ≤ Bbnd` valid for every `t ∈ [0, T₀)`, the solution is
bounded on the whole half-open interval by the explicit constant
`(y 0 + Bbnd)·exp (C_gron·Kbnd)`.

Proof: on each `[0, t] ⊆ [0, T₀)` apply `A04.gronwall_integral_mul` to get
`y t ≤ (y 0 + ∫₀ᵗ b)·exp (C_gron·∫₀ᵗ k)`, then replace the two integrals by their
caps.  The base `y 0 + ∫₀ᵗ b ≥ 0` (from `y 0 ≥ 0` and `b ≥ 0`) is what lets the
monotone replacement go through both factors. -/
theorem gronwall_bddAbove_Ico {T₀ Cgron Kbnd Bbnd : ℝ} {y k b : ℝ → ℝ}
    (hCgron : 0 ≤ Cgron) (hy0 : 0 ≤ y 0)
    (hy : ContinuousOn y (Ico 0 T₀))
    (hk : ContinuousOn k (Ico 0 T₀)) (hb : ContinuousOn b (Ico 0 T₀))
    (hknn : ∀ t ∈ Ico 0 T₀, 0 ≤ k t) (hbnn : ∀ t ∈ Ico 0 T₀, 0 ≤ b t)
    (hkbnd : ∀ t ∈ Ico 0 T₀, (∫ s in (0 : ℝ)..t, k s) ≤ Kbnd)
    (hbbnd : ∀ t ∈ Ico 0 T₀, (∫ s in (0 : ℝ)..t, b s) ≤ Bbnd)
    (hstep : ∀ t ∈ Ico 0 T₀, y t ≤ y 0 + ∫ s in (0 : ℝ)..t, (Cgron * k s * y s + b s)) :
    ∀ t ∈ Ico 0 T₀, y t ≤ (y 0 + Bbnd) * Real.exp (Cgron * Kbnd) := by
  intro t ht
  have ht0 : (0 : ℝ) ≤ t := ht.1
  have htT : t < T₀ := ht.2
  have hsub : Icc (0 : ℝ) t ⊆ Ico (0 : ℝ) T₀ := fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 htT⟩
  -- The A04 variable-coefficient Grönwall inequality on the compact subinterval `[0, t]`.
  have hG := gronwall_integral_mul (t₀ := (0 : ℝ)) (t₁ := t) (Cgron := Cgron)
    ht0 hCgron (hy.mono hsub) (hk.mono hsub) (hb.mono hsub)
    (fun s hs => hknn s (hsub hs)) (fun s hs => hbnn s (hsub hs))
    (fun s hs => hstep s (hsub hs)) t ⟨ht0, le_rfl⟩
  -- Replace the two integrals by their uniform caps.
  have hIb : (∫ s in (0 : ℝ)..t, b s) ≤ Bbnd := hbbnd t ht
  have hIk : (∫ s in (0 : ℝ)..t, k s) ≤ Kbnd := hkbnd t ht
  have hIbnn : 0 ≤ ∫ s in (0 : ℝ)..t, b s :=
    intervalIntegral.integral_nonneg ht0 (fun s hs => hbnn s (hsub hs))
  have hbase_nn : 0 ≤ y 0 + ∫ s in (0 : ℝ)..t, b s := by linarith
  have hBbnd_nn : 0 ≤ y 0 + Bbnd := by linarith
  have hexp : Real.exp (Cgron * ∫ s in (0 : ℝ)..t, k s) ≤ Real.exp (Cgron * Kbnd) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hIk hCgron)
  calc y t
      ≤ (y 0 + ∫ s in (0 : ℝ)..t, b s) * Real.exp (Cgron * ∫ s in (0 : ℝ)..t, k s) := hG
    _ ≤ (y 0 + Bbnd) * Real.exp (Cgron * ∫ s in (0 : ℝ)..t, k s) :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
    _ ≤ (y 0 + Bbnd) * Real.exp (Cgron * Kbnd) :=
        mul_le_mul_of_nonneg_left hexp hBbnd_nn

/-- **A3 packaging: one horizon `T₀` for every order.**  A single coupling
function `k` (with a single integral cap `Kbnd`) drives an order-indexed family
`y_m`, `b_m` with order constants `C_m`, `B_m`.  If each order `m ≥ m₀` satisfies
the `gronwall_bddAbove_Ico` hypotheses on the *same* `[0, T₀)`, then every `y_m`
is bounded above on `[0, T₀)`.

The point is that `T₀` is a single shared variable: this is precisely the
manuscript's "the higher-order bounds hold on the same local interval for every
order" (`appendix-a-local-theory.tex:66-67`). -/
theorem higherOrder_bddAbove {T₀ Kbnd : ℝ} {m₀ : ℕ} {C B : ℕ → ℝ}
    {y b : ℕ → ℝ → ℝ} {k : ℝ → ℝ}
    (hk : ContinuousOn k (Ico 0 T₀))
    (hknn : ∀ t ∈ Ico 0 T₀, 0 ≤ k t)
    (hkbnd : ∀ t ∈ Ico 0 T₀, (∫ s in (0 : ℝ)..t, k s) ≤ Kbnd)
    (H : ∀ m, m₀ ≤ m →
        0 ≤ C m ∧ 0 ≤ y m 0 ∧
        ContinuousOn (y m) (Ico 0 T₀) ∧ ContinuousOn (b m) (Ico 0 T₀) ∧
        (∀ t ∈ Ico 0 T₀, 0 ≤ b m t) ∧
        (∀ t ∈ Ico 0 T₀, (∫ s in (0 : ℝ)..t, b m s) ≤ B m) ∧
        (∀ t ∈ Ico 0 T₀, y m t ≤ y m 0 + ∫ s in (0 : ℝ)..t, (C m * k s * y m s + b m s))) :
    ∀ m, m₀ ≤ m → BddAbove ((fun t => y m t) '' Ico 0 T₀) := by
  intro m hm
  obtain ⟨hCm, hy0m, hym, hbm, hbnnm, hbbndm, hstepm⟩ := H m hm
  refine ⟨(y m 0 + B m) * Real.exp (C m * Kbnd), ?_⟩
  rintro x ⟨t, ht, rfl⟩
  exact gronwall_bddAbove_Ico hCm hy0m hym hk hbm hknn hbnnm hkbnd hbbndm hstepm t ht

/-- **A3 packaging, driver tied to the family's lowest index.**  The special case
of `higherOrder_bddAbove` in which the coupling coefficient is the square of the
*lowest propagated order*, `k = fun s => (y m₀ s)²`.

**Caveat (lane 122 review, F6):** this is NOT the manuscript's driver.  The
manuscript couples through the **fixed order 2** (eq:criterion,
`02-preliminaries.tex:111`: `∫₀^S ‖u‖²_{H²} < ∞`), which on the OpenAI spine
(`m₀ = q+1 = 7`) is *below* the family's lowest index; instantiated here the cap
`hkbnd : ∫₀ᵗ (y m₀)² ≤ Kbnd` would assume the high-order control one is proving
(circular, and contradicts row A3-L1).  For the manuscript coupling use
`higherOrder_bddAbove_fixedDriverSq` with `m_drive := 2`.  This lemma is kept only
as a true (harmless) specialization; do not read it as the `‖u‖²_{H²}` driver. -/
theorem higherOrder_bddAbove_lowestOrderSq {T₀ Kbnd : ℝ} {m₀ : ℕ} {C B : ℕ → ℝ}
    {y b : ℕ → ℝ → ℝ}
    (hy0cont : ContinuousOn (y m₀) (Ico 0 T₀))
    (hkbnd : ∀ t ∈ Ico 0 T₀, (∫ s in (0 : ℝ)..t, (y m₀ s) ^ 2) ≤ Kbnd)
    (H : ∀ m, m₀ ≤ m →
        0 ≤ C m ∧ 0 ≤ y m 0 ∧
        ContinuousOn (y m) (Ico 0 T₀) ∧ ContinuousOn (b m) (Ico 0 T₀) ∧
        (∀ t ∈ Ico 0 T₀, 0 ≤ b m t) ∧
        (∀ t ∈ Ico 0 T₀, (∫ s in (0 : ℝ)..t, b m s) ≤ B m) ∧
        (∀ t ∈ Ico 0 T₀,
          y m t ≤ y m 0 + ∫ s in (0 : ℝ)..t, (C m * (y m₀ s) ^ 2 * y m s + b m s))) :
    ∀ m, m₀ ≤ m → BddAbove ((fun t => y m t) '' Ico 0 T₀) :=
  higherOrder_bddAbove (k := fun s => (y m₀ s) ^ 2)
    (hy0cont.pow 2) (fun _ _ => sq_nonneg _) hkbnd H

/-- **A3 packaging, manuscript driver: fixed low order `m_drive`.**  The
manuscript-faithful coupling of `higherOrder_bddAbove`: the driver is a *fixed*
order `m_drive`, chosen **independently of** the family's lowest index `m₀` — for
the paper, `m_drive = 2`, so `k = fun s => (y 2 s)²` is the eq:criterion driver
`‖u‖²_{H²}` (`02-preliminaries.tex:111`, eq:Rhigh "for every `m ≥ 3`"
`appendix-a-local-theory.tex:129`).  The driver function `y m_drive` is supplied
from outside the propagated family, so its continuity is a separate hypothesis
and its integral cap `Kbnd` is the `L²_tH^{m_drive}` control the low-order mild
solution already has.  Nonnegativity of `k` is automatic (`sq_nonneg`). -/
theorem higherOrder_bddAbove_fixedDriverSq {T₀ Kbnd : ℝ} {m₀ m_drive : ℕ} {C B : ℕ → ℝ}
    {y b : ℕ → ℝ → ℝ}
    (hdrive : ContinuousOn (y m_drive) (Ico 0 T₀))
    (hkbnd : ∀ t ∈ Ico 0 T₀, (∫ s in (0 : ℝ)..t, (y m_drive s) ^ 2) ≤ Kbnd)
    (H : ∀ m, m₀ ≤ m →
        0 ≤ C m ∧ 0 ≤ y m 0 ∧
        ContinuousOn (y m) (Ico 0 T₀) ∧ ContinuousOn (b m) (Ico 0 T₀) ∧
        (∀ t ∈ Ico 0 T₀, 0 ≤ b m t) ∧
        (∀ t ∈ Ico 0 T₀, (∫ s in (0 : ℝ)..t, b m s) ≤ B m) ∧
        (∀ t ∈ Ico 0 T₀,
          y m t ≤ y m 0 + ∫ s in (0 : ℝ)..t, (C m * (y m_drive s) ^ 2 * y m s + b m s))) :
    ∀ m, m₀ ≤ m → BddAbove ((fun t => y m t) '' Ico 0 T₀) :=
  higherOrder_bddAbove (k := fun s => (y m_drive s) ^ 2)
    (hdrive.pow 2) (fun _ _ => sq_nonneg _) hkbnd H

end NSFormalization.Section4.A01
