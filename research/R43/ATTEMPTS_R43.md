# R43 (Prop 4.3) — attempts, positive and negative (lane 159)

Scope: split the proof route of `04-whole-space.tex:90-133` and close the cheapest
rows in Lean. Primary deliverable `research/R43/R43_SPLIT.md`; Lean in
`formalization/NSFormalization/Section4/R43/Pieces.lean`.

## Positive: what closed, and how

* **S2 scalar bootstrap is already in the tree — reuse, not reprove.** The lead's
  brief listed "the S2 scalar ODE-inequality lemma (continuity/first-crossing)" as a
  candidate to prove. It already exists, domain-agnostic, in
  `NSFormalization.Paper1.ScalarEnergy` (`Paper1/ScalarEnergy.lean`):
  `sqrt_energy_le_primitive` (regularized `√` division), `continuous_bootstrap` (first
  level-crossing), and `critical_norm_bound` — whose `henergy` hypothesis
  `E't/2 + (ν − C·y t)·(z t)^2 ≤ b t · y t` **is eq:Rcritical1 verbatim**. Lane 154's
  `NSFormalization.Section4.C01.sqrt_energy_le_primitive'`
  (`Section4/C01/EnergyBounds.lean:179`) generalizes it to arbitrary `E(0)/N(0)` (the
  general-`a` primitive bound). Reproving would have violated the reuse rule. Delivered
  `criticalNormBound_radius` as a thin wrapper adding only the `ν/(2C₀)` gate arithmetic.

* **G6 (power spelling)** `x ^ (2:ℕ) = x ^ (2:ℝ)` in `ℝ≥0∞`:
  `rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast]`. One line.

* **G8 (constant arithmetic)** closed in three lemmas. Radius: `c = min (1/(8C₀)) (1/(4 C₁ Cemb))`
  gives `c < 1/(4C₀)` (strict, via `1/(8C₀) < 1/(4C₀)`) and `C₁·Cemb·c ≤ 1/4`. Gate
  discharge (real + ℝ≥0∞) by `nlinarith` on the scaled inequalities; the `ν`-free
  `C₁·Cemb·c ≤ 1/4` scaled by `ν` meets `ν/4`. The ℝ≥0∞ version matches C01's exact gate
  `ENNReal.ofReal C₁ * criticalL3 ≤ ENNReal.ofReal (ν/4)` via `ENNReal.ofReal_mul` + `gcongr`-style `mul_le_mul'`.

## Negative: dead ends and pitfalls

* **`import Mathlib.Analysis.SpecialFunctions.Pow.NNRpow` does not exist at this pin.**
  A `lake env lean` probe that did `import Mathlib` (wholesale) hid this. `ENNReal.rpow_natCast`
  lives in `Mathlib.Analysis.SpecialFunctions.Pow.NNReal` (`:686`). Lesson: probe with the
  *targeted* import you intend to ship, not `import Mathlib`.

* **`mul_le_mul_left'` is not the ℝ≥0∞ name here.** For `ENNReal.ofReal C₁ * L3 ≤ ENNReal.ofReal C₁ * X`
  from `L3 ≤ X`, `mul_le_mul_left'` was `unknownIdentifier`; `mul_le_mul' le_rfl hL3le` works.

* **`div_le_iff₀ … at ⊢` mis-fires when the goal RHS is a bare `1/4`.** Rewrote the third
  radius bound as a `calc` through `C₁*Cemb*(1/(4 C₁ Cemb)) = 1/4` (`field_simp` with
  `C₁*Cemb ≠ 0`) instead. `mul_div_assoc`/`sub_eq_zero` gymnastics on `C₀*(ν/(2C₀)) ≤ ν/2`
  also failed; `le_of_eq (by field_simp)` closes it directly (do **not** append `ring` —
  `field_simp` already discharges it, and a trailing `ring` errors "No goals").

* **`le_rfl` fails a non-vacuity witness when Lean keeps `1*(1/8)` unreduced.** In the G8c
  witness `hL3le : ENNReal.ofReal (1/8) ≤ ENNReal.ofReal (1*(1/8))` needs
  `ENNReal.ofReal_le_ofReal (by norm_num)`, not `le_rfl`.

## Not attempted in Lean, with reason (all in `R43_SPLIT.md`)

* **G7 / S1 (eq:Rcritical1)** — R43-owned, size L, needs a differentiable `Ḣ^{1/2}`/`Ḣ^{3/2}`
  critical path no lane exports. The genuine analytic substance R43 owes itself.
* **S3 embedding, S4 assembly, S5 lifespan** — the sibling clauses (`velocityCriticalL3`,
  `h2TimeIntegral`, `lifespanInfiniteOfLocallyFinite`) are **draft-only, unregistered**
  (A05 V2 / C01 V4 / A04 V3 prerequisites). Cannot be consumed until registered.
* **G2 (S6 reduction)** — path-level force-norm monotonicity, new, unowned.
* **G3 (non-vacuity)** — order-`1/2` force datum *paths* for general `f` are not in D01
  (only integer orders via `MemForceR`, or compact support via `compact_exists_homogeneousPath`).
  Not closable for general `f` on current definitions.
