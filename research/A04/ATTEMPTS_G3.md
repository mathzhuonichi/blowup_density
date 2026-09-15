# A04 unit G3 — variable-coefficient Grönwall (attempts log)

Module: `formalization/NSFormalization/Section4/A04/Gronwall.lean`
Axiom audit: `research/A04/axioms_g3.lean`.

## What was proved

Three theorems, pure real analysis, `sorry`-free, axioms
`[propext, Classical.choice, Quot.sound]` for all three. Imports narrowed to
`Mathlib.Analysis.Calculus.Deriv.MeanValue`, `Mathlib.Analysis.SpecialFunctions.ExpDeriv`,
`Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus` (see Review fixes).

- `gronwall_integral` (integral form): `t₀ ≤ t₁`; `y, c, b` `ContinuousOn (Icc t₀ t₁)`;
  `c, b ≥ 0` on `Icc`; `∀ t ∈ Icc, y t ≤ y t₀ + ∫_{t₀}^t (c·y + b)` ⇒
  `∀ t ∈ Icc, y t ≤ (y t₀ + ∫_{t₀}^t b)·exp(∫_{t₀}^t c)`.
- `gronwall_deriv` (differential form): same conclusion from a right derivative
  `HasDerivWithinAt y (y' x) (Ici x) x` on `Ioo`, `IntervalIntegrable y'`, and
  `y' x ≤ c x·y x + b x` on `Ioo`. Reduced to the integral form via FTC-2.
- `gronwall_integral_mul` (A04 corollary): coefficient `Cgron·k`, `Cgron ≥ 0`,
  `k ≥ 0` continuous ⇒ `y t ≤ (y t₀ + ∫ b)·exp(Cgron·∫ k)`.

## Hypotheses actually needed vs. the paper

- **Continuity of `c` and `b`**, not merely `L¹`/local integrability as
  `appendix-a:142-147` phrases it. Reason below (integrability route). This is the
  one place the Lean statement is stronger than the manuscript sentence; it is
  harmless for A04 because on the open existence interval `u` and `f` are `C^∞` in
  time, so `‖u(·)‖²_{H²}` (the coefficient) and `‖f(·)‖_{H^m}` (the inhomogeneity)
  are continuous on every compact subinterval; the "only `L¹` in time" character of
  the coefficient enters at the assembly stage (sup over `t₁ ↑ S`), not inside G3.
- **`y ≥ 0` is NOT needed** — the integrating-factor argument never uses it.
- **`b ≥ 0` IS needed**: used only to bound `∫ (exp(-∫c)·b) ≤ ∫ b`. Without it the
  weight `exp(-∫c) ≤ 1` no longer gives `(y t₀ + ∫b)·exp(∫c)` as the clean bound.
  (`b = ‖f‖_{H^m} ≥ 0` in the paper.)
- **`c ≥ 0` IS needed**: for `exp(-∫c) ≤ 1` and for the derivative sign
  `c·(y − Y) ≤ 0`. (`c = C_{m,ν}‖u‖²_{H²} ≥ 0` in the paper.)

## Route that closed (integrating factor + antitone)

Set `F u = (y t₀ + ∫_{t₀}^u (c·y+b))·exp(−∫_{t₀}^u c) − ∫_{t₀}^u (exp(−∫_{t₀}^s c)·b)`.
Its derivative at interior `x` factors as `exp(−∫c)·c x·(y x − Y x) ≤ 0` where
`Y = y t₀ + ∫(c·y+b) ≥ y` by hypothesis. Hence `AntitoneOn F`, so `F t ≤ F t₀ = y t₀`.
Rearranging (multiply by `exp(∫c)`, bound `∫ exp(−∫c)·b ≤ ∫ b`) gives the claim.

Mathlib lemmas used:
- `intervalIntegral.integral_hasDerivAt_right` + `ContinuousOn.stronglyMeasurableAtFilter`
  (`isOpen_Ioo`) + `ContinuousOn.intervalIntegrable_of_Icc` for FTC-1 at interior points
  (the exact idiom already appears in `Paper1/ScalarEnergy.lean`'s
  `packet_energy_integral_bound`).
- `intervalIntegral.continuousOn_primitive_interval'` (needs `(μ := volume)` given
  explicitly, else the `IsLocallyFiniteMeasure` instance is stuck on a metavariable).
- `HasDerivAt.const_add`, `HasDerivAt.neg`, `HasDerivAt.exp`, `HasDerivAt.mul`,
  `HasDerivAt.sub`; `antitoneOn_of_hasDerivWithinAt_nonpos` (same lemma
  `ScalarEnergy.lean` uses).
- `intervalIntegral.integral_mono_on`, `intervalIntegral.integral_nonneg`,
  `Real.exp_le_one_iff`, `Real.exp_add`, `Real.exp_pos`, `intervalIntegral.integral_const_mul`.
- differential form: `intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le`
  (FTC-2, right derivatives), `IntervalIntegrable.mono_set` with
  `uIcc_subset_uIcc_left`, `integral_mono_on_of_le_Ioo`.

Bookkeeping notes that cost time:
- The derivative-sign subgoal is already β-reduced after the metavariable for `f'`
  is fixed by `((hY.mul hE).sub hK).hasDerivWithinAt`; an extra `simp only []` there
  errors with "made no progress". `nlinarith [mul_nonneg (mul_nonneg hepos.le hcx)
  (sub_nonneg.mpr hyY), …]` closes it directly.
- `ContinuousOn.intervalIntegrable` wants `uIcc`; on `Icc` use
  `.intervalIntegrable_of_Icc h`.

## Routes considered and rejected (negative examples)

1. **Mathlib's constant-`K` Grönwall** (`le_gronwallBound_of_liminf_deriv_right_le`,
   `norm_le_gronwallBound_of_norm_deriv_right_le`, and the in-tree wrapper
   `EulerOrdinarySobolev.linear_stability_within`,
   `vendor/NavierStokesAndEuler/Euler/OrdinaryEulerL2Stability.lean:46`). These give
   `exp(K·(t−t₀))` with a single constant `K`; Mathlib's own TODO says the
   variable-coefficient version is absent. A change of variables `τ = ∫c` to reduce to
   constant `K` needs `c > 0` and `C¹` to make `t ↦ ∫c` a diffeomorphism — false for
   merely-integrable `c`, and even for continuous `c` it adds a reparametrisation with no
   payoff over the direct integrating-factor proof. **Not used.**

   **Correction (review G3, finding 1).** A genuine *variable-coefficient* Grönwall
   *does* already exist in tree, by the same integrating-factor route:
   `EulerOrdinarySobolev.variable_linear_stability`
   (`vendor/NavierStokesAndEuler/Euler/OrdinaryVariableGronwall.lean:14`), `sorry`-free,
   `X t ≤ X 0 · exp(C · ∫₀ᵗ K)` from `X' t ≤ C·K(t)·X t`. It is **not** a substitute for
   G3 and G3 is **not** derivable from it, for three reasons:
   (a) it is **homogeneous** (`b = 0`) — it has no `+ ‖f‖_{H^m}` term and cannot express
   `higherOrderBound`'s inhomogeneity; this missing `b` is the real obstruction (it is
   also why it needs no sign condition on `K`, a nice cross-check that G3's `c ≥ 0` and
   `b ≥ 0` are forced by the inhomogeneity);
   (b) it is only in **differential form**, whereas A04 consumes the **integral form**
   `y ≤ y t₀ + ∫(c·y + b)`;
   (c) it is anchored at **`t₀ = 0`** and bundles the coefficient as a `C(Icc 0 T, ℝ)`
   with the vendor's `extendPath`/`realIntegral` plumbing, whereas G3 takes a general base
   point `t₀` and a plain `ℝ → ℝ` with `ContinuousOn`.
   So `gronwall_deriv` cannot be cheaply derived from, nor cheaply share a lemma with,
   `variable_linear_stability` — the type-level mismatch (`b`, `t₀`, the `C(·,ℝ)`
   packaging) is larger than the shared 8-line integrating-factor core. The identical
   route being carried twice is a positive signal but not reusable code; the phrasing
   "genuinely new to this repository" (earlier draft, and `COMPARISON.md:215`) is dropped.

2. **Merely `IntervalIntegrable` `c` and/or `b`** (the paper's literal `L¹`
   hypothesis). Rejected after analysis, not a coding failure:
   - If `b` (or `c`) is only integrable, the indefinite integral `Y` and the
     integrating-factor combination `F` are only differentiable *almost everywhere*,
     not on the whole interior. `antitoneOn_of_hasDerivWithinAt_nonpos`,
     `antitoneOn_of_deriv_nonpos` and FTC-2 (`integral_eq_sub_of_hasDeriv_right_of_le`)
     all require the derivative to exist at *every* interior point, and the
     "countable exceptional set" mean-value lemmas do not help because the Lebesgue
     null set where an indefinite integral fails to be differentiable can be
     uncountable. The route we *would* take for a rigorous integrable-coefficient proof
     is therefore the absolutely-continuous / a.e.-FTC toolkit — but it is not strictly
     *needed*: the classical **FTC-free Picard iteration** (iterate `y ≤ A + ∫ c·y`,
     bound the `n`-fold iterated kernel on the simplex by `(∫c)ⁿ/n!` via Fubini/symmetry,
     sum the exponential series) uses no differentiation at all and needs only `c ≥ 0`,
     measurability and boundedness of `y`. Either way it is a much larger campaign, and it
     is not what A04 actually consumes (see the hypotheses discussion above), so the
     *decision* to state G3 with continuous coefficients is right; only the earlier word
     "needs" is softened here (review G3, finding 2).
   - A partial relaxation `c` continuous, `b` only integrable *is* provable (split
     `Y = P + R`, `P = ∫ c·y` is `C¹`, handle the `R = ∫ b` term by monotonicity of
     `R` and `∫ c·exp(−∫c) = 1 − exp(−∫c)`), but it still requires `c` continuous and
     roughly doubles the proof for a hypothesis A04 does not need. **Not pursued;
     recorded here as the natural next strengthening if a consumer ever needs
     `b ∈ L¹` with continuous coefficient.**

3. **A separate clean-valued `hderiv` via `convert … using 1; ring`.** The raw
   derivative from `(hY.mul hE).sub hK` carries `HasDerivAt.mul`'s `d x` / `c x`
   β-redexes; matching it to a hand-factored value through `convert` was fragile
   about how deep `HasDerivAt`/`HasDerivAtFilter` unfolds. Replaced by letting the
   metavariable take the raw value and discharging the sign with `nlinarith` (which
   normalises with `ring`), which is robust. **Superseded, not a failure.**

## Review fixes (lane 041, ACCEPT-WITH-NOTES)

Applied the four notes from `research/A04/REVIEW_G3.md`; no Lean statement or proof
was rewritten (the three theorems are unchanged).

1. **Prior art (finding 1).** Corrected route 1 above and `COMPARISON.md` row G3 to
   name `EulerOrdinarySobolev.variable_linear_stability`
   (`vendor/NavierStokesAndEuler/Euler/OrdinaryVariableGronwall.lean:14`) as an existing
   variable-coefficient Grönwall by the same integrating-factor route, with the three
   reasons it does not cover A04 (homogeneous `b = 0`; differential form only; `t₀ = 0`
   with a bundled `C(Icc 0 T, ℝ)` coefficient). `gronwall_deriv` is **not** cheaply
   derivable from / shareable with it — the missing inhomogeneity `b`, the `t₀` shift,
   and the `C(·,ℝ)`/`extendPath`/`realIntegral` packaging together exceed the shared
   ~8-line core. Dropped "genuinely new to this repository" from the module docstring
   and `COMPARISON.md:215`.
2. **Softened "needs the a.e.-FTC toolkit" (finding 2).** Route 2 first bullet now says
   the AC / a.e.-FTC toolkit is the route we would take, and records the FTC-free
   classical Picard-iteration alternative; the module docstring no longer overstates.
3. **Minimal imports (finding 3).** Replaced `import Mathlib` with
   `Mathlib.Analysis.Calculus.Deriv.MeanValue`,
   `Mathlib.Analysis.SpecialFunctions.ExpDeriv`,
   `Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus`. Verified by trial:
   `continuousOn_primitive_interval'` is reachable transitively through
   `FundThmCalculus`, so `DominatedConvergence` need not be imported explicitly. The
   build closure dropped from 8763 to 2680 jobs.
4. **Docstring self-contradiction (finding 4).** The header now states the resolution —
   "on every compact subinterval of `(0, S)` that same coefficient is in fact
   continuous" — in the same paragraph as the `L¹` mention, before the "Hypotheses
   actually used" section.

Post-fix gates (from `verification/`, `LEAN_NUM_THREADS=6`, one lake at a time):
`lake build NSFormalization.Section4.A04.Gronwall` → `Build completed successfully
(2680 jobs)`, exit 0; `lake env lean ../research/A04/axioms_g3.lean` → three
`[propext, Classical.choice, Quot.sound]` lines, exit 0; `make check` → exit 0.
