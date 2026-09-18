# REPORT 322 — T11 U12, `higherOrderBound` (periodic `eq:Rhigh` + Grönwall)

Lane `322-T11-U12-high-order`, branch `erenup/322-T11-U12-high-order`.
**Partial, honest.** The target field is proved from exactly one written-out
hypothesis (the periodic `eq:Rhigh`); everything else in the chain is
unconditional. No `sorry`, no axiom, no named `Input` predicate.

## 1. 证了哪个定理 (what was proved)

**Main.** `NSFormalization.Section3.T11.higherOrderBound_of_energyInequality`
proves the `higherOrderBound` field of `PeriodicContinuationAPI`
(`research/T11/probes/api_on_canonical.lean:112-121`) **verbatim**:

> for `0 < ν`, `a ∈ initialClassT`, `f ∈ forceClassT`, `0 < S`, and any pair
> `(u,p)` with `SolvesBelowT ν a f S u p` and `squaredHTwoIntegralT S u ≠ ⊤`,
> every integer order `m` has a finite `M` with
> `periodicSobolevENorm m (u(t,·)) ≤ M` for all `t ∈ [0,S)`.

from one hypothesis: the manuscript's `eq:Rhigh`
(`appendix-a-local-theory.tex:131-138`) on a `ClassicalSolutionT`, at every
order `m ≥ 3` and every interior time, with the dissipation norm carried by an
existentially quantified `g ≥ 0`. `Chigh : ℕ → ℝ` is the manuscript's `C_m`;
Young's absorption produces `C_{m,ν} = C_m²/(4ν)`, the same value as Section 4.

**Unconditional (no hypothesis at all):**

| theorem | content |
|---|---|
| `periodicSobolevENorm_mono_order` | `r ≤ s → ‖z‖_{H^r} ≤ ‖z‖_{H^s}`, constant `1` (the torus weight is `≥ 1`); this is what covers the target's `m < 3` |
| `running_hTwo_integral_le` | the `ℝ≥0∞` criterion `squaredHTwoIntegralT S u ≠ ⊤` caps **every** running real integral `∫₀ᵗ‖u‖²_{H²}` by one constant, uniformly in the horizon of the local solution carrying `u` |
| `force_hm_profile_cap` | `f ∈ F_T` ⟹ `s ↦ ‖f(s)‖_{H^m}` continuous on `ℝ` and `∫₀ᵗ‖f‖_{H^m} ≤ B` for one `B` |
| `torusPressureDrop` | **the pressure term of `eq:Rhigh` vanishes** for a solenoidal velocity datum — pure symbol algebra on the lattice, exhibited in the probe at a nonzero velocity datum and a nonzero pressure-gradient datum |
| `torusLaplacianSymbol_pairing` / `_nonpos` | dissipation pairing `= −|2πk|²∑ᵢ|ûᵢ(k)|²` at each frequency, hence `≤ 0` |
| `torusRealPairing_le` | force term by Cauchy–Schwarz |
| `torusYoungAbsorb` | Young's absorption, fixing `C_{m,ν} = C_m²/(4ν)` |
| `torusGronwallChain` | `eq:Rhigh → eq:highcontinuation → Grönwall` on the real profiles |
| `continuousOn_torusSobolevNormAt_velocity` | the `H^m` profile of a solution is continuous on `[0,T)` |

Against the brief's four steps: **(3) force Cauchy–Schwarz** and **(4) Grönwall**
are complete; **(1)** is complete except for the two facts in §3; **(2)** is
*not* conditional on a named tame-product input, because the tame product alone
would not close (1) — see §3.

## 2. Lean 里现在有什么 (what is in Lean now)

* `formalization/NSFormalization/Section3/T11/HighOrder.lean` — 710 lines,
  24 declarations, namespace `NSFormalization.Section3.T11`, two **named** local
  normed instances (`highOrderNormedGroup/Space`, per `logs/LESSONS.md` 09-17).
  New imports beyond T11: `Section4.A01.Propagation` and `Section4.A04.Regularized`
  — both Mathlib-only modules of pure real analysis (`gronwall_bddAbove_Ico`,
  `sqrt_le_primitive_linear`). `Section4.A04.HighContinuation` was deliberately
  **not** imported (it would pull the whole whole-space energy chain into
  Section 3 for six lines of arithmetic; `torusYoungAbsorb` reproves that
  arithmetic, with the docstring saying so).
* `research/T11/probes/high_order_closes.lean` — the target field copied verbatim
  from `api_on_canonical.lean` and discharged; definitional checks; a sharpness
  check that the running `H²` cap does not depend on the local horizon; and the
  nonzero shear-mode witness for the pressure drop (kept out of the module so
  that every module declaration prints exactly the three standard axioms).
* `research/T11/axioms_high_order.lean` — `#guard_msgs`-checked `#print axioms`
  for all 24 module declarations, each exactly
  `[propext, Classical.choice, Quot.sound]`, plus two non-vacuity examples.
* `research/T11/ATTEMPTS_HIGH_ORDER.md` — every failed path with its exact error
  text, the reuse audit, and the residual in full.

Nothing existing was modified. No contract, binding or test was touched (U17
registers T11's contract; this lane only supplies the theorem).

## 3. 缺口是什么 (the gap)

The single hypothesis `hRhigh` of `higherOrderBound_of_energyInequality`. It is
*not* the target restated — it is a differential inequality at one interior time
of one local solution, and the passage to a uniform bound over all of `[0,S)` for
the glued `SolvesBelowT` field is what this module proves. Two independent facts
are missing for it, which is exactly why **no** `def … : Prop` named input was
introduced:

1. **Time differentiability of the coefficient path.** `ClassicalSolutionT.sobolev`
   supplies only `ContinuousOn G`; `eq:Rhigh` needs
   `HasDerivAt (‖G ·‖²) (2⟪G t, G' t⟫) t`, i.e. `PeriodicLocalRegularity.sobolev_smooth`,
   which `SolvesBelowT` does not carry. Section 4 obtained it from
   `A04.classical_hasSmoothSobolevPath` via the local carrier + uniqueness; the
   torus analogue runs through lane 321's `regularity`, still conditional on the
   open `PeriodicQuantitativeLocalInput'`. The momentum equation in datum form
   (Section 4's SL1/SL2) is missing with it.
2. **The torus tame product at the pairing level**,
   `|⟪(u·∇)u,u⟫_{H^m}| ≤ C_m‖u‖_{H²}‖u‖_{H^m}‖∇u‖_{H^m}`. T12's `tameProduct` is a
   *scalar physical-field* bound in `periodicScalarSobolevENorm` — an ingredient,
   not the estimate. Lane 328's `torusConvolutionCLM_real` (`H^r×H^r→H^{r-1}`) is
   the natural starting point; turning it into the pairing bound is open.

Suggested follow-up split (both are `L`, astra):
**U12a** — smooth datum path + momentum in datum form + the `H^m` energy identity
`½(‖u‖²_{H^m})' = ν⟪G,L⟫ − ⟪G,N⟫ + ⟪G,F⟫` on the torus carrier (the pressure term
is already discharged here);
**U12b** — the nonlinear pairing bound from lane 328's real-order convection CLM.
Their conjunction is exactly `hRhigh`, and `higherOrderBound` then follows by one
application of this lane's theorem.

Not a gap, but worth recording: `hRhigh`'s dissipation is `ν * g ^ 2` with
`g ≥ 0` existential rather than a fixed spelling of `‖∇u‖_{H^m}`, because T10's
`periodicHomogeneousENorm` is defined only for mean-zero fields and a velocity
slice with nonzero Galilean mean is not mean zero. This *weakens* the hypothesis,
so U12a/U12b are free to discharge it at the true gradient norm.

## 4. 跑了什么命令、什么结果 (commands and results)

```
cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.HighOrder
  → ✔ [9984/9984] Built … Build completed successfully (0 errors, 0 warnings)
cd verification && LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T11/HighOrder.lean
  → clean (no output)
cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/T11/probes/high_order_closes.lean
  → clean (no output): the verbatim target closes
cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/T11/axioms_high_order.lean
  → clean (no output): 36 #guard_msgs axiom prints all match
make check   (worktree root)
  → architecture checks OK; test_contract_policy 13/13 OK;
    check_work_queue: 45 work items consistent
```

Axiom audit: all 24 module declarations print exactly
`[propext, Classical.choice, Quot.sound]`. The shear-mode witness moved to the
probe, where `shearFreq`/`shearFreq_ne_neg` print `[propext]` and
`shearFreq_component_one` prints `[propext, Quot.sound]` — strict subsets, i.e.
no extra axiom anywhere. No `sorry`/`admit`/`axiom`/`native_decide`; no
`set_option maxHeartbeats`.
