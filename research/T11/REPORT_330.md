# REPORT 330 — T11 / U9d1c: the endpoint Duhamel half-step, unconditional

## 1. Which theorem was proved

**`theorem NSFormalization.Section3.T11.torusHalfStepInput : TorusHalfStepInput`**
— lane 319's single residual analytic input, proved outright. Unfolded (and
re-checked verbatim in the probe, independently of the `def`):

```lean
∀ (ν : ℝ), 0 < ν → ∀ (C : TorusTwoSpaceContract ν)
  (a : SpatialField) (g : SpaceTimeField) (T : ℝ),
  a ∈ initialClassT → ContDiff ℝ ∞ g → IsPeriodicOn univ g → 0 < T →
  ∀ (A : PeriodicSobolev 3) (F P u : ℝ → PeriodicSobolev 3),
    IsPeriodicDatum 3 a A → IsPeriodicSobolevPath 3 g F →
    (∀ t : ℝ, 0 ≤ t → IsPeriodicLerayDatum (F t) (P t)) →
    TorusForcedMildOn C A P T u →
    ∀ r : ℝ, 3 ≤ r → ∀ v : ℝ → PeriodicSobolev r,
      ContinuousOn v (Ico 0 T) →
      (∀ t ∈ Ico 0 T, IsPeriodicReweight 3 r (u t) (v t)) →
      ∃ w : ℝ → PeriodicSobolev (r + 1 / 2),
        ContinuousOn w (Ico 0 T) ∧
        ∀ t ∈ Ico 0 T, IsPeriodicReweight r (r + 1 / 2) (v t) (w t)
```

Because `PeriodicSobolev` is phantom-indexed over one `ℓ²` carrier, the
conclusion is the honest ℓ²-membership statement
`k ↦ W(k)^{1/4}(v t)_i(k) ∈ ℓ²` plus continuity in `t` — a real half-order
gain, not a re-indexing.

Consequences, now unconditional (the input is discharged, the horizon `T` is
unchanged, no shrinkage):

* `persistence_halfOrder_ladder_unconditional` — the order ladder
  `3 + n/2` for every `n : ℕ`;
* **`persistence_unconditional`** — for every `m : ℕ` a continuous order-`m`
  datum path `u_m` on `Ico 0 T` with `IsPeriodicReweight 3 m (u t) (u_m t)` and
  a bound on every compact subset. This is `torusForcedMildOn_persistence` with
  its hypothesis removed.

Non-vacuity: `persistence_unconditional_constant` instantiates all hypotheses on
the constant-datum family of `Persistence.lean` (`a = g = const c`, mild solution
`t ↦ (1+t)•torusConstantDatum 3 c`), and the probe's
`constant_persistence_nonzero` shows the produced `u_m t` is nonzero whenever
`c i ≠ 0` (the zero mode carries `(1+t)c`).

**The route.** With `σ := r + 1/2`,

`w(t) = e^{νtΔ}A′ + ∫₀ᵗ e^{ν(t−τ)Δ}P_σ(τ) dτ − ∫₀ᵗ S_frac(ν(t−τ)) Q_r(v τ, v τ) dτ`,

`A′` the order-`σ` datum of the smooth `a` (`exists_periodicDatum_smooth`), `P_σ`
a **continuous** order-`σ` Leray force path, `Q_r` lane 328's real-order
projected convolution (values in `H^{r−1}`), `S_frac` lane 329's gain-`3/2`
smoothing with kernel `(ν(t−τ))^{-3/4}`. The three coefficient identities

* `heat`: `W^{(σ−3)/2}` commutes with the heat symbol,
* `force`: `W^{(σ−3)/2}` passes through the interval integral,
* `nonlinear`: `W^{3/4}·W^{(r−3)/2} = W^{(σ−3)/2}·W^{1/2}`
  (`torusHalfStep_weight_identity`),

turn `w(t)` into the order-`σ` transport of the order-three Duhamel formula of
`TorusForcedMildOn`, hence into the transport of `u(t)` itself.

**Deviation from the brief, and why.** The brief routed the force through
`S_frac` as well. That cannot work: the gain `σ` costs the kernel
`(t−τ)^{-σ/2}`, integrable only for `σ < 2`, while `r ≥ 3` is arbitrary — so the
smooth force must be used at the *top* order, where the plain bounded heat
semigroup suffices and no singular kernel is needed. Details in
`ATTEMPTS_DUHAMEL_HALF_STEP.md` §1–2.

## 2. What is in Lean now

New module `formalization/NSFormalization/Section3/T11/DuhamelHalfStep.lean`
(577 lines, 43 named declarations + 2 named local instances), four sections
beyond the target:

| declaration | content |
|---|---|
| `torusDatum_ext`, `torusCoeff_norm_le`, `torusEvalCLM`, `torusCoeff_intervalIntegral` | coefficient extensionality; `‖A.1 i k‖ ≤ ‖A‖`; coefficient evaluation as a real CLM; Bochner interval integrals computed coefficientwise |
| `torusLerayCLM (s : ℝ) : PeriodicSobolev s →L[ℝ] PeriodicSobolev s` | the periodic Leray projector as a **bounded** operator at every real order (`Section3/T10/Leray.lean` only had the existential `leray_exists_contraction`), with `torusLerayCLM_coeff`, `torusLeray_reweight` (commutes with order transport) and `torusLerayCLM_eq_of_isDatum` (uniqueness) |
| `exists_continuous_lerayForcePath (σ : ℝ)` | a smooth space-periodic force has a **continuous** Leray datum path at every *real* order, transporting the order-three path: integer-order continuity (`T10.ForcePaths.continuous_datum_path`) at `m = ⌈σ⌉₊`, then the bounded descent `persistenceDown`, then the bounded Leray |
| `torusFracContract r hr hν` | a genuine `MNS2.EndpointSafeTwoSpaceDuhamelContract ℝ (PeriodicSobolev (r+1/2)) (PeriodicSobolev (r-1))`: `torusHeatCLM` / `torusHeatSmoothingCLM_frac (r-1)` / `torusConvolutionCLM_real r hr` / majorant `torusFracMajorant ν τ = (ντ + (3/4)e^{-1})^{3/4}(ντ)^{-3/4}`, with `torusFracSymbol_add`, `torusFracConst_mono`, `torusFracMajorant_intervalIntegrable`. All of HeliCorgi's endpoint-safe integrability and continuity theory then applies verbatim |
| `torusHalfStepField`, `torusFracDuhamel_continuousOn`, `torusHalfStepField_continuousOn` | the field above; continuity of the singular Duhamel integral on the half-open window `Ico 0 T` (closed subwindows + `ContinuousWithinAt.mono_of_mem_nhdsWithin`) |
| `torusHalfStep_down_eq`, `torusFracDuhamelIntegrand_coeff`, `torusHalfStepField_coeff` | `persistenceDown r 3 (v s) = u s`; the integrand identity; **the half-step coefficient identity** `(w t).1 i k = W(k)^{(r+1/2−3)/2}·(u t).1 i k` on `Ico 0 T` |
| `torusHalfStepInput`, `persistence_halfOrder_ladder_unconditional`, `persistence_unconditional` | the target and its two consumers |
| `isSolenoidal_const`, `constantDatum_mem_initialClassT`, `torusConstantDatum_solenoidal`, `torusConstantDatum_lerayDatum`, `persistence_unconditional_constant` | non-vacuity |

No existing module was modified. No `sorry`/`admit`/`axiom`/`native_decide`; no
`set_option maxHeartbeats` anywhere; every `instance` carries an explicit name.

Files: the module; `research/T11/probes/duhamel_half_step_closes.lean`;
`research/T11/axioms_duhamel_half_step.lean`;
`research/T11/ATTEMPTS_DUHAMEL_HALF_STEP.md`; this report; one appended
paragraph in `research/T11/EXISTENCE_ROUTE.md` and one line in
`research/T11/T11_SPLIT.md`.

## 3. Gaps

* **No residual input in this lane.** Nothing is assumed beyond the statement's
  own hypotheses; there is no `def … : Prop`, alias or structure packaging any
  part of the goal.
* **Coefficients, not fields.** `persistence_unconditional` yields order-`m`
  *coefficient* data. Recovering a physical velocity field with `C^∞` spatial
  slices is U9d's Fourier-inversion problem (lane 318, partial). Time
  regularity, pressure and the momentum equation are untouched (U9d2).
* **Smoothness of `g` is needed globally.** `continuous_datum_path` requires
  `ContDiff ℝ ∞ g` on all of space-time; there is no `ContDiffOn`-on-a-slab
  version in the tree, so `exists_continuous_lerayForcePath` inherits that
  hypothesis. Harmless here (`TorusHalfStepInput` assumes exactly this), but it
  blocks a future slab variant.
* **Not sharp.** `torusFracMajorant` and lane 328's `torusConvolutionConstant_real`
  are upper bounds only; nothing quantitative (lifespan, smallness) is claimed.
* **A contract inhabitant is still needed downstream.** `TorusTwoSpaceContract ν`
  is a hypothesis here; `torusTwoSpaceContract_nonempty` discharges it from
  `TorusConvolutionInput`, which lane 328 proved (`torusConvolutionInput_ofReal`),
  so the chain is closed, but this lane does not re-assemble it.
* No error text remains: both new Lean files and the audit compile with zero
  errors and zero warnings. Errors met during development and their fixes are in
  `ATTEMPTS_DUHAMEL_HALF_STEP.md` §3.

## 4. Commands and results

```
cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.DuhamelHalfStep
  → ✔ [9987/9987] Built NSFormalization.Section3.T11.DuhamelHalfStep (5.6s)
    Build completed successfully (9987 jobs).  [0 errors; the only warnings in the
    log are pre-existing, in Paper1/*, Source/* and vendor/HeliCorgi/*]

cd verification && lake env lean ../formalization/NSFormalization/Section3/T11/DuhamelHalfStep.lean
  → no output (0 errors, 0 warnings), exit 0

cd verification && lake env lean ../research/T11/probes/duhamel_half_step_closes.lean
  → no output (0 errors, 0 warnings); the verbatim `TorusHalfStepInput` statement,
    both lane-319 consumers, `exists_continuous_lerayForcePath`,
    `torusFracContract`, `torusLerayCLM` and the nonzero constant instance all close;
    3 embedded `#guard_msgs` axiom checks pass

cd verification && lake env lean ../research/T11/axioms_duhamel_half_step.lean
  → no output: all 45 declarations (43 theorems/defs + 2 local instances) print
    exactly [propext, Classical.choice, Quot.sound]

make check   (from the worktree root)
  → check_formalization_plan / check_contracts OK; test_contract_policy 13/13 OK;
    check_work_queue: "45 work items: ownership, contract registration and task
    cards consistent."

grep -n "sorry|admit|native_decide|^axiom|maxHeartbeats" on the module, probe and
audit → no hits (the only match is the word "axioms" inside the audit's docstring).
```

## Review corrections (codex, ACCEPT-WITH-NOTES)
Two qualifications requested by the reviewer: the "slab-continuity" gap noted in §3 is specific to the T10/torus vocabulary (no `ContDiffOn`-slab force-path lemma in the tree), and the "Fourier-inversion" gap is specific to the torus coefficient carrier; neither is a gap in the proved theorem. See `research/T11/REVIEW_330-T11-U9d1c-duhamel-half-step.md`.
