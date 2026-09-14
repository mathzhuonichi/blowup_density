# REVIEW — lane 121 (A04 / G1 sub-lemma SL4 = `hpr`, the pressure drop)

Reviewer run in the lane worktree `.claude/worktrees/121-A04-hpr-leray-adjoint`
(branch `erenup/121-A04-hpr-leray-adjoint`, one commit `aceaae2` on merge-base
`8aab657` = `origin/erenup/integration`).  Module under review:
`formalization/NSFormalization/Section4/A04/PressureDrop.lean` (249 lines, 10 declarations
+ one fit `example`).  Probes in `/tmp/rev121/`, reproduced verbatim in the appendices.

## Verdict: **ACCEPT-WITH-NOTES**

The module proves what it says, on the carrier's real inner product, in the binder shape the
consumer wants; axioms are the standard three; the statements are non-vacuous; the recorded
failures are honest.  All notes are record staleness or MAINT promotion — none blocks the merge.

**Bonus result (finding 13): with this lane's `hpr`, eq:Rhigh assembles end to end.** The
reviewer wrote `/tmp/rev121/assembly.lean` (appendix D), a 70-line reconstruction of
`Spec.lean:424-434` `energyIdentityHigh` from in-tree lemmas only, and it compiled **first try**
with standard axioms.  The `energyIdentityHigh` lane is **S**, not M.  Recipe in §5.

---

## 1. Compiles / axioms / hygiene — PASS

| command (worktree root, after `. scripts/lean-env.sh`) | result |
|---|---|
| `cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A04.PressureDrop` | `Build completed successfully (9940 jobs).` (only the 52 known vendor HeliCorgi warnings) |
| `cd verification && lake env lean ../formalization/NSFormalization/Section4/A04/PressureDrop.lean` | silent, exit 0 |
| `cd verification && lake env lean ../research/A04/axioms_hpr.lean` | 10 declarations, each `[propext, Classical.choice, Quot.sound]`, exit 0 |
| `make check` | exit 0 (`30 work items: ownership, contract registration and task cards consistent.`) |
| `make test` | exit 0, all registered contracts `checked; standard logical axioms only` |
| `grep -nE 'sorry\|admit\|axiom\|native_decide\|maxHeartbeats\|set_option' …/PressureDrop.lean` | 1 hit, line 46, inside the module docstring |
| `grep -nE '^\s*(instance\|def\|abbrev\|structure\|class\|notation\|scoped)' …/PressureDrop.lean` | **no match** (exit 1) — no new definition, no new instance |
| `cd verification && lake env lean ../research/A04/probes/hpr_probe{1,2}.lean` | both silent, exit 0 (the committed probe records still compile) |

The 10 declarations audited: `coordinates_inner_bilin`, `complementSymbolComplex_inner_left`,
`lerayComplementL2_inner_left`, `lerayComplementAmbient_inner_left`, `carrier_inner_eq`,
`lerayComplement_selfAdjoint`, `inner_lerayComplement_eq_zero_of_eq_zero`, `isSobolevDatum_zero`,
`velocity_datum_lerayComplement_eq_zero`, `pressure_drop`.

CI coverage: `formalization/NSFormalization.lean` (the library root aggregator) does **not** import
this module — but it does not import `A04/MomentumDatum.lean` or `A04/NonlinearBound.lean` either,
and `experiments/build_changed_lean.py --base-ref` (CI step, `contracts.yml:81`) compiles every
changed `.lean` as an explicit `lake build` target.  So the module *is* built in CI.  Pre-existing
repo-wide gap, not this lane's.

## 2. Statement fidelity — PASS

### (a) Signatures and the consumer fit

`#check` with `pp.fullNames` (`/tmp/rev121/fid.lean`) gives, for the headline theorem:

```
@NSFormalization.Section4.A04.pressure_drop : ∀ {ν : ℝ} {a : …A02.SpatialField}
  {f : …A02.SpaceTimeField} {T : ℝ} (u : …A02.ClassicalSolutionR ν a f T),
  NSFormalization.Section4.D01.MemForceR f →
    ∀ {m : ℕ} {t : ℝ}, t ∈ Set.Ioo 0 T →
      ∀ {G P : NSFormalization.Paper3.RealVectorSobolev ↑m},
        …D01.IsSobolevDatum (↑m) (fun x => u.velocity (t, x)) G →
          …D01.IsSobolevDatum (↑m)
              (fun x => NavierStokes.ProblemStatement.pressureGradient u.pressure t x) P →
            ⟪G, P⟫ = 0
```

Hypotheses are exactly `u, hf, ht, hG, hP` — nothing else, no extra `2 ≤ m` (correct: the pressure
drop holds at every order; `momentum_datum`'s `hm : 2 ≤ m` is needed only by *its* route).  The `hP`
argument is character-identical to `momentum_datum`'s `hP` (`A04/MomentumDatum.lean:149`); the `hG`
argument is `momentum_datum`'s `hGd` evaluated at `t` (`hGd t ⟨le_of_lt ht.1, ht.2⟩`).

The reviewer rebuilt the fit in /tmp rather than trusting the module's own `example`
(`/tmp/rev121/fit.lean`, appendix A), against **both** consumers:

* `fit_Rhigh` — `pressure_drop` fills `inner_energy_Rhigh`'s `hpr` slot (`HighEnergy.lean:136-146`),
  not just `inner_energy_assembly`'s.
* `fit_chain` — the real consumer shape: `momentum_datum` supplies `hmom` and `pressure_drop`
  supplies `hpr` **at the same `P`, from the same `hP`**, with `hf : A02.MemForceR f` handed to
  both.  Both `#print axioms` → `[propext, Classical.choice, Quot.sound]`.

### (b) The inner product is the carrier's real instance — PASS

`#synth InnerProductSpace ℝ (RealVectorSobolev (3:ℝ))` →
`PiLp.innerProductSpace fun x => ↥(NSFormalization.Source.RealSobolev.RealSobolevHilbert 3)`,
the single instance path (`PiLp.innerProductSpace` over lane 053's
`Paper3.realSobolevInnerProductSpace`, `Paper3/RealPositiveDensity.lean:27`).  The module defines
**no** instance and **no** local pairing (grep above returns nothing), so `⟪·,·⟫` in
`carrier_inner_eq` / `lerayComplement_selfAdjoint` / `pressure_drop` is the same `inner ℝ` that
`inner_energy_assembly` resolves at `E = RealVectorSobolev (m:ℝ)` — which `fit_chain` confirms by
unification.

`carrier_inner_eq` is **proved**, not `rfl` (it cannot be: it crosses ℝ↔ℂ).  Its two ingredients
are honest: `Paper3.realSobolev_inner_eq_ambient` (`A04/RealPairing.lean:77-78`) **is** `rfl` — the
`Submodule` inner product is literally the ambient one on coercions — and
`Paper3.real_inner_eq_re_complex` (`RealPairing.lean:66-71`) is lane 082's proved `L²` bridge.  The
`PiLp` sum is moved across `RCLike.re` by `map_sum`.  No instance is bypassed or re-derived.

### (c) The transverse datum uses only `ClassicalSolutionR` fields — PASS

`velocity_datum_lerayComplement_eq_zero` uses exactly two solution fields:
`u.velocity_smooth` (via `contDiff_slice`) and `u.divergence t ht' x`
(`A02/SolutionClass.lean:128`, the `∇·u = 0 on Ico 0 T` field).  `MemLp` comes from the datum
hypothesis itself (`memLp_of_isSobolevDatum`), not from an extra assumption.  No `hf`, no
`u.momentum`, no `u.sobolev`.  ATTEMPTS §4's defeq claim is real: `fun x => u.divergence t ht' x`
typechecks directly at the `∑ j, partialDeriv j … x j` shape with no conversion — reproduced in the
Ico probe below.

**`Ioo` can be `Ico`** for this lemma: `ht` is used only to build `ht' : t ∈ Ico 0 T`.  The
reviewer restated it on `Ico 0 T` with `set_option autoImplicit false` and the **identical proof
body** compiles (`/tmp/rev121/ico.lean`, appendix B), standard axioms.  Not a defect —
`pressure_drop` itself genuinely needs `Ioo` (both `D01.smoothL2_momentumResidual_slice`
(`MomentumSlice.lean:65`) and `D01.pin_pressureGradient_datum` (`PressureJets.lean:115`) take
`t ∈ Ioo 0 T`) — but the `Ico` form is free and reusable at `t = 0`.  Finding 4.

### (d) Non-vacuity — PASS (`/tmp/rev121/nonvac.lean`, appendix C)

* **`pressure_drop` on a concrete solution.**  Re-used the 117 reviewer's `zeroSol ν :
  ClassicalSolutionR ν 0 0 1` and `memForceR_zero`; `pressure_drop_on_zeroSol (ν) (m)` instantiates
  `pressure_drop` at `t = 1/2` with `G = P = 0` and both datum hypotheses discharged.  Compiles,
  standard axioms.  So the hypothesis bundle is satisfiable.
* **`lerayComplement_selfAdjoint` is not about the zero operator.**  `complementSymbol_not_zero`
  proves, for `ξ = EuclideanSpace.single 0 1`,
  `complementSymbolComplex ξ (r3FrequencyVectorComplex ξ) = r3FrequencyVectorComplex ξ ≠ 0`
  (the rank-one projection fixes the longitudinal direction; `Submodule.starProjection_eq_self_iff`
  + `Submodule.mem_span_singleton_self`).  The fibre symbol of `lerayComplement` is therefore a
  nonzero projection at every nonzero frequency, so `lerayComplement` cannot be identically zero.
* **Carrier level, conditional.**  `lerayComplement_ne_zero_on_gradients`: for any smooth `L²`
  **curl-free** `z` whose order-0 datum is nonzero, `lerayComplement 0 (orderZeroDatum hz) =
  orderZeroDatum hz ≠ 0` (lane 108's `lerayComplement_zero_orderZeroDatum_eq_self`).  The reviewer
  did **not** discharge `orderZeroDatum hz ≠ 0` for a concrete gradient: that needs the Plancherel
  norm identity `‖orderZeroDatum hz‖ = ‖z‖_{L²}`, which `D01/OrderZeroDatum.lean:43-55` records as
  *deliberately not proved in the tree*.  So the unconditional carrier witness is genuinely
  unavailable today; the symbol-level argument above is the substitute, and it settles the question.

### Manuscript fidelity

`paper/sections/appendix-a-local-theory.tex:137` reads *"The pressure term vanishes by
solenoidality."*  That is precisely `pressure_drop`: the only physical input beyond `∇p` having an
order-`m` datum is `u.divergence`.  The manuscript justifies it by "integrating by parts … Fourier
approximation"; the Lean proof does the Fourier-side version of the same content
(`⟪û, ξ p̂⟫ = 0` because `û ⟂ ξ`).  Faithful.

## 3. Consistency — PASS with MAINT notes

* **Imports**: 5 (`A04.MomentumDatum`, `A04.HighEnergy`, `D01.PressureJets`, `A04.RealPairing`,
  `Mathlib.Analysis.InnerProductSpace.Adjoint`).  Import-closure walk (python over `import` lines):
  **187 modules, 0 `A01`**.  ✔
* **No restated definitions.**  Zero `def`/`instance`/`structure`/`notation` in the module.  ✔
* **Duplication of the four `L²`/ambient facts** — none today, but three MAINT items (findings 6–8).
  `exact?` on `coordinates_inner_bilin`'s exact statement, with the whole `PressureJets`/`RealPairing`
  closure in scope and `maxHeartbeats 1000000`, returns verbatim:
  ```
  /tmp/rev121/dup.lean:15:2: error: `exact?` could not close the goal. Try `apply?` to see partial suggestions.
  ```
  The tree has only the **diagonal** `Leray.coordinates_inner_self`
  (`D01/LerayMultiplier.lean:415-431`); `coordinates_inner_bilin` is that proof character-for-character
  with `b'` threaded through.  It should be promoted and the diagonal made a corollary
  (`coordinates_inner_self b = coordinates_inner_bilin μ b b`).
* **`isSobolevDatum_zero`**: `grep -rn 'IsSobolevDatum.*fun _ : Space => (0 : Space)'` over
  `formalization/NSFormalization` matches **only this module**.  Lane 117's `datum_zero` lived only
  in the reviewer's `/tmp` probe (`REVIEW_SL8_ASSEMBLY.md` appendix A), and this reviewer had to
  write it a third time for appendix C.  Not a duplicate today; promote next to
  `isSobolevDatum_unique` (`D01/ForceClass.lean:286`).  Finding 8.
* **`velocity_datum_lerayComplement_eq_zero` vs `D01/PressureJets.lean`** — finding 9, the one
  substantive consistency note.  Two blocks are near-verbatim shared:
  - order-0 transversality: `PressureJets.lean:71-77` (`hi4`, for `∂ₜu`) is line-for-line
    `PressureDrop.lean:194-196` (`hc0`, for `u`) — same
    `lerayComplement_eq_zero_of_transverse 0 _ (orderZeroDatum_transverse_of_divergence_free …)`;
  - the order-0 → order-`m` lift: `PressureDrop.lean:197-206` is the same
    `h0m` / `isSobolevDatum_lower` / `isSobolevDatum_unique` / `lerayComplement_lowerVectorL` /
    `isSobolevDatum_lower_iff` skeleton as `isSobolevDatum_pressureGradient_lerayComplement`
    (`PressureJets.lean:97-112`).
  MAINT should factor one `D01.Leray` lemma pair —
  `lerayComplement_datum_eq_zero_of_divergence_free {s : ℝ} (hsm) (hdiv) (hG : IsSobolevDatum s z G) :
  lerayComplement s G = 0` (subsuming both order-0 uses and this lane's order-`m` statement) and a
  `lerayComplement_datum_lift` for the shared lift — and derive all three call sites from it.
* **MAINT promotion list assessment.**  The lane's list (four `L²`/ambient facts → `D01/LerayMultiplier`
  / `LerayDatum`) is right but incomplete.  Reviewer's amended list:
  | lemma | target |
  |---|---|
  | `coordinates_inner_bilin` | `D01/LerayMultiplier.lean` §IsometryBridge, next to `coordinates_inner_self` (make the diagonal a corollary) |
  | `complementSymbolComplex_inner_left` | `D01/LerayMultiplier.lean`, next to `complementSymbolComplex_apply` (:56) |
  | `lerayComplementL2_inner_left`, `lerayComplementAmbient_inner_left` | `D01/LerayMultiplier.lean`, next to `lerayComplementAmbient_apply` |
  | `carrier_inner_eq` | `A04/RealPairing.lean`, next to `realSobolev_inner_eq_ambient` (:77) — it is the vector version of that lemma |
  | `lerayComplement_selfAdjoint`, `inner_lerayComplement_eq_zero_of_eq_zero` | `D01/LerayDatum.lean` (carrier-level Leray facts) |
  | `isSobolevDatum_zero` | `D01/ForceClass.lean`, next to `isSobolevDatum_unique` (:286) |
  | `velocity_datum_lerayComplement_eq_zero` | keep in A04, but derive from a new shared `D01.Leray` lemma (finding 9) |

## 4. Honesty of `ATTEMPTS_HPR.md` — PASS, one failure reproduced verbatim

**Claim 1 (Route A unavailable) — reproduced.**  `grep -rn 'IsIdempotentElem.*[Ii]sSelfAdjoint|isSelfAdjoint_iff_isStarNormal'` over Mathlib returns exactly the two cited lemmas
(`Mathlib/Analysis/InnerProductSpace/Adjoint.lean:450`, `Mathlib/Analysis/CStarAlgebra/Projection.lean:49`),
both with `IsStarNormal` as **input**; source at `Adjoint.lean:449` reads
`/-- An idempotent operator is self-adjoint iff it is normal. -/`.  No `_of_norm_le_one` /
contractive-idempotent lemma exists (`grep 'norm_le_one'` over
`Mathlib/Analysis/InnerProductSpace/*.lean` + `Mathlib/Analysis/CStarAlgebra/*.lean` filtered on
`proj|selfadj|idem`: no hits).  Machine check, `/tmp/rev121/neg3.lean`:

```lean
example (T : E →L[ℝ] E) (hidem : IsIdempotentElem T) (hnorm : ‖T‖ ≤ 1) : IsSelfAdjoint T := by
  rw [ContinuousLinearMap.IsIdempotentElem.isSelfAdjoint_iff_isStarNormal hidem]
  exact?
```
verbatim output:
```
/tmp/rev121/neg3.lean:11:2: error: `exact?` could not close the goal. Try `apply?` to see partial suggestions.
```
(A bare `exact? : IsSelfAdjoint T` from the same hypotheses, `/tmp/rev121/neg.lean`, instead dies as
`(deterministic) timeout at whnf, maximum number of heartbeats (200000) has been reached` — worth
recording so the next lane does not read the timeout as "maybe it exists".)

**Claim 2 (Route B) — matches the module line for line.**  **Claim 3 (no `lowerVectorL`
injectivity/isometry)**: `grep 'lowerVectorL' | grep -iE 'inj|isometry|norm|mono'` over
`formalization/NSFormalization` returns no such lemma; the `isSobolevDatum_lower_iff` +
`isSobolevDatum_unique` detour is the right one.  **Claim 4 (divergence defeq)** — reproduced in
appendix B.  **Namespace pitfalls** — the `D01.MemForceR` vs `A02.MemForceR` split is visible in the
`#check` above and is `rfl`-equal (117's `fid_a.lean`); `fit_chain` passes an `A02.MemForceR` into
`pressure_drop` with no coercion.  Harmless (finding 5), and already in `LESSONS.md`.

## 5. For the lead — the `energyIdentityHigh` assembly recipe (size **S**)

Target: `research/A04/Spec.lean:424-434` field `energyIdentityHigh`.  Instantiate
**`A04.inner_energy_Rhigh`** (`Section4/A04/HighEnergy.lean:136-146`) at `E = RealVectorSobolev (m:ℝ)`,
with `C := Chigh m := A03.outerTameConst m`, `u2 := sobolevNormAt 2 w.velocity t`,
`uNorm := sobolevNormAt (m:ℝ) w.velocity t`, `grad := gradientSobolevNormAt (m:ℝ) w.velocity t`,
`fNorm := sobolevNormAt (m:ℝ) f t`.

| slot | lemma | file:line |
|---|---|---|
| — datum path `G` | `hpath m` where `hpath : HasSmoothSobolevPath T w.velocity` (the spec's own hypothesis) | `A04/DerivNorm.lean:87` |
| `hd` (`d = 2⟪G t, deriv G t⟫`) | take `d := 2 * ⟪G t, deriv G t⟫`, so `hd := rfl`; the `HasDerivAt` conjunct is `hasDerivAt_datumNormSq_of_contDiffOn hGc ht` + `congr_of_eventuallyEq` through `sobolevNormAt_eq` (exactly the body of `exists_hasDerivAt_sobolevNormAt_sq`, which cannot be used as a black box because the assembly needs *the same* `G` for `hmom`) | `A04/DerivNorm.lean:119`, `A04/Continuity.lean:84`, `A04/DerivNorm.lean:141` |
| `hmom` | `momentum_datum w hf (by omega : 2 ≤ m) hGd hGc ht hL hN hP hF` | `A04/MomentumDatum.lean:140` |
| `hlap` | `inner_datum_laplacian_le' m hsl (hGd t ht') hA' hA hL` | `A04/LaplacianAssembly.lean:354` |
| `hpr` | **`pressure_drop w hf ht (hGd t ht') hP`** — this lane | `A04/PressureDrop.lean:216` |
| `hnl` | `inner_advection_bound_slice w hm2 ht (hGd t ht') hN`, then `outerNormAt_le hm2 (A03.SmoothL2.memHmVector hsl m) h2 hmz` multiplied on the left by `grad ≥ 0` and reassociated (`nlinarith`) | `A04/NonlinearBound.lean:186`, `A04/HighEnergy.lean:187` |
| `hG` | `(sobolevNormAt_eq (hGd t ht')).symm` | `A04/Continuity.lean:84` |
| `hF` | `(sobolevNormAt_eq hF).symm` | same |

Inputs those need, all in tree:

* `hsl := C01.velocity_slice_smoothL2 w ht'` (`C01/VelocityJets.lean:85`),
  `hinf := C01.velocity_slice_memHInfty w ht'` (`:77`).
* `hA' : IsSobolevDatum ((m:ℝ)+1) …` = `isSobolevDatum_castOrder (cast_mid_order m) (hinf.2 (m+1)).choose_spec`,
  `hA : IsSobolevDatum ((m:ℝ)+2) …` = the same with `(((m+2:ℕ):ℝ) = (m:ℝ)+2) := by push_cast; ring`
  (`A04/LaplacianAssembly.lean:81,103`).
* `hL`, `hN`: `(memHInfty_iff_smoothSquareIntegrableJets.mpr (laplacian_slice_smoothL2 w ht)).2 m`
  and the same with `advection_slice_smoothL2 w ht` (`D01/Pressure.lean:223,291`) — `A05.SmoothL2`
  is defeq to `SmoothSquareIntegrableJets`, so no bridge is needed.
* `hP`: `exists_isSobolevDatum_pressureGradient_slice w hf ht m` (`D01/PressureJets.lean:141`, lane 117).
* `hF`: `(hf.2 m)` gives `Gf` with `IsSobolevPath`; `F := Gf t`, `hF := hFpath t (le_of_lt ht.1)`.
* finiteness for `outerNormAt_le`: `sobolevENorm_velocity_ne_top w 2 ht'` / `… w m ht'`
  (`A04/Continuity.lean:64`).

**Remaining gap: none analytic.**  The reviewer *executed* this recipe —
`/tmp/rev121/assembly.lean`, appendix D, 70 lines — and it compiled first try:
`'Rev121Asm.energyIdentityHigh_core' depends on axioms: [propext, Classical.choice, Quot.sound]`.
What is left for the lane is bookkeeping only:

1. a formalization `def Chigh (m : ℕ) : ℝ := A03.outerTameConst m` + `Chigh_pos` from
   `A03.outerTameConst_pos` (currently `Chigh` exists only in `Spec.lean:332`);
2. wrapping in the spec's exact ∀-prefix (the spec's `a ∈ initialClassR` hypothesis is simply
   unused — harmless);
3. contract V1 field + binding + test.

**The "SL3 Laplacian order shift" is not a gap.**  `inner_datum_laplacian_le'` already delivers
`hlap` (as `≤`, and `inner_datum_laplacian` as an equality) from the order-`(m+1)`/`(m+2)` data that
`C01.velocity_slice_memHInfty` hands out for free.  `G1_SPLIT.md`'s table is what says otherwise,
and it is stale — see finding 10.

**Size: S.**  One module, no new mathematics.

## 6. Numbered findings

| # | sev | finding |
|---|---|---|
| 1 | — | Build, `lake env lean`, 10 × standard axioms, `make check`, `make test` all green; no `sorry`/`axiom`/`set_option`/`maxHeartbeats`; no new `def`/`instance`. |
| 2 | — | Binder shapes match `momentum_datum` (`MomentumDatum.lean:140-160`) and both `inner_energy_assembly` / `inner_energy_Rhigh`; reviewer-written fits (`fit_Rhigh`, `fit_chain`) compile with standard axioms. |
| 3 | — | Inner product is the carrier's own `PiLp.innerProductSpace ∘ Paper3.realSobolevInnerProductSpace`; `realSobolev_inner_eq_ambient` is `rfl`, `carrier_inner_eq` is honestly proved; no instance shadowing. |
| 4 | LOW | `velocity_datum_lerayComplement_eq_zero` holds verbatim on `Ico 0 T` (proof body unchanged, verified). `Ioo` is inherited from `pressure_drop`'s upstream, which genuinely needs it. Free strengthening for a V2/MAINT pass; reusable at `t = 0`. |
| 5 | LOW | `pressure_drop` exports `D01.MemForceR`, `momentum_datum` exports `A02.MemForceR`; `rfl`-equal, consumers unaffected (verified by `fit_chain`). Already recorded in ATTEMPTS + `LESSONS.md`. |
| 6 | LOW (MAINT) | `coordinates_inner_bilin` strictly generalizes `Leray.coordinates_inner_self` (`D01/LerayMultiplier.lean:415`) with a character-identical proof. Promote; make the diagonal a corollary. `exact?` confirms it exists nowhere in tree or Mathlib. |
| 7 | LOW (MAINT) | The three Leray self-adjointness facts belong beside their definitions in `D01/LerayMultiplier.lean`; `carrier_inner_eq` belongs beside `realSobolev_inner_eq_ambient` in `A04/RealPairing.lean`. Amended promotion table in §3. |
| 8 | LOW (MAINT) | `isSobolevDatum_zero` is not an in-tree duplicate, but three lanes (117 probe, 121, this review) have now written it. Promote next to `isSobolevDatum_unique` (`D01/ForceClass.lean:286`). |
| 9 | MED (MAINT) | `velocity_datum_lerayComplement_eq_zero` duplicates `D01/PressureJets.lean:71-77` (order-0 transversality for `∂ₜu`) and `:97-112` (the order-`m` lift) near-verbatim. Factor one `D01.Leray.lerayComplement_datum_eq_zero_of_divergence_free` + `lerayComplement_datum_lift` and derive all three sites. Not a merge blocker; do it before the D01/A04 SIMP pass. |
| 10 | LOW | Record staleness in `research/A04/G1_SPLIT.md`: the sub-lemma table still marks **SL2** "open" (`momentum_datum`, `A04/MomentumDatum.lean:140`, is done), **SL3** "open" (`inner_datum_laplacian` / `inner_datum_laplacian_le'`, `A04/LaplacianAssembly.lean:330,354`, are done) and **SL5** "open" (its own `SL5_SPLIT.md` says CLOSED). The lane updated only its own SL4 row. Since §5 shows the *whole* of eq:Rhigh now assembles, these rows would misdirect the next lane — lead should fix them at merge. |
| 11 | LOW | `A04/HighEnergy.lean:24` still says lane 053's inner-product instance is "in PR, not yet on integration"; it is on integration (`Paper3/RealPositiveDensity.lean:27`). ATTEMPTS records this; docstring fix for MAINT. |
| 12 | INFO | `hf` in `pressure_drop` is a *route* hypothesis, not a mathematical one: the manuscript's pressure drop needs only `div u = 0` and `∇p` having an order-`m` datum. This route needs `hf` because it pins `P` through the momentum residual, whose datum needs `f(t,·) ∈ H^m`. Note for a hypothetical V2 with the IBP route; no action now. |
| 13 | — | **Bonus:** the full `energyIdentityHigh` assembles from in-tree lemmas (appendix D, first try, standard axioms). The assembly lane is **S**. |

---

## Appendix A — `/tmp/rev121/fit.lean` (consumer fit, reviewer-written)

```lean
import NSFormalization.Section4.A04.PressureDrop
open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Section4.A04
open NSFormalization.Section4.A02 (SpaceTimeField SpatialField ClassicalSolutionR)
open NSFormalization.Section4.D01
open NSFormalization.Paper3 (RealVectorSobolev)
open scoped RealInnerProductSpace ContDiff
namespace Rev121Fit
#synth InnerProductSpace ℝ (RealVectorSobolev (3 : ℝ))
-- → PiLp.innerProductSpace fun x => ↥(NSFormalization.Source.RealSobolev.RealSobolevHilbert 3)

theorem fit_Rhigh
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (u : ClassicalSolutionR ν a f T) (hf : MemForceR f)
    {m : ℕ} {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T)
    {G Gt N P L Fd : RealVectorSobolev (m : ℝ)} {grad C u2 uNorm fNorm d : ℝ}
    (hν : 0 ≤ ν) (hd : d = 2 * ⟪G, Gt⟫) (hmom : Gt = ν • L - N - P + Fd)
    (hlap : ⟪G, L⟫ ≤ -grad ^ 2) (hnl : -⟪G, N⟫ ≤ C * u2 * uNorm * grad)
    (hGn : ‖G‖ = uNorm) (hFn : ‖Fd‖ = fNorm)
    (hGd : IsSobolevDatum (m : ℝ) (fun x : Space => u.velocity (t, x)) G)
    (hPd : IsSobolevDatum (m : ℝ) (fun x : Space => pressureGradient u.pressure t x) P) :
    (1 / 2) * d + ν * grad ^ 2 ≤ C * u2 * uNorm * grad + fNorm * uNorm :=
  inner_energy_Rhigh hν hd hmom hlap (pressure_drop u hf ht hGd hPd) hnl hGn hFn

/-- `momentum_datum` supplies `hmom` and `pressure_drop` supplies `hpr` at the SAME `P`,
    from the SAME `hP`, with an `A02.MemForceR` handed to both. -/
theorem fit_chain
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (u : ClassicalSolutionR ν a f T) (hf : NSFormalization.Section4.A02.MemForceR f)
    {m : ℕ} (hm : 2 ≤ m) {Gfun : ℝ → RealVectorSobolev (m : ℝ)}
    (hGd : ∀ t ∈ Ico (0 : ℝ) T, IsSobolevDatum (m : ℝ) (fun x => u.velocity (t, x)) (Gfun t))
    (hGc : ContDiffOn ℝ ∞ Gfun (Ico (0 : ℝ) T))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) {L N P Fd : RealVectorSobolev (m : ℝ)}
    (hL : IsSobolevDatum (m : ℝ) (fun x => spatialLaplacian u.velocity t x) L)
    (hN : IsSobolevDatum (m : ℝ) (fun x => advection u.velocity t x) N)
    (hP : IsSobolevDatum (m : ℝ) (fun x => pressureGradient u.pressure t x) P)
    (hF : IsSobolevDatum (m : ℝ) (fun x => f (t, x)) Fd)
    {grad C u2 uNorm fNorm d : ℝ}
    (hν : 0 ≤ ν) (hd : d = 2 * ⟪Gfun t, deriv Gfun t⟫)
    (hlap : ⟪Gfun t, L⟫ ≤ -grad ^ 2) (hnl : -⟪Gfun t, N⟫ ≤ C * u2 * uNorm * grad)
    (hGn : ‖Gfun t‖ = uNorm) (hFn : ‖Fd‖ = fNorm) :
    (1 / 2) * d + ν * grad ^ 2 ≤ C * u2 * uNorm * grad + fNorm * uNorm :=
  inner_energy_Rhigh hν hd (momentum_datum u hf hm hGd hGc ht hL hN hP hF) hlap
    (pressure_drop u hf ht (hGd t ⟨le_of_lt ht.1, ht.2⟩) hP) hnl hGn hFn
end Rev121Fit
```
Output: both `#print axioms` → `[propext, Classical.choice, Quot.sound]`.

## Appendix B — `/tmp/rev121/ico.lean` (the `Ico` strengthening, finding 4)

`velocity_datum_lerayComplement_eq_zero_Ico` — hypothesis `ht : t ∈ Ico (0:ℝ) T`, `set_option
autoImplicit false in`, proof body **copied unchanged** from the module except
`have ht' := …` deleted and `ht` used directly (including
`have hdiv : ∀ x, ∑ j : Fin 3, partialDeriv j (fun y : Space => u.velocity (t, y)) x j = 0 :=
fun x => u.divergence t ht x`, which is ATTEMPTS §4's defeq claim).  Output:
`'Rev121Ico.velocity_datum_lerayComplement_eq_zero_Ico' depends on axioms: [propext, Classical.choice, Quot.sound]`.

## Appendix C — `/tmp/rev121/nonvac.lean` (non-vacuity)

```lean
/-- `pressure_drop` on a concrete solution at a concrete interior time. -/
theorem pressure_drop_on_zeroSol (ν : ℝ) (m : ℕ) :
    (⟪(0 : RealVectorSobolev (m : ℝ)), (0 : RealVectorSobolev (m : ℝ))⟫ : ℝ) = 0 :=
  pressure_drop (zeroSol ν) memForceR_zero (m := m) (t := 1/2)
    (by constructor <;> norm_num)
    (by have : (fun x : Space => (zeroSol ν).velocity (1/2, x)) = fun _ : Space => (0 : Space) := rfl
        rw [this]; exact datum_zero (m : ℝ))
    (by have : (fun x : Space => pressureGradient (zeroSol ν).pressure (1/2) x)
            = fun _ : Space => (0 : Space) := by funext x; simp [zeroSol, pressureGradient]
        rw [this]; exact datum_zero (m : ℝ))

theorem freqVec_ne_zero : MNS2.r3FrequencyVectorComplex (EuclideanSpace.single 0 (1 : ℝ)) ≠ 0 := by
  intro h
  have h0 : (MNS2.r3FrequencyVectorComplex (EuclideanSpace.single 0 (1:ℝ))) 0 = 0 := by rw [h]; rfl
  simp [MNS2.r3FrequencyVectorComplex] at h0

/-- The fibre symbol fixes the (nonzero) longitudinal direction: `lerayComplement` is not 0. -/
theorem complementSymbol_not_zero :
    complementSymbolComplex (EuclideanSpace.single 0 (1 : ℝ))
        (MNS2.r3FrequencyVectorComplex (EuclideanSpace.single 0 (1 : ℝ)))
      = MNS2.r3FrequencyVectorComplex (EuclideanSpace.single 0 (1 : ℝ))
    ∧ MNS2.r3FrequencyVectorComplex (EuclideanSpace.single 0 (1 : ℝ)) ≠ 0 := by
  refine ⟨?_, freqVec_ne_zero⟩
  simp only [complementSymbolComplex]
  exact (Submodule.starProjection_eq_self_iff …).2 (Submodule.mem_span_singleton_self _)

/-- Carrier level (conditional on a nonzero order-0 datum, see §2(d)). -/
theorem lerayComplement_ne_zero_on_gradients {z : Space → Space} (hz : MemLp z 2 volume)
    (hsm : ContDiff ℝ ∞ z)
    (hcurl : ∀ (i j : Fin 3) (x : Space), partialDeriv i z x j = partialDeriv j z x i)
    (hne : orderZeroDatum hz ≠ 0) : ∃ A : RealVectorSobolev 0, lerayComplement 0 A ≠ 0 :=
  ⟨orderZeroDatum hz, by rw [lerayComplement_zero_orderZeroDatum_eq_self hz hsm hcurl]; exact hne⟩
```
(`zeroSol`, `memForceR_zero`, `datum_zero`, `jets_zero` copied from `REVIEW_SL8_ASSEMBLY.md`
appendix A.)  Output: all three `#print axioms` → `[propext, Classical.choice, Quot.sound]`.

## Appendix D — `/tmp/rev121/assembly.lean` (§5, the eq:Rhigh assembly, compiled first try)

```lean
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

/-- Reviewer's reconstruction of `Spec.lean:424-434` `energyIdentityHigh`,
with `Chigh m := A03.outerTameConst m`. -/
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
  obtain ⟨A1, hA1⟩ := hinf.2 (m + 1)
  have hA' := isSobolevDatum_castOrder (cast_mid_order m) hA1
  obtain ⟨A2, hA2⟩ := hinf.2 (m + 2)
  have hA := isSobolevDatum_castOrder
    (show (((m + 2 : ℕ) : ℝ)) = ((m : ℝ) + 2) by push_cast; ring) hA2
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
  · have hgrad0 : 0 ≤ gradientSobolevNormAt (m : ℝ) w.velocity t := ENNReal.toReal_nonneg
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
```
Verbatim output (the **only** output — no errors, no warnings):
```
'Rev121Asm.energyIdentityHigh_core' depends on axioms: [propext, Classical.choice, Quot.sound]
```
