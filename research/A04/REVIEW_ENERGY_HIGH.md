# REVIEW — lane 128 (A04 unit G1 assembly: eq:Rhigh `energyIdentityHigh`)

Reviewed commit `ca05e91` on `erenup/128-A04-energy-identity-high`, diffed against the
merge-base `47118a1` with `origin/erenup/integration`.  Worktree
`.claude/worktrees/128-A04-energy-identity-high`; probes in `/tmp/rev128/`.

Target: `paper/sections/appendix-a-local-theory.tex:132-137` (eq:Rhigh), spec field
`research/A04/Spec.lean:424-434` `energyIdentityHigh`.

## Verdict: **ACCEPT**

The module compiles clean and silent, the three public declarations carry only the standard
three axioms, the theorem's statement is **token-for-token identical** to the spec field
(machine diff: 127 tokens each, zero differences), every name in it resolves to the intended
formalization definition, and each spec-vocabulary object except the `ClassicalSolutionR`
structure is `rfl`-bridgeable (verified, not asserted).  The hypothesis package is inhabited
and the derivative the theorem produces on the witness is forced to the right value.  The
ATTEMPTS table's three load-bearing claims all reproduce.

Six findings below, all LOW / INFO; none blocks the merge.  Findings 4 and 5 are notes for the
SIMP lane, finding 6 is a strengthening for the contract lane.

---

## 1. Compiles / axioms / hygiene — **PASS**

```
$ cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A04.EnergyIdentityHigh
EXIT=0
Build completed successfully (9950 jobs).
   (the only warnings are the 52 known benign vendor/HeliCorgi linter warnings)

$ lake env lean ../formalization/NSFormalization/Section4/A04/EnergyIdentityHigh.lean
EXIT=0     # 0 bytes of output — silent

$ lake env lean ../research/A04/axioms_energy_identity_high.lean
EXIT=0
'NSFormalization.Section4.A04.Chigh_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A04.energyIdentityHigh_core' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A04.energyIdentityHigh' depends on axioms: [propext, Classical.choice, Quot.sound]
   (the conformance `example` elaborated: no error, no output line of its own)

$ lake env lean /tmp/rev128/p7_misc.lean
'NSFormalization.Section4.A04.Chigh' depends on axioms: [propext, Classical.choice, Quot.sound]
   (the fourth public declaration, the `def`, which the conformance file does not print)

$ lake env lean ../research/A04/probes/hpr_probe1.lean      EXIT=0  (silent)
$ lake env lean ../research/A04/probes/hpr_probe2.lean      EXIT=0  (silent)
   — the two stale `A04.RealPairing` → `D01.RealPairing` import fixes are correct.
   The other two probes also still compile:
$ lake env lean ../research/A04/probes/energy_identity_high_probe.lean
'Rev121Asm.energyIdentityHigh_core' depends on axioms: [propext, Classical.choice, Quot.sound]
$ lake env lean ../research/A04/probes/fit_chain_probe.lean
'Rev121Fit.fit_Rhigh' / 'Rev121Fit.fit_chain' depend on axioms: [propext, Classical.choice, Quot.sound]

$ make check     EXIT=0   (13 contract-policy tests OK; "30 work items: ownership, contract
                           registration and task cards consistent.")
$ make test      EXIT=0   (all registered Tests modules "checked; standard logical axioms only")

$ grep -nE 'sorry|admit|\baxiom\b|native_decide|maxHeartbeats|set_option' \
    formalization/NSFormalization/Section4/A04/EnergyIdentityHigh.lean \
    research/A04/axioms_energy_identity_high.lean
(none)
```

## 2. Statement fidelity — **PASS**

### (a) Machine diff against the spec field — zero differences

Both statements extracted as text (spec `Spec.lean:424-434`; theorem
`EnergyIdentityHigh.lean:145-155` with the leading `theorem ` and trailing ` := by` stripped),
whitespace-normalized, then diffed line-wise and token-wise:

```
$ diff -u /tmp/rev128/spec_field.txt /tmp/rev128/thm.txt      → (NO DIFF)
$ diff -u /tmp/rev128/spec_tok.txt  /tmp/rev128/thm_tok.txt   → (NO TOKEN DIFF)
$ wc -l /tmp/rev128/spec_tok.txt /tmp/rev128/thm_tok.txt
 127 /tmp/rev128/spec_tok.txt
 127 /tmp/rev128/thm_tok.txt
```

So there is not even a local-restatement *name* difference at the source level: the two
statements are the same string.  The names of course resolve differently (spec → contract /
spec-local vocabulary, module → formalization vocabulary), so the resolution was checked with
`set_option pp.fullNames true` (`/tmp/rev128/p1_fullnames.lean`).  Every constant is the
intended one:

```
NSFormalization.Section4.A04.energyIdentityHigh : ∀ (ν : ℝ) (a : NSFormalization.Section4.A02.SpatialField)
  (f : NSFormalization.Section4.A02.SpaceTimeField) (T : ℝ),
  (0 : ℝ) < ν →
    a ∈ NSFormalization.Section4.A02.initialClassR →
      NSFormalization.Section4.D01.MemForceR f →
        ∀ (w : NSFormalization.Section4.A02.ClassicalSolutionR ν a f T),
          NSFormalization.Section4.A04.HasSmoothSobolevPath T w.velocity →
            ∀ (m : ℕ), (3 : ℕ) ≤ m → ∀ t ∈ Set.Ioo (0 : ℝ) T, ∃ d,
              HasDerivAt (fun r => NSFormalization.Section4.A04.sobolevNormAt (↑m) w.velocity r ^ (2 : ℕ)) d t ∧
                (1 / 2 : ℝ) * d + ν * NSFormalization.Section4.A04.gradientSobolevNormAt (↑m) w.velocity t ^ (2 : ℕ) ≤
                  NSFormalization.Section4.A04.Chigh m *
                      NSFormalization.Section4.A04.sobolevNormAt (2 : ℝ) w.velocity t *
                      NSFormalization.Section4.A04.sobolevNormAt (↑m) w.velocity t *
                      NSFormalization.Section4.A04.gradientSobolevNormAt (↑m) w.velocity t +
                    NSFormalization.Section4.A04.sobolevNormAt (↑m) f t *
                      NSFormalization.Section4.A04.sobolevNormAt (↑m) w.velocity t
```

Note the `MemForceR` resolves to `D01.MemForceR`, not the `A02.MemForceR` the `open` list
might suggest — the same phenomenon `logs/LESSONS.md` records for lane 111.  Harmless: both
are `rfl`-equal to `Contracts.V1.Data.MemForceR` (`Bindings/DatumLemmas.lean:119`,
`Bindings/Uniqueness.lean:50`), and the bridge was re-verified here.

**`HasSmoothSobolevPath` is the same predicate as the spec's** — verified, not assumed.
`/tmp/rev128/p5_hssp_bridge.lean` restates `Spec.lean:247`, `:183` and `:190` verbatim but in
the **contract** vocabulary (`BlowupDensity.Contracts.V1.Data.IsSobolevDatum`/`sobolevENorm`,
`BlowupDensity.Contracts.V1.TameProduct.gradientSobolevENorm`) and proves five `rfl` bridges:

```lean
theorem hssp_bridge : SpecHasSmoothSobolevPath = NSFormalization.Section4.A04.HasSmoothSobolevPath := rfl
theorem sobolevNormAt_bridge : SpecSobolevNormAt = NSFormalization.Section4.A04.sobolevNormAt := rfl
theorem gradientSobolevNormAt_bridge : SpecGradientSobolevNormAt = NSFormalization.Section4.A04.gradientSobolevNormAt := rfl
theorem initialClassR_bridge : (BlowupDensity.Contracts.V1.Data.initialClassR : Set SpatialField)
    = NSFormalization.Section4.A02.initialClassR := rfl
theorem memForceR_bridge (f : SpaceTimeField) :
    BlowupDensity.Contracts.V1.Data.MemForceR f = NSFormalization.Section4.D01.MemForceR f := rfl
```
```
$ lake env lean /tmp/rev128/p5_hssp_bridge.lean
EXIT=0
```

`HasSmoothSobolevPath` also has **exactly one** copy in `formalization/`
(`Section4/A04/DerivNorm.lean:87`); the other three occurrences are `research/A04/Spec.lean:247`,
the probe `research/A04/axioms_d1.lean:51` and a quotation in `REVIEW_D2.md` — none is a second
library definition.  `ClassicalSolutionR` is the one object with no `rfl` bridge — it is a
`structure`, the documented CLAUDE.md exception, handled by `Bindings.uniqueness_toA02`.

### (b) Against the manuscript display — exact

`paper/sections/appendix-a-local-theory.tex:132-137`:

```
\frac12\frac{\dd}{\dd t}\norm{u}_{H^m}^2 +\nu\norm{\nabla u}_{H^m}^2
 \le C_m\norm{u}_{H^2}\norm{u}_{H^m}\norm{\nabla u}_{H^m} +\norm{f}_{H^m}\norm{u}_{H^m}
```
with `:131` "For every integer $m\ge3$" and `:137-138` "The pressure term vanishes by solenoidality".

| manuscript | Lean | verdict |
|---|---|---|
| `½ (d/dt)‖u‖²_{H^m}` | `∃ d, HasDerivAt (fun r => sobolevNormAt m u r ^ 2) d t ∧ (1/2)*d + …` | exact; the `∃ d, HasDerivAt … ∧` packaging *asserts* the differentiability the manuscript's `d/dt` presupposes, which is strictly more than writing `deriv` |
| `+ ν‖∇u‖²_{H^m}` | `+ ν * gradientSobolevNormAt m u t ^ 2` | exact |
| `C_m‖u‖_{H²}‖u‖_{H^m}‖∇u‖_{H^m}` | `Chigh m * sobolevNormAt 2 u t * sobolevNormAt m u t * gradientSobolevNormAt m u t` | exact: **one** constant, three factors, orders `2 / m / m`, left-associated |
| `+‖f‖_{H^m}‖u‖_{H^m}` | `+ sobolevNormAt m f t * sobolevNormAt m u t` | exact |
| `m ≥ 3` integer | `∀ m : ℕ, 3 ≤ m` | exact |
| pressure absent | absent — discharged inside `pressure_drop` by `ClassicalSolutionR.divergence` | exact |

Two conventions worth stating explicitly, neither a deviation:

* **`gradientSobolevNormAt` is `‖∇u‖_{H^m}`, not `‖u‖_{H^{m+1}}`.**
  `A03.gradientSobolevENorm s v = columnsSobolevENorm s (fun j => partialDeriv j v)
  = (∑_{j<3} ‖∂ⱼv‖²_{H^s})^{1/2}` (`A03/OuterTameProduct.lean:75,88`), i.e. literally the
  Frobenius `H^m` norm of the gradient.  That is the manuscript's own quantity; the
  `‖u‖_{H^{m+1}}`-shaped reading (which would be a *different*, equivalent-up-to-constants
  statement) is **not** what is stated.  Good.
* **The derivative is the two-sided `HasDerivAt` on the open interval `Ioo 0 T`.**  This is the
  faithful reading — at `t = 0` only the one-sided derivative can exist, and the manuscript's
  identity is used on intervals of smooth existence.  It does mean the Lean field says nothing
  at `t = 0`; the underlying datum path (`HasSmoothSobolevPath`) is `C^∞` on `Ico 0 T`, so a
  one-sided `HasDerivWithinAt` at `0` would be available if a consumer ever needed it.  Not a
  defect — noting it so no one later mistakes the gap for an oversight.

### (c) Load-bearing hypotheses — the ATTEMPTS table reproduces on all three claims

* **`a ∈ initialClassR` is genuinely unused.**  Confirmed structurally, not by deletion:
  `energyIdentityHigh_core` simply does not have the hypothesis, and it proves the same
  conclusion.  `#check @…energyIdentityHigh_core` (pp.fullNames, `/tmp/rev128/p1.log`):
  ```
  @NSFormalization.Section4.A04.energyIdentityHigh_core : ∀ {ν : ℝ} {a : …SpatialField}
    {f : …SpaceTimeField} {T : ℝ}, (0 : ℝ) < ν → …D01.MemForceR f →
      ∀ (w : …A02.ClassicalSolutionR ν a f T), …A04.HasSmoothSobolevPath T w.velocity →
        ∀ (m : ℕ), (3 : ℕ) ≤ m → ∀ {t : ℝ}, t ∈ Set.Ioo (0 : ℝ) T → ∃ d, …
  ```
  (`a` survives only as the implicit index of `ClassicalSolutionR`, which is unavoidable.)
  This sidesteps the two recorded traps at once: the `autoImplicit` false negative of lesson
  077 and the "omit the argument and re-apply" false positive of lesson 113.
* **`3 ≤ m` can be weakened to `2 ≤ m`** — confirmed.  `/tmp/rev128/p2_weak_m.lean` is the core
  copied verbatim with `(hm : 3 ≤ m)` → `(hm : 2 ≤ m)` and `have hm2 : 2 ≤ m := by omega` →
  `:= hm`:
  ```
  $ lake env lean /tmp/rev128/p2_weak_m.lean
  EXIT=0    (silent)
  ```
* **`0 < ν` can be weakened to `0 ≤ ν`** — confirmed.  `/tmp/rev128/p3_weak_nu.lean` is the core
  with `(hν : 0 < ν)` → `(hν : 0 ≤ ν)` and `inner_energy_Rhigh (le_of_lt hν) rfl` →
  `inner_energy_Rhigh hν rfl`:
  ```
  $ lake env lean /tmp/rev128/p3_weak_nu.lean
  EXIT=0    (silent)
  ```
  (`inner_energy_Rhigh` itself only asks `0 ≤ ν`, `A04/HighEnergy.lean:137`.)

Both weakenings are **strengthenings of the theorem, recorded for a possible V2 — not a change
request**: the spec field states `0 < ν` and `3 ≤ m`, the manuscript states `m ≥ 3` at `:131`
and `ν > 0` throughout, and the lane is right to state the field exactly as the spec does.

`MemForceR f`, `HasSmoothSobolevPath T w.velocity` and `t ∈ Ioo 0 T` are used at named sites in
the proof body (`hf.2 m`, `exists_isSobolevDatum_pressureGradient_slice … hf`, `momentum_datum
… hf`, `pressure_drop … hf`; `obtain ⟨G, hGd, hGc⟩ := hpath m`; `ht`/`ht'`), as the table says.

### (d) Non-vacuity — **PASS**

`/tmp/rev128/p4_vacuity.lean` rebuilds `zeroSol` (`research/D01/REVIEW_SL8_ASSEMBLY.md`
appendix A) in this import closure, supplies the missing `HasSmoothSobolevPath` witness, and
instantiates the **spec field itself**:

```lean
theorem path_zero (ν : ℝ) : HasSmoothSobolevPath 1 (zeroSol ν).velocity := by
  intro m
  exact ⟨fun _ => 0, fun t _ => datum_zero _, contDiffOn_const⟩

theorem rhigh_on_zeroSol : ∃ d : ℝ, HasDerivAt (fun r : ℝ => sobolevNormAt ((3:ℕ):ℝ) (zeroSol 1).velocity r ^ 2) d (1/2) ∧ … :=
  energyIdentityHigh 1 0 0 1 one_pos zero_mem_initialClassR memForceR_zero (zeroSol 1)
    (path_zero 1) 3 le_rfl (1/2) (by constructor <;> norm_num)

theorem d_forced_zero {d : ℝ} (hd : HasDerivAt (fun r : ℝ => sobolevNormAt ((3:ℕ):ℝ) (zeroSol 1).velocity r ^ 2) d (1/2)) : d = 0
```
```
$ lake env lean /tmp/rev128/p4_vacuity.lean
EXIT=0
'Rev128.rhigh_on_zeroSol' depends on axioms: [propext, Classical.choice, Quot.sound]
'Rev128.d_forced_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
```

So (i) the whole hypothesis package — `0 < ν`, `0 ∈ initialClassR`, `MemForceR 0`, a
`ClassicalSolutionR`, `HasSmoothSobolevPath`, `3 ≤ m`, `t ∈ Ioo 0 T` — is inhabited, and
`HasSmoothSobolevPath` in particular is not an unsatisfiable clause; (ii) the `d` the theorem
returns on this witness is **forced** to `0` (proved by `HasDerivAt.unique` against the
constant-zero path, using `sobolevNormAt s 0 t = 0`), so `d = 0` is not merely consistent — it
is the only possibility, and on the zero solution the display degenerates correctly to `0 ≤ 0`.

**Does the inequality have content?**  The real vacuity risk here is *not* the RHS being zero —
it is the `.toReal` convention: `sobolevNormAt`/`gradientSobolevNormAt` are `ENNReal.toReal`, so
a `⊤` norm silently reads as `0`.  If `gradientSobolevENorm` were `⊤` on real solutions, the
dissipation `ν‖∇u‖²_{H^m}` on the left would vanish and eq:Rhigh would collapse to
`(1/2)d ≤ ‖f‖‖u‖`.  It is not.  `Continuity.lean:64,73` already give
`sobolevENorm_velocity_ne_top` / `sobolevENorm_force_ne_top` for the three `sobolevNormAt`
slots; for the fourth, the reviewer proved the missing one (`/tmp/rev128/p6_finite.lean`,
compiled first try):

```lean
theorem gradientSobolevENorm_velocity_ne_top {ν : ℝ} {a : SpatialField} {f : SpaceTimeField}
    {T : ℝ} (w : ClassicalSolutionR ν a f T) (m : ℕ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    gradientSobolevENorm (m : ℝ) (fun x : Space => w.velocity (t, x)) ≠ ⊤
```
```
$ lake env lean /tmp/rev128/p6_finite.lean
EXIT=0
'Rev128Fin.gradientSobolevENorm_velocity_ne_top' depends on axioms: [propext, Classical.choice, Quot.sound]
```
(route: `velocity_slice_memHInfty` at order `m+1` → `D01.isSobolevDatum_partialDeriv` per column
→ `sobolevENorm_le_of_isSobolevDatum` → `A03.columnsSobolevENorm_le_sum` + `ENNReal.sum_ne_top`.)

Hence all four quantities in eq:Rhigh are genuine finite norms on the class the field is
quantified over, and the statement is a real differential inequality: with `f = 0` it says
`(1/2)(d/dt)‖u‖²_{H^m} ≤ C_m‖u‖_{H²}‖u‖_{H^m}‖∇u‖_{H^m} − ν‖∇u‖²_{H^m}`, which is exactly the
inequality G2 then absorbs by Young's to get eq:highcontinuation.  The one thing that cannot be
demonstrated by instantiation today is a witness with `‖∇u‖_{H^m} ≠ 0`: no nonzero classical
solution exists in tree yet (that is A01's job), so `zeroSol` is the only inhabitant available
and on it both sides are `0`.  See finding 6.

## 3. Consistency with the tree — **PASS**, findings 1-5

* **Imports.**  Six, all used: `A04.{PressureDrop, NonlinearBound, LaplacianAssembly, DerivNorm}`,
  `A03.OuterTameProduct`, `C01.VelocityJets`.  `inner_energy_Rhigh`/`outerNormAt_le`
  (`A04/HighEnergy.lean`) and `momentum_datum` (`A04/MomentumDatum.lean`) arrive through
  `PressureDrop`, which imports both directly.  Transitive closure: 117 local
  `NSFormalization.*` modules (22 `D01`, 15 `A04`, 5 `A03`, 1 each `A01/A02/A05/C01/I03`, plus
  Paper3/Paper1/Source).  See finding 3 about the single `A01` module.
* **No restated definitions.**  `Chigh` is a new `def` (correct — it is the contract's own
  constant, not a copy of anything) and the only one.  `HasSmoothSobolevPath`,
  `sobolevNormAt`, `gradientSobolevNormAt`, `MemForceR`, `initialClassR`, `ClassicalSolutionR`
  are all imported, none re-declared — confirmed by grep over `formalization/` (`def
  HasSmoothSobolevPath` appears once, at `DerivNorm.lean:87`).  `Chigh`/`Chigh_pos` do not
  collide with any existing name.
* The `Chigh` docstring claim "eq:tame's `6 · vectorTameConst`" is accurate:
  `A03/OuterTameProduct.lean:166` `def outerTameConst (k : ℕ) : ℝ := 6 * vectorTameConst k`.

### Finding 1 — LOW (note only): the promoted probe is now redundant

`research/A04/probes/energy_identity_high_probe.lean` still carries
`Rev121Asm.energyIdentityHigh_core`, which a normalized diff shows is the module's
`energyIdentityHigh_core` **character for character** (only the probe's trailing
`#print axioms` / `end Rev121Asm` differ):

```
$ diff -u /tmp/rev128/probe_core.txt /tmp/rev128/mod_core.txt
@@ -51,5 +51,3 @@
 (sobolevNormAt_eq hF).symm
-#print axioms energyIdentityHigh_core
-end Rev121Asm
```

This is strong corroboration of the "promoted verbatim" claim, so it is *good* that the probe is
still there for this review.  But from now on it is a second copy that can silently drift, and
nothing in CI compiles it.  Recommend the SIMP lane either delete it (the module plus this
review record the provenance) or leave a one-line header saying it is superseded by
`Section4/A04/EnergyIdentityHigh.lean`.  No action needed in this lane.

### Finding 2 — LOW (note for SIMP): `A04/HighEnergy.lean:24` docstring is stale

```
formalization/NSFormalization/Section4/A04/HighEnergy.lean:24:
(lane 053's `Paper3.realSobolevInnerProductSpace`, in PR, not yet on integration).
```
Lane 053 landed; `#check @NSFormalization.Paper3.realSobolevInnerProductSpace` resolves on this
branch.  The surrounding paragraph also still lists items (i)-(v) as "not proved here", and
(i)-(iv) are all now done (`TimeDerivative.lean`, `MomentumDatum.lean`,
`LaplacianAssembly.lean`, `PressureDrop.lean`).  Untouched by this lane — flagging for SIMP.

### Finding 3 — LOW (pre-existing, not this lane): one `A01` module in the A04 closure

`NSFormalization.Section4.A01.ConvectionDivergence` is in the import closure, pulled in by
`A04/AdvectionDivergence.lean:1`, which predates this lane.  `DEPENDENCY_GRAPH.md:205-209`
declares `A04 ← A02, A03`, so this is a (benign, acyclic — `lake build` is clean) layering
deviation already on integration.  Recorded so it is not mistaken for a lane-128 regression.

### Finding 4 — INFO: `G1_SPLIT.md`'s SL7 row is now stale

The lane correctly updated the `assembly` row and the closing paragraph, but the SL7 row
(`G1_SPLIT.md:51`) still reads "carrier identifications need lane 053 | lane 053 instance for
`⟪⟫`↔`sobolevNormAt`".  Lane 053 is merged and SL7's identifications are exactly the
`sobolevNormAt_eq` calls the assembled core now makes.  One-line fix, SIMP or a later A04 lane.

### Finding 5 — INFO: the `open` list exports `D01.MemForceR`, not `A02.MemForceR`

Already covered in §2(a); harmless (`rfl`-equal), but the contract lane should write the
qualified name in `Bindings/` rather than rely on the `open`, per lesson 111.

## 4. Honesty of `research/A04/ATTEMPTS_ENERGY_HIGH.md` — **PASS**

Every checkable claim was reproduced:

| claim | verified by |
|---|---|
| core "promoted verbatim" from the 121 probe | normalized diff, finding 1 — character-identical |
| `Chigh` unfolds so a bare `exact` closes the wrapper | the module's proof is `intro …; exact energyIdentityHigh_core …` and compiles; `#print Chigh` shows the plain `def` |
| `a ∈ initialClassR` unused | §2(c), by the core's `#check` |
| `0 < ν` has slack (`0 ≤ ν` suffices) | `/tmp/rev128/p3_weak_nu.lean`, EXIT=0 |
| `3 ≤ m` has slack (`2 ≤ m` suffices) | `/tmp/rev128/p2_weak_m.lean`, EXIT=0 |
| `MemForceR`, `HasSmoothSobolevPath`, `t ∈ Ioo 0 T` load-bearing | named use sites in the proof body |
| nothing needed restating; the five objects already live in `formalization/` | grep over `formalization/`, §3 |
| the two stale probe imports fixed, both compile | §1, both EXIT=0 silent |
| `make check` passes | §1, EXIT=0 |
| "Failures: none" | nothing hidden was found; every probe in this review that mirrors the lane's route compiled |
| "no A04 partial contract registered yet" | `verification/contracts.json` mentions A04 only inside other contracts' "NOT asserted" clauses — confirmed |

No recorded failure to reproduce (the ATTEMPTS honestly records that there were none).  The one
thing the table does not say, and could: the `0 ≤ ν` / `2 ≤ m` slack is *inherited* from the
sub-lemmas (`inner_energy_Rhigh` asks `0 ≤ ν` at `HighEnergy.lean:137`; `outerNormAt_le` and
`inner_advection_bound_slice` ask `2 ≤ m`), not an accident of this assembly.

---

## 5. For the lead — the A04 partial contract lane (`Contracts/V1/EnergyHighPartial.lean`)

**Status.**  No A04 contract is registered.  `verification/contracts.json` contains no A04 entry;
`grep -rn 'sobolevNormAt\|gradientSobolevNormAt\|HasSmoothSobolevPath' verification/Contracts/V1/*.lean`
returns **nothing**.  So all three of eq:Rhigh's spec-local defs are new to `Contracts/V1`.

**Fields.**  Three, shaped like `Contracts/V1/EnergyAbsorptionPartial.lean` (whose
`EnergyAbsorptionPartialAPI` also carries data fields `C_1`/`C_1_pos` alongside statement
fields, making it a `Type` and its binding a `def` — same here):

* `Chigh : ℕ → ℝ` — opaque, per the decision recorded in `research/A04/COMPARISON.md:66` and
  `Spec.lean:325-339`;
* `Chigh_pos : ∀ m : ℕ, 0 < Chigh m`;
* `energyIdentityHigh` — the field statement copied token-for-token from `Spec.lean:424-434`
  (which, by §2(a), is also token-for-token the proved theorem).

**Vocabulary — what must be restated in the contract, and what is already there.**

| object | in `Contracts/V1`? | action |
|---|---|---|
| `ClassicalSolutionR`, `initialClassR`, `MemForceR`, `SpatialField`, `SpaceTimeField`, `IsSobolevDatum`, `sobolevENorm` | **yes** — `Contracts/V1/Data.lean:99,104,160,…` | use directly |
| `gradientSobolevENorm` | **yes** — `Contracts/V1/TameProduct.lean:192` | use directly |
| `RealVectorSobolev` | yes, via `Paper3` (contracts already import it) | use directly |
| `sobolevNormAt` | **no** | restate verbatim: `(sobolevENorm s fun x : Space => u (t, x)).toReal` |
| `gradientSobolevNormAt` | **no** | restate verbatim: `(TameProduct.gradientSobolevENorm s fun x : Space => u (t, x)).toReal` |
| `HasSmoothSobolevPath` | **no** | restate verbatim (`Spec.lean:247` / `DerivNorm.lean:87`, they are the same text) |

All three restatements are `rfl`-bridgeable to the formalization definitions — **already
verified** in this review by `/tmp/rev128/p5_hssp_bridge.lean`, which is literally the three
contract-vocabulary restatements plus `:= rfl` bridges, EXIT=0.  So the binding's drift guards
are three one-line `rfl` theorems, and the contract-side restatement carries no risk.

**Binding.**  `Bindings/EnergyHighPartial.lean`, modelled on `EnergyAbsorptionPartial`'s
`velocityJets`:

* `Chigh := NSFormalization.Section4.A04.Chigh`, `Chigh_pos := …A04.Chigh_pos`, plus the drift
  bridge `Chigh_eq : Contract.Chigh = A04.Chigh := rfl` (trivially available since the field is
  assigned that constant);
* `energyIdentityHigh := fun ν a f T hν ha hf w hpath m hm t ht =>
  A04.energyIdentityHigh ν a f T hν ha hf (uniqueness_toA02 w) hpath m hm t ht` — the solution
  crosses the two `ClassicalSolutionR` copies field-by-field via the existing
  `Bindings/Uniqueness.lean:63` `uniqueness_toA02`, and **the conclusion needs no massaging**:
  `(uniqueness_toA02 w).velocity = w.velocity` holds by `rfl`
  (`Bindings/Uniqueness.lean:78-79` already states it as an `example`), and `w.velocity` is the
  only projection the statement mentions.  `hpath` transports for the same reason.
* `Tests/EnergyHighPartial.lean` asserting the standard three axioms.

**Two-agent statement comparison: it does NOT exist for this field.**
`research/A04/COMPARISON.md` is the *source-to-target* comparison (what already exists in the
three codebases vs. what the spec demands) — §2 "Field-by-field comparison", §4 "Bounded
implementation split".  It is not the CLAUDE.md rule-2 artifact (two read-only, mutually
blind agents each writing the Lean statement from the paper, then diffed).  `logs/AGENT_RUNS.csv`
confirms: A04's spec came from a **single** lane `030-A04-spec` with one reviewer
(`research/A04/REVIEW.md`, ACCEPT-WITH-NOTES), whereas R43/R44 did get paired blind drafts
(`037-R43-spec-A` / `038-R43-spec-B`, `046-R44-spec-A`).  Before freezing
`Contracts/V1/EnergyHighPartial.lean`, a short blind-restatement lane on eq:Rhigh alone
(`appendix-a-local-theory.tex:132-137`, paper-only, no access to `Spec.lean`) would close rule 2
cheaply — it is a single display, and this review has already pinned down the only two places a
second reader could legitimately disagree (`‖∇u‖_{H^m}` as the gradient norm vs. `‖u‖_{H^{m+1}}`,
and `Ioo 0 T` two-sided vs. `Ico 0 T` one-sided).

**One more thing the contract lane should decide (finding 6 — INFO, a strengthening).**
`Chigh m := A03.outerTameConst m`, and `Bindings/TameProduct.lean:102` binds the **registered**
`TameProductAPI.Ctame := A03.outerTameConst`.  So in the bound implementation
`Chigh = tame.Ctame` holds **by `rfl`** — precisely the identification `COMPARISON.md:66` and
`Spec.lean:332` say an implementation *may* make but the contract does not require.  Keeping
`Chigh` opaque in the contract is still right (it is what the manuscript licenses), but the
binding could cheaply export `Chigh_eq_Ctame : Chigh = tame.Ctame := rfl` as a bonus lemma, and
G2 (`Cgron m ν = (Chigh m)²/(4ν)`) will want it.

Also worth exporting from A04 while the contract lane is open: the reviewer's
`gradientSobolevENorm_velocity_ne_top` (§2(d), proof in `/tmp/rev128/p6_finite.lean`, ~12 lines).
It is the missing fourth member of `Continuity.lean`'s finiteness family, it is what makes
eq:Rhigh's left-hand dissipation a genuine norm rather than a `⊤ ↦ 0` artefact, and G2's Young
absorption will need exactly it.

---

## 6. Commands run

```
. scripts/lean-env.sh                                   # Lean 4.34.0-rc2
cd verification
LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A04.EnergyIdentityHigh       # EXIT=0, 9950 jobs
LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section4/A04/EnergyIdentityHigh.lean  # EXIT=0, silent
LEAN_NUM_THREADS=6 lake env lean ../research/A04/axioms_energy_identity_high.lean   # EXIT=0, 3x standard axioms
LEAN_NUM_THREADS=6 lake env lean ../research/A04/probes/{energy_identity_high_probe,fit_chain_probe,hpr_probe1,hpr_probe2}.lean  # all EXIT=0
LEAN_NUM_THREADS=6 lake env lean /tmp/rev128/p1_fullnames.lean    # resolved constants, EXIT=0
LEAN_NUM_THREADS=6 lake env lean /tmp/rev128/p2_weak_m.lean       # 2 ≤ m,  EXIT=0
LEAN_NUM_THREADS=6 lake env lean /tmp/rev128/p3_weak_nu.lean      # 0 ≤ ν,  EXIT=0
LEAN_NUM_THREADS=6 lake env lean /tmp/rev128/p4_vacuity.lean      # zeroSol instantiation + d=0, EXIT=0
LEAN_NUM_THREADS=6 lake env lean /tmp/rev128/p5_hssp_bridge.lean  # 5 rfl bridges, EXIT=0
LEAN_NUM_THREADS=6 lake env lean /tmp/rev128/p6_finite.lean       # gradient enorm ≠ ⊤, EXIT=0
LEAN_NUM_THREADS=6 lake env lean /tmp/rev128/p7_misc.lean         # #print axioms Chigh, EXIT=0
cd .. && make check                                               # EXIT=0
       make test                                                  # EXIT=0
diff -u /tmp/rev128/spec_tok.txt /tmp/rev128/thm_tok.txt          # no difference, 127 tokens each
diff -u /tmp/rev128/probe_core.txt /tmp/rev128/mod_core.txt       # only the probe's trailer
```

Probe sources are transient (`/tmp/rev128/`); every one of them is quoted above in the part that
carries the evidence, per `logs/LESSONS.md` (2026-09-14, lane 106).
