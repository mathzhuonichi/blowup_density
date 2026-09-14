# REVIEW — lane 132 (D01 · C1b-m-D close: rows D-b-transport + D-close)

Reviewer run: worktree `.claude/worktrees/132-D01-db-transport`, branch `erenup/132-D01-db-transport`,
one commit `a94ba20` on top of merge-base `56b5757` with `origin/erenup/integration`.
Diff: `formalization/NSFormalization/Section4/D01/FiniteOrderConstructor.lean` (new, 347 lines),
`research/D01/ATTEMPTS_FINITE_ORDER_CLOSE.md` (new), `research/D01/axioms_finite_order_close.lean` (new),
table updates in `research/D01/FINITE_ORDER_SPLIT.md` and `research/A01/C1B_SPLIT.md`.
Nothing under `verification/` changed, so the registered contract closure is untouched.
Probes: `/tmp/rev132/` (all error text quoted below is copied into this file, per LESSONS 2026-09-14).

## Verdict: **ACCEPT-WITH-NOTES**

The mathematics is right, the statement is faithful, the hypotheses are load-bearing (two independent
collapse arguments), and the two promoted lemmas are byte-identical to the lane-125 reviewer probes.
Findings 4–8 are notes; finding 3 is an honesty correction to `ATTEMPTS`; nothing blocks the merge.

---

## 1. Compiles / axioms / hygiene — PASS

All from `.../132-D01-db-transport`, `. scripts/lean-env.sh`, `cd verification`, `LEAN_NUM_THREADS=6`.

```
$ lake build NSFormalization.Section4.D01.FiniteOrderConstructor
EXIT=0
Build completed successfully (9926 jobs).
```
(only pre-existing vendor/upstream linter warnings: `R3LerayComplexFiberSymbol.lean:42` unnecessarySimpa,
`PacketForceExtension.lean:44` deprecated `if_pos`, `SobolevDirectionalDerivative.lean:103` deprecated
`SchwartzMap.smul_apply`; none from the new module.)

```
$ lake env lean ../formalization/NSFormalization/Section4/D01/FiniteOrderConstructor.lean
EXIT=0     # 0 bytes of output — silent, so both `example`s elaborate too
```

```
$ lake env lean ../research/D01/axioms_finite_order_close.lean
EXIT=0
'…isSobolevDatum_partialDeriv_weak' depends on axioms: [propext, Classical.choice, Quot.sound]
'…db_cycles_full'                  … [propext, Classical.choice, Quot.sound]
'…memLp_coord_smul_datum'          … [propext, Classical.choice, Quot.sound]
'…HasWeakDerivsL2'                 … [propext, Classical.choice, Quot.sound]
'…weakDerivs_mono'                 … [propext, Classical.choice, Quot.sound]
'…exists_isSobolevDatum_of_memLp_derivs' … [propext, Classical.choice, Quot.sound]
'…smoothField_weakDeriv_pairing'   … [propext, Classical.choice, Quot.sound]
'…weakDerivs_smooth'               … [propext, Classical.choice, Quot.sound]
```

`#print axioms` cannot name an `example`, so the two module `example`s are **not** covered by that file.
I restated both as named theorems (`/tmp/rev132/p4_nonvac.lean`) and audited them:

```
'nonvac_hyp'           depends on axioms: [propext, Classical.choice, Quot.sound]
'nonvac_datum_agrees'  depends on axioms: [propext, Classical.choice, Quot.sound]
```

```
$ make check
EXIT=0
Ran 13 tests in 0.041s / OK
30 work items: ownership, contract registration and task cards consistent.
```
`make test` not run: no file under `verification/` changed, so the registered closure is bit-identical to base.

Hygiene grep over the two new Lean files for `sorry|admit|axiom|native_decide|maxHeartbeats|maxRecDepth|set_option`:
the only hit is the module docstring line 51 (`No sorry, no axiom; …`). No `set_option` anywhere — in
particular no heartbeat bump, which matters because the two `linear_combination` calls sit under a
`filter_upwards` with a 20-hypothesis context and still close in the default budget.

## 2. Statement fidelity

### (a) `HasWeakDerivsL2` — PASS, it is exactly what is advertised

`#check` with `pp.fullNames` (`/tmp/rev132/p1_checks.lean`) confirms all eight exports live in
`NSFormalization.Section4.D01` and that `IsSobolevDatum` resolves to `Section4.D01.IsSobolevDatum`
(`SmoothDatum.lean:237`), the verbatim restatement of `Contracts/V1/Data.lean:160` — not the A02 copy.

The unfolding is definitional (`/tmp/rev132/p2_unfold.lean`, both by `Iff.rfl`, EXIT=0):

```lean
HasWeakDerivsL2 z 0       ↔ MemLp z 2 volume
HasWeakDerivsL2 z (m+1)   ↔ MemLp z 2 volume ∧ ∀ j : Fin 3, ∃ w : Space → Space,
                              HasWeakDerivsL2 w m ∧
                              ∀ (i : Fin 3) (ψ : 𝓢(Space, ℂ)),
                                ∫ x, ψ x * (w x i : ℂ) = ∫ x, (-∂_{eⱼ} ψ) x * (z x i : ℂ)
```

**In words.** `HasWeakDerivsL2 z m` says: `z` is square integrable; and for every coordinate word of
length `≤ m`, the field obtained by applying that word is itself square integrable and is the weak
coordinate derivative of its parent in the Schwartz-pairing sense `∫ψ·(∂ⱼz)ᵢ = ∫(−∂ⱼψ)·zᵢ`, one
coordinate at a time, for every complex Schwartz test function and every component `i`. The derivative
fields are *existentially* quantified per coordinate (not a chosen family), they are required to be in
`L²` through the recursive call (whose base case is exactly `MemLp w 2`), and the recursion bottoms out
at `MemLp z 2`. **No smoothness, no continuity, no `SmoothL2Field`, no datum, no Fourier object appears
anywhere in the predicate.** The IBP sign is the standard one (`translation a u = u(·+a)` in the tree,
see §"Euler side" below, and the minus sits on `ψ`).

Two extra checks that it cannot be hiding regularity (`/tmp/rev132/p4b_nonvac.lean`, EXIT=0, both standard axioms):

```lean
theorem weakDerivs_congr : ∀ m z z', z =ᵐ[volume] z' → HasWeakDerivsL2 z m → HasWeakDerivsL2 z' m
theorem nonvac_nonsmooth (Z : SmoothL2Field Space) (m : ℕ) (S : Set Space) (hS : volume S = 0)
    (g : Space → Space) : HasWeakDerivsL2 (fun x => if x ∈ S then g x else Z.field x) m
```
i.e. the predicate is a.e.-invariant in `z`, so an arbitrary null-set edit of a smooth `L²` field — a
field that is discontinuous on a dense set — still satisfies it at every order. It is genuinely a weak
predicate, not smoothness in disguise.

### (b) The constant — PASS, and it is exactly the tree's angular convention

The advertised a.e. identity `(ξⱼ)·(A i) =ᵐ (frequencyUnit/(2πi))·(C j i)` is **internal** to the proof
(the `have heq`, in the division-free form `(2πi)·(ξⱼ • A i) =ᵐ c·(C j i)` with `c = frequencyUnit`);
the exported conclusion is only the `MemLp`. It is therefore kernel-checked (the `MemLp` proof goes
through `memLp_congr_ae heq`), but it is not available downstream — see finding 5.

Convention check. `Source/FourierConvention.lean:15` `def frequencyUnit : ℝ := 2 * Real.pi`, so
(`/tmp/rev132/p2_unfold.lean`, proved):

```lean
example : ((frequencyUnit : ℝ) : ℂ) / (2 * (Real.pi : ℂ) * Complex.I) = -Complex.I
```

So the identity is literally `ξⱼ·(A i) =ᵐ −i·(C j i)`, i.e. **`i·ξⱼ·(A i) = (C j i)`** — the angular
multiplier is `iξⱼ` with **no loose `2π`**, exactly lane 119's finding. Cross-checks:

* the cycles-side symbol is `sobolevDirectionalSymbol a ξ = 2πi·⟨ξ,a⟩·(1+‖ξ‖²)^{-1/2}`
  (`Paper3/SobolevDirectionalDerivative.lean:10`), Mathlib's cycles convention `𝓕f(ξ)=∫e^{-2πi⟨x,ξ⟩}f`;
  `db_cycles_full`'s conclusion carries `2πi·ξⱼ` in the cycles variable. Correct there.
* the angular variable is the cycles variable dilated by `c = frequencyUnit = 2π`
  (`angularFourier f ξ = c^{-3/2}·𝓕f(c⁻¹ξ)`), so `2πi·ξ_cyc,j = 2πi·(ξ_ang,j/2π) = i·ξ_ang,j`. Matches.
* `DerivativeDatum.lean:245` `isSobolevDatum_partialDeriv` advertises the multiplier
  `iξⱼ·(1+‖ξ‖²)^{-1/2}`; its Bessel factor is the **order drop** `m+1 → m`. In
  `memLp_coord_smul_datum` both `A` and `C j` sit at the *same* order `s`, so no Bessel factor is
  expected and none appears. Consistent.

### (c) Non-vacuity — PASS

The two module `example`s elaborate (silent `lake env lean`) and, restated as named theorems, print the
three standard axioms (§1). `weakDerivs_smooth` gives inhabitation at every order from any
`SmoothL2Field`, and `nonvac_datum_agrees` pins the constructed datum to `smoothAngularDatum` by
`isSobolevDatum_unique`, so the new route cannot be producing a *different* datum than D01's existing
smooth one. The non-smooth witness above (finding: a.e. edit) settles inhabitation outside `C^∞`.

I did **not** attempt the Lipschitz-compactly-supported witness: Mathlib has no packaged
"Lipschitz ⟹ Schwartz-pairing weak derivative" lemma at this pin, so it is a real (small) analysis
task, not a cheap `example`. The a.e.-edit witness above already discharges "not secretly smooth"
more cheaply and more strongly; the Lipschitz case is only interesting as a *regularity* example and
is not needed by anything downstream.

### (d) Negative check — PASS, two independent collapses

`/tmp/rev132/p3_neg.lean` with `set_option autoImplicit false` (LESSONS 2026-09-14 on silent
re-binding of deleted hypotheses), EXIT=0, both compile:

```lean
theorem free_constructor_collapse
    (freeCon : ∀ (m : ℕ) (z : Space → Space), MemLp z 2 volume →
      ∃ A : RealVectorSobolev (m : ℝ), IsSobolevDatum (m : ℝ) z A)
    {z} (hz : ContDiff ℝ ∞ z) (hL2 : MemLp z 2 volume) : MemLp (iteratedFDeriv ℝ 1 z) 2 volume

theorem free_transport_collapse
    (freeTransport : ∀ {s : ℝ} {y : Space → Space} {A : RealVectorSobolev s},
      IsSobolevDatum s y A → ∀ i j : Fin 3,
        MemLp (fun ξ => (ξ j : ℂ) • ((A i : RealSobolevHilbert s) : FourierData) ξ) 2 volume)
    {z} (hz : ContDiff ℝ ∞ z) (hL2 : MemLp z 2 volume) : MemLp (iteratedFDeriv ℝ 1 z) 2 volume
```

The first says: replace `HasWeakDerivsL2 z m` by bare `MemLp z 2` in
`exists_isSobolevDatum_of_memLp_derivs` and you prove `L² ∩ C^∞ ⊆ H¹`, which is false. The second is
the sharper one, aimed at the new lemma: drop the `C`-family **and** the pairing `hw` from
`memLp_coord_smul_datum` and the same collapse follows through
`raisableWitness_of_memLp_smul` → `isSobolevDatum_raise` → `memLp_iteratedFDeriv_of_isSobolevDatum`.
So the pairing hypotheses are not decoration; they carry the whole analytic content. (This is the
lane-125 reviewer's `free_raise_collapse` argument, re-derived one level up. As there, the *falsity* of
`L² ∩ C^∞ ⊆ H¹` is classical prose, not a Lean counterexample — the tree has no smooth `L²` field with
non-`L²` gradient. That is the same standard of evidence lane 125 was accepted on.)

## 3. Consistency

* **Imports.** Two: `Section4.D01.FiniteOrderDatum` and `Section4.D01.OrderZeroDatum` — the minimal
  pair (the raising step and the order-0 seed). Everything else arrives transitively. No `Contracts.*`,
  no `Formal.*`, no vendor import; the contract import policy does not apply (this is a
  `formalization/` module) and `make check` passes regardless.
* **No restated definitions.** `grep -rn "def HasWeakDeriv\|WeakDeriv\|weakDeriv" formalization/NSFormalization`
  returns nothing outside the new file: `HasWeakDerivsL2` is genuinely new, no shadowing, no duplicate
  of an existing predicate (LESSONS 2026-09-14 on scanning all of `{Source,Paper3,Paper1,Section4}`).
* **`db_cycles_full` / `isSobolevDatum_partialDeriv_weak` are byte-identical to the probes.** Machine
  diff of the extracted declarations: `isSobolevDatum_partialDeriv_weak` probe 949 chars vs module 949
  chars IDENTICAL; `db_cycles_full` probe 2891 vs module 2891 IDENTICAL. Credit is given in both
  docstrings. → finding 6 (MAINT).
* **The `rfl` claim holds** (`/tmp/rev132/p2_unfold.lean`):
  `example (s : ℝ) (f : SobolevHilbert s) : cyclesToAngular s f = angularFrequencyDilation (angularWeightEquiv s f) := rfl`
  — matching `Paper3/AngularTameProduct.lean:11` `(angularWeightEquiv s).trans angularFrequencyDilation.toContinuousLinearEquiv`.
  This is what makes the transport a five-line cancellation instead of the `Transverse.lean:177-205`
  symbol juggling; the lane's positive finding is real.
* **Placement.** The module belongs in `Section4/D01` (it is a datum-constructor, its two imports and
  all its ingredients are D01/Paper3, and it closes a `FINITE_ORDER_SPLIT.md` row). Yes.
* **Namespace hygiene.** The module sits inside `namespace NSFormalization.Section4.D01` and also
  `open NSFormalization.Paper3`. `angularFrequencyDilation_coeFn` exists in **both** (lane 109 left a
  `Section4.D01` alias at the old location); inside the module the enclosing namespace wins, so it
  resolves fine. A copy of the same proof pasted into a *neutral* namespace with both opened fails with
  `error: Ambiguous term angularFrequencyDilation_coeFn` — I hit this in `/tmp/rev132/p5_*` before
  putting the probes back into `NSFormalization.Section4.D01`. This is the already-recorded LESSONS
  entry, not a defect of this lane; noted so the next copier does not lose 10 minutes.

## 4. Honesty of `ATTEMPTS_FINITE_ORDER_CLOSE.md`

Method: mechanically regenerate `memLp_coord_smul_datum` into `namespace NSFormalization.Section4.D01`
with a single targeted mutation, three files, one control.

**Control** (`/tmp/rev132/q_control.lean`, unmodified copy): `EXIT=0`. The harness is faithful.

**Dead end 1 — flipped `linear_combination` signs: REPRODUCED EXACTLY.**
`/tmp/rev132/q_deadend1.lean` (coefficients negated), `EXIT=1`:

```
/tmp/rev132/q_deadend1.lean:66:4: error: ring failed, ring expressions not equal
…
⊢ ↑Real.pi * Complex.I * ↑(ξ.ofLp j) * ↑(frequencyUnit ^ (-3 / 2)) * angularWeightSymbol s (c⁻¹ • ξ) *
        ↑↑f (c⁻¹ • ξ) * 4 -
      ↑(frequencyUnit ^ (-3 / 2)) * angularWeightSymbol s (c⁻¹ • ξ) * ↑c * ↑↑g (c⁻¹ • ξ) * 2 =
    0
```
The record says "the residual `ring` goal came out as `… * 4 - … * 2 = 0` … exact error text
`ring failed, ring expressions not equal`". Both match verbatim. Accurate.

**Dead end 2 — `MemLp.const_smul` function-vs-lambda: PARTLY INACCURATE (finding 3).**
The record claims `MemLp.const_smul` "does **not** directly unify" with the lambda-shaped goal and that
the `memLp_congr_ae` detour is the fix. That is not what happens at this site. Replacing the module's
three-line `hRmem` block by the one-line term

```lean
  have hRmem : MemLp (fun ξ => ((c : ℝ) : ℂ) * (((C j i : RealSobolevHilbert s) : FourierData) : Space → ℂ) ξ) 2 volume :=
    (Lp.memLp ((C j i : RealSobolevHilbert s) : FourierData)).const_smul ((c : ℝ) : ℂ)
```
makes the **whole theorem compile**: `/tmp/rev132/q_deadend2.lean`, `EXIT=0`. Three separate phrasings
of the goal all elaborate (`/tmp/rev132/q_d2variants.lean`, EXIT=0): with `*`, with `•`, and in the
un-eta-expanded `(c • ⇑h)` form — `SMul ℂ ℂ` is `Mul.toSMul`, so they are reducibly defeq.

What *is* reproducible is the `simpa` route, and its error is word-for-word the one quoted in the
record (`/tmp/rev132/q_d2simpa.lean`, `EXIT=1`):

```
error: Type mismatch: After simplification, term
  MemLp.const_smul (Lp.memLp ↑h) ↑frequencyUnit
 has type
  @MemLp Space ℂ … (frequencyUnit • ↑↑↑h) 2 volume
but is expected to have type
  @MemLp Space ℂ … (fun ξ => ↑frequencyUnit * ↑↑↑h ξ) 2 volume
```
So the author did hit this error — via `simpa`, which normalises the hypothesis' `•` to `*` and then
fails on the eta shape — and then wrote the `memLp_congr_ae` detour, never retrying the bare `exact`.
The diagnosis in `ATTEMPTS` ("does not directly unify") is wrong; the symptom and the error text are
right. Net effect on the module: three unnecessary lines. The *second* `const_smul` site
(`hfin := hLmem.const_smul (2πi)⁻¹` with its `memLp_congr_ae`) is genuinely needed — that congruence
cancels the constant, it is not a smul/mul shim.

## 5. Findings

| # | Sev | Finding |
|---|---|---|
| 1 | — | **Compiles, standard axioms, no hygiene violations.** 8 declarations audited; the 2 `example`s audited separately as named theorems. `make check` green. |
| 2 | — | **Statement is faithful.** `HasWeakDerivsL2` unfolds by `Iff.rfl` to exactly "`MemLp z 2` + iterated coordinate weak derivatives in `L²` with the Schwartz pairing, to depth `m`"; no smoothness, no datum, a.e.-invariant in `z`. The constant is `iξⱼ` in the angular variable, no loose `2π`, consistent with lane 119 and with `isSobolevDatum_partialDeriv`. Hypotheses are load-bearing (two collapses). |
| 3 | **low** | `ATTEMPTS` dead end 2 mis-diagnosed: `MemLp.const_smul` *does* unify directly (`exact` works in all three phrasings); only the `simpa` route fails, with the quoted error. The `hRmem` detour is 3 removable lines — the whole theorem compiles without it (`/tmp/rev132/q_deadend2.lean` EXIT=0). Fix in a later SIMP pass, or leave; no correctness impact. Worth one line in `logs/LESSONS.md`: *"`simpa using h` can manufacture a fake unification failure by normalising `•`→`*` in the hypothesis only; try bare `exact` before writing a `memLp_congr_ae` shim."* |
| 4 | **low** | Docstring mislabel, twice (module header and §1): "the **dilation Jacobian** `frequencyUnit` … survives". The Jacobian factor is `c^{-3/2}` and it *cancels* (it is identical on both sides); the surviving `c` comes from the coordinate rescaling `(c⁻¹•ξ)ⱼ = c⁻¹·ξⱼ`. `ATTEMPTS` states this correctly. Also, since `frequencyUnit = 2π` the advertised constant `frequencyUnit/(2πi)` is just `−i`, i.e. the identity is the clean `i·ξⱼ·(A i) =ᵐ (C j i)` — saying so would make the convention legible at a glance. Docstring only; nothing frozen. |
| 5 | **low** | The angular a.e. identity is proof-internal (`have heq`), not exported; only the `MemLp` escapes. Row **D-euler-coord** will want the identity itself (to build the order-`m` datum of `∂ⱼz` *from* the datum of `z`, rather than just its `L²` witness). Cheap follow-up: promote `heq` to a standalone `theorem coord_smul_datum_ae` in the same module when that row is taken. |
| 6 | **low / MAINT** | `research/D01/probes/rev125_partialderiv_weak.lean` and `rev125_db_cycles.lean` now duplicate the tree byte-for-byte (verified). They are dead weight and can drift. Suggest replacing each with a one-line pointer to `FiniteOrderConstructor.lean`, or deleting them, in a MAINT commit. `rev125_collapse.lean`, `rev125_converse.lean`, `rev125_nonvac.lean` stay — they carry negative/converse content that is not in the tree. |
| 7 | **low** | No test closure imports `FiniteOrderConstructor` (`NSFormalization.lean` contains no `Section4` import at all, so `lake build`'s default target misses it; `verification`'s registered contracts do not reach it). CI *does* compile it on this PR via `experiments/build_changed_lean.py --base-ref`, but after merge it can rot silently when `LerayLowering` / `SmoothDatum` / `AngularTameProduct` / `DerivativeDatum` change — LESSONS 2026-09-14 (068 conformance drift). The lane already records the mitigation; lead should keep `research/D01/axioms_finite_order_close.lean` on the SIMP/tester checklist. Pre-existing pattern (same as lane 125), not a regression. |
| 8 | **info** | `C1B_SPLIT.md` row C1b-m-E's flagged open item — *"whether `sobolevTranslation` is coordinatewise (reviewer did not verify)"* — is now **settled: it is, definitionally.** See the next section. |

---

## 6. For the lead: the Euler-side lane **D-euler-pairing**

### What it must prove

Two units. Sizes assume the `lean-install.sh` fixed cost is already paid.

**E1 — descent of every derivative word (M, ~60–90 lines, bookkeeping only).**
For `u : SobolevSpace 1 q` angle-invariant (clause 7 of `Source/OrdinaryForcedLocal.lean:47`,
`∀ θ t, sobolevTranslation 1 (q+1) (0,θ) (u t) = u t`) and every word `w : Fin n → Fin 4` with
`n + 3 ≤ q`, produce `z_w : EulerMeanSolenoidal.L2` with `ordinaryLift z_w = word 1 u _ w`.
Route: `word_has_jet 1 u r n (h : n+r ≤ q) w` → `ofJet` packages that jet as an element of
`SobolevSpace 1 r` whose `value` is `word 1 u _ w` (`value_ofJet`) → `exists_ordinary_value (hq : 3 ≤ r)`
on it. The angle-invariance side condition is now free: I verified (`/tmp/rev132/p6_euler.lean`, EXIT=0)

```lean
example (q : ℕ) (a : LiftDomain 1) (u : SobolevSpace 1 q) (w : SobolevWord q) :
    (sobolevTranslation 1 q a u).val w = translation 1 a (u.val w) := rfl
example (q n : ℕ) (u : SobolevSpace 1 q) (hn : n ≤ q) (w : Fin n → Fin 4) (θ : AddCircle (1:ℝ))
    (hu : sobolevTranslation 1 q (0, θ) u = u) :
    translation 1 (0, θ) (word 1 u hn w) = word 1 u hn w :=
  congrArg (fun v : SobolevSpace 1 q => v.val ⟨⟨n, Nat.lt_succ_of_le hn⟩, w⟩) hu
```
because `sobolevTranslation = liftOperator … (translation a)` acts on the array coordinatewise **by
`rfl`** (`Euler/CylinderSobolevOperators.lean:117`). **This closes C1b-m-E's open item.** The only
residual bookkeeping is relating `(ofJet J).val w'` to `word 1 u _ (w' ++ w)` so the invariance transfers
to the packaged element — a `jet_word_eq`-flavoured induction (vendor has `jet_word_eq` for the
full-depth case, `Euler/CylinderSobolevSpace.lean`).

**E2 — the actual obligation: strong `L²` translation derivative ⟹ Schwartz pairing (M, ~60–120 lines).**
The statement to prove, in D01's exact shape (this is what `HasWeakDerivsL2` consumes verbatim):

```lean
theorem schwartz_pairing_of_translation_hasDerivAt
    (j : Fin 3) {z w : EulerMeanSolenoidal.L2}
    (h : HasDerivAt (fun t : ℝ => EulerMeanSolenoidal.translation (t • coordinateVector j) z) w 0)
    (i : Fin 3) (ψ : SchwartzMap Space ℂ) :
    ∫ x, ψ x * ((w x i : ℝ) : ℂ) = ∫ x, (-∂_{coordinateVector j} ψ) x * ((z x i : ℝ) : ℂ)
```

Proof sketch and why the sign comes out right: the tree's convention is
`EulerMeanSolenoidal.translation a u = u(· + a)` (`Euler/MeanSolenoidalTranslation.lean:18`,
`translation_ae`), so `h` really is `w = ∂ⱼz` in the strong sense. Then
`t ↦ ∫ψ(x)·z(x+t eⱼ)dx` is the composition of the `L²`-pairing CLM `v ↦ ∫ψ·v` with the path, so by
`ContinuousLinearMap.hasFDerivAt.comp_hasDerivAt` (exactly the pattern of
`Euler/MeanSmoothRepresentative.lean:55-63` `ordinaryLift_hasDerivAt`) its derivative at `0` is
`∫ψ·wᵢ`. The same function equals `∫ψ(y − t eⱼ)·z(y)dy` by translation invariance of Lebesgue measure,
whose derivative at `0` is `∫(−∂ⱼψ)·zᵢ`. Equate.

### Does it need anything beyond IBP for strong `L²` translation derivatives?

**No.** In particular it does **not** need the compact cutoff of LESSONS 2026-09-14/094. That lesson
bites when one integrates by parts against a merely-`L²` field whose *classical* derivative is not
known integrable; here nothing is differentiated classically — the translation is moved onto `ψ` by an
exact change of variables, and the only derivative taken is the one `h` already supplies in `L²`. The
integrals all converge by Cauchy–Schwarz (`ψ ∈ 𝓢 ⊂ L²`, `z, w ∈ L²`).

The only genuinely analytic step is differentiating `t ↦ ∫ψ(y − t eⱼ)·z(y)dy` at `0`. Two routes:
* **direct**: `MeasureTheory.hasDerivAt_integral_of_dominated_loc_of_deriv_le`, dominating
  `|∂ₜψ(y−teⱼ)| ≤ sup_{|t|≤1}|∂ⱼψ(y−teⱼ)| ≲ (1+‖y‖)^{-N}` (Schwartz), times `z ∈ L²`, in `L¹`. ~80–120 lines.
* **cheaper, worth trying first**: put `ψ` on the other side of the isometry —
  `⟪ψ, translation (teⱼ) z⟫ = ⟪translation (−teⱼ) ψ, z⟫` — and use the vendor's own
  `EulerLpTranslation.SmoothL2Field.translation_contDiff` (already used by `exists_local`) for the
  smooth `L²` orbit of `ψ`. That turns E2 into a CLM composition plus the adjoint identity, ~40 lines,
  with no dominated convergence at all. Needs a `SchwartzMap → SmoothL2Field` packaging step (`ψ` is
  `ℂ`-valued and componentwise smooth with all `L²` derivatives, so this should be routine).

Also required, small: `ordinaryLift` intertwines spatial translations — **already in vendor**,
`Euler/MeanOrdinaryLift.lean:32` `ordinaryLift_translation`, plus `ordinaryLift` is a linear isometry
so `HasDerivAt` transfers down through injectivity. And the identification
`(standardDirection i).1 = coordinateVector i` for `i : Fin 3` (the 4th direction is the angle).

### Caveat the lead should price in

`exists_local {q} (hq : 6 ≤ q)` produces `T` **after** `q` is fixed, and E1 costs three Sobolev orders
(`exists_ordinary_value` needs `3 ≤ r`). So the chain delivers `HasWeakDerivsL2 (⇑(U t)) m` for
`m ≤ q − 2` on the interval `T = T(q)` — i.e. **each finite order `m` on its own interval**, not all
orders on one interval. `exists_isSobolevDatum_of_memLp_derivs` then fires at every `t ∈ [0,T(q)]` for
that `m`, which is exactly C1b-m-D as stated. Getting `MemHInfty`-strength (`∀ m` at a *common* `T`)
needs a `T` independent of `q` — persistence of regularity, a separate obligation, not part of
D-euler-pairing.

### Consumer in A01 (note for the next C1b lane)

`Section4/A01/CarrierBridge.lean:98,104` currently stops at order 0
(`isSobolevDatum_zero_ordinaryL2`, `exists_isSobolevDatum_zero_ordinaryL2`, both on
`U : EulerMeanSolenoidal.L2`). Once D-euler-pairing lands, the natural addition there is
`exists_isSobolevDatum_m_ordinaryL2 : HasWeakDerivsL2 (⇑U) m → ∃ A : RealVectorSobolev m, IsSobolevDatum m (⇑U) A`,
one `exact` on the new constructor, plus `IsSobolevDatum.congr_field` (`CarrierBridge.lean:79`) to move
it onto `velocity` via C1b-rep. `DatumPathContinuity.lean` should **not** consume it: its CLM bundling
(`orderZeroDatumCLM`, `:103`) relies on the order-0 tail being a composition of CLMs, and lane 125's
`raiseHilbert` is multiplication by the unbounded `(1+‖ξ‖²)^{1/2}` — row C1b-c8-m's recorded asymmetry
(*lowering is a CLM, raising is not*) is unchanged by this lane.

## 7. Commands run

From `.claude/worktrees/132-D01-db-transport`, `. scripts/lean-env.sh`, `cd verification`, `LEAN_NUM_THREADS=6`:

| command | result |
|---|---|
| `lake build NSFormalization.Section4.D01.FiniteOrderConstructor` | EXIT 0, `Build completed successfully (9926 jobs).` |
| `lake env lean ../formalization/NSFormalization/Section4/D01/FiniteOrderConstructor.lean` | EXIT 0, 0 bytes |
| `lake env lean ../research/D01/axioms_finite_order_close.lean` | EXIT 0, 8× `[propext, Classical.choice, Quot.sound]` |
| `make check` (repo root) | EXIT 0, 13 policy tests OK, 30 work items consistent |
| `lake env lean /tmp/rev132/p1_checks.lean` | EXIT 0 — `#check` all 8 with `pp.fullNames`; `IsSobolevDatum` = `Section4.D01.IsSobolevDatum` |
| `lake env lean /tmp/rev132/p2_unfold.lean` | EXIT 0 — `HasWeakDerivsL2` at 0 and `m+1` by `Iff.rfl`; `cyclesToAngular = dilation ∘ weight` by `rfl`; `frequencyUnit/(2πi) = -I` |
| `lake env lean /tmp/rev132/p3_neg.lean` | EXIT 0 — both collapse theorems (`autoImplicit false`) |
| `lake env lean /tmp/rev132/p4_nonvac.lean` | the two module `example`s as named theorems: standard axioms |
| `lake env lean /tmp/rev132/p4b_nonvac.lean` | EXIT 0 — `weakDerivs_congr`, `nonvac_nonsmooth`, standard axioms |
| `lake env lean /tmp/rev132/q_control.lean` | EXIT 0 (mutation harness faithful) |
| `lake env lean /tmp/rev132/q_deadend1.lean` | EXIT 1 — `ring failed, ring expressions not equal`, residual `… * 4 - … * 2 = 0` (record confirmed) |
| `lake env lean /tmp/rev132/q_deadend2.lean` | **EXIT 0** — the recorded dead end does not occur; detour removable |
| `lake env lean /tmp/rev132/q_d2variants.lean` | EXIT 0 — `const_smul` unifies in `*`, `•` and un-eta forms |
| `lake env lean /tmp/rev132/q_d2simpa.lean` | EXIT 1 — the `simpa` route reproduces the recorded `Type mismatch` verbatim |
| `lake build NSFormalization.Source.OrdinaryCylinderDescent` | EXIT 0 (3850 jobs) |
| `lake env lean /tmp/rev132/p6_euler.lean` | EXIT 0 — `sobolevTranslation` coordinatewise by `rfl`; word-level angle invariance by `congrArg` |
| declaration-level diff probes vs module (python) | `isSobolevDatum_partialDeriv_weak` 949/949 IDENTICAL; `db_cycles_full` 2891/2891 IDENTICAL |
