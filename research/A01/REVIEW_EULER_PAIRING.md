# REVIEW — lane 140-A01-euler-pairing (rows D-euler-pairing / C1b-m-E)

Reviewer run 2026-09-14, worktree `.claude/worktrees/140-A01-euler-pairing`, branch
`erenup/140-A01-euler-pairing` @ `181c47c`, merge-base `2aab3ad` with `origin/erenup/integration`.
Probes in `/tmp/rev140/` (contents of the load-bearing ones are transcribed below, per LESSONS
2026-09-14 "`/tmp` 探针是易失的").

## VERDICT: **ACCEPT-WITH-NOTES**

E2 (row D-euler-pairing) and E1 (row C1b-m-E) are both genuinely closed, with the *exact* statement
`HasWeakDerivsL2` consumes, the correct sign, standard axioms, and a real instantiation on
`exists_local`'s output.  Two doc-level notes (F2, F7) and one MAINT duplicate (F7); nothing blocking.

---

## 1. Compiles / axioms / hygiene — PASS

```
$ . scripts/lean-env.sh && cd verification
$ LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.D01.FiniteOrderConstructor \
      NSFormalization.Source.OrdinaryForcedLocal NSFormalization.Section4.A01.EulerPairing
Build completed successfully (9952 jobs).            # EXIT=0
$ LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section4/A01/EulerPairing.lean
                                                      # EXIT=0, 0 bytes of output (silent)
$ LEAN_NUM_THREADS=6 lake env lean ../research/A01/axioms_euler_pairing.lean   # EXIT=0
```
All **12** printed declarations (11 exports + `euler_pairing_nonvacuous`) report
`[propext, Classical.choice, Quot.sound]`.  Sample tail:

```
'NSFormalization.Section4.A01.weakDeriv_pairing_of_translation_hasDerivAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.exists_isSobolevDatum_m_of_ae' depends on axioms: [propext, Classical.choice, Quot.sound]
'euler_pairing_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound]
```

```
$ make check
python3 experiments/test_contract_policy.py → Ran 13 tests … OK
python3 experiments/check_work_queue.py  → 30 work items: ownership, contract registration and task cards consistent.
```

Hygiene grep on the new module:
```
$ grep -n 'sorry\|admit\|axiom\|native_decide\|maxHeartbeats\|set_option' \
      formalization/NSFormalization/Section4/A01/EulerPairing.lean
48:No `sorry`, no `axiom`; `#print axioms` is standard (`research/A01/axioms_euler_pairing.lean`).
90:set_option maxHeartbeats 400000 in
```
Line 48 is docstring prose.  **Exactly one** `set_option`, single-declaration (`… in`), on E2.
No `sorry`/`admit`/`native_decide` anywhere.

### F1 (INFO) — the heartbeat claim is exactly right
```
$ sed 's/400000/250000/' … > /tmp/rev140/EP250.lean   ; lake env lean /tmp/rev140/EP250.lean
EXIT=0   (7.53s user)
$ sed 's/^set_option maxHeartbeats 400000 in$//' … > /tmp/rev140/EP_default.lean ; lake env lean …
EXIT=1
/tmp/rev140/EP_default.lean:91:0: error: (deterministic) timeout at `whnf`, maximum number of
  heartbeats (200000) has been reached
```
250000 compiles in 7.5 s; the default 200000 genuinely fails on E2's *statement* elaboration (`whnf`,
not a proof search).  400000 is margin, ≤ the LESSONS ceiling, on one declaration, with the reason in
the comment above it.  Accept as written.

---

## 2. Statement fidelity — PASS (the strongest part of the lane)

All 11 exports `#check`ed with `pp.fullNames true` (`/tmp/rev140/check1.lean`, EXIT=0 apart from one
unknown-identifier on an unimported name I added myself).

### F2 (LOW, doc only) — the module header understates its own order budget
`EulerPairing.lean:42` says the chain delivers `HasWeakDerivsL2 (⇑(U t)) m` for **`m ≤ q − 3`**.  The
theorem actually delivers `m + 3 ≤ q + 1`, i.e. **`m ≤ q − 2`** — which is what `ATTEMPTS_EULER_PAIRING.md`,
`C1B_SPLIT.md` row C1b-m-E and `FINITE_ORDER_SPLIT.md` all say, and what the `#check` shows.  The
header is the only place with `q − 3`.  Harmless (it understates), but fix on the next touch of the file.

### (a) E2 — hypothesis and conclusion

`#check` (abridged):
```
NSFormalization.Section4.A01.weakDeriv_pairing_of_translation_hasDerivAt : ∀ (j : Fin 3)
  {z w : ↥EulerMeanSolenoidal.L2},
  HasDerivAt (fun t => (EulerMeanSolenoidal.translation (t • NavierStokes.ProblemStatement.coordinateVector j)) z) w 0 →
    ∀ (i : Fin 3) (ψ : 𝓢(NavierStokes.ProblemStatement.Space, ℂ)),
      ∫ (x : …Space), ψ x * ↑((↑↑w x).ofLp i) =
        ∫ (x : …Space), (-∂_{NavierStokes.ProblemStatement.coordinateVector j} ψ) x * ↑((↑↑z x).ofLp i)
```
The hypothesis is the **strong `L²` translation derivative at `t = 0`** along `coordinateVector j` —
literally the shape of `EulerCylinderSobolevSpace.word_hasDerivAt` after the `ordinaryLift` pullback
(`#check` of `word_hasDerivAt` confirms `HasDerivAt (fun t => translation period (translationPath period
(standardDirection i) t) (word …)) (word … (Fin.cons i w)) 0`, matching
`hasDerivAt_meanTranslation_of_lift`'s hypothesis with `period = 1`, `i = j.succ`).

**F3 (PASS) — the conclusion IS the `HasWeakDerivsL2` clause, not a paraphrase.**
`/tmp/rev140/fidelity.lean`, EXIT=0:
```lean
-- F1: the order-1 predicate unfolds to exactly that clause
example (z : Space → Space) :
    HasWeakDerivsL2 z 1 ↔
      (MemLp z 2 volume ∧ ∀ j : Fin 3, ∃ w : Space → Space, MemLp w 2 volume ∧
        (∀ (i : Fin 3) (ψ : SchwartzMap Space ℂ),
          ∫ x, ψ x * ((w x i : ℝ) : ℂ)
            = ∫ x, (-∂_{coordinateVector j} ψ) x * ((z x i : ℝ) : ℂ))) := Iff.rfl

-- F2: E2 alone builds the predicate, by the anonymous constructor (no `convert`, no rewriting)
example (z : EulerMeanSolenoidal.L2) (W : Fin 3 → EulerMeanSolenoidal.L2)
    (h : ∀ j : Fin 3,
      HasDerivAt (fun t : ℝ => EulerMeanSolenoidal.translation (t • coordinateVector j) z) (W j) 0) :
    HasWeakDerivsL2 (⇑z) 1 :=
  ⟨Lp.memLp z, fun j => ⟨⇑(W j), Lp.memLp (W j),
    fun i ψ => weakDeriv_pairing_of_translation_hasDerivAt j (h j) i ψ⟩⟩
```
Both `Iff.rfl` and the anonymous constructor go through: the pairing shape is syntactically identical.

**F4 (PASS) — the sign is right, checked against an independently written proof.**
The orientation is pinned by two `#check`s:
```
EulerMeanSolenoidal.translation_ae : ↑↑((EulerMeanSolenoidal.translation a) u) =ᵐ[volume] fun x => ↑↑u (x + a)
SchwartzMap.lineDerivOp_apply_eq_fderiv : (∂_{m} f) x = (fderiv ℝ (⇑f) x) m
```
so `translation a u = u(·+a)` and `∂_{eⱼ}ψ` is the honest directional derivative — hence `w = +∂ⱼz`
and `∫ψ·∂ⱼz = ∫(−∂ⱼψ)·z` is the textbook identity, with the minus on `ψ`.  Verified *on a concrete
smooth field, twice*, in `/tmp/rev140/fidelity.lean` (EXIT=0):

```lean
/-- Route A: from lane 140's E2. -/
theorem sign_test_from_E2 (u : EulerMeanSolenoidal.L2) (hu : SmoothOrbit u) (j i : Fin 3)
    (ψ : SchwartzMap Space ℂ) :
    ∫ x, ψ x * ((fderiv ℝ (representative u hu) x (coordinateVector j) i : ℝ) : ℂ)
      = ∫ x, (-∂_{coordinateVector j} ψ) x * ((representative u hu x i : ℝ) : ℂ) := by
  have hE2 := weakDeriv_pairing_of_translation_hasDerivAt j
    (orbitDerivative_hasDerivAt u hu (coordinateVector j)) i ψ
  …                                    -- rewrite by `orbitDerivative_ae_fderiv` and `representative_ae`

/-- Route B: from lane 132's independently written smooth-case pairing. -/
theorem sign_test_from_D01 … :  (same statement) :=
  smoothField_weakDeriv_pairing (EulerMeanSmoothRepresentative.smoothL2Field u hu) j i ψ
```
Both routes prove the **same** statement.  Lane 132's `weakDerivs_smooth` uses
`w = Z.directionalField (coordinateVector j)`, and
`LpSmoothFieldAlgebra.directionalField_field : (directionalField A v).field x = fderiv ℝ A.field x v := rfl`
— the honest `+∂ⱼ`.  Vendor's `MeanSpatialDerivative.orbitDerivative_ae_fderiv` says
`⇑(orbitDerivative u v) =ᵐ fun x => fderiv ℝ (representative u hu) x v`, also `+`.  A sign slip in E2
would make route A produce `+∂ⱼψ` on the right and the two routes would disagree; they don't.

**F5 (PASS) — negative check: the `HasDerivAt` hypothesis is load-bearing.**
`/tmp/rev140/fidelity.lean`, EXIT=0 (with `set_option autoImplicit false in`, per LESSONS 2026-09-14
on autoImplicit re-binding deleted hypotheses):
```lean
set_option autoImplicit false in
theorem E2_hypothesis_is_load_bearing
    (H : ∀ (j : Fin 3) (z w : EulerMeanSolenoidal.L2) (i : Fin 3) (ψ : SchwartzMap Space ℂ),
      ∫ x, ψ x * ((w x i : ℝ) : ℂ) = ∫ x, (-∂_{coordinateVector j} ψ) x * ((z x i : ℝ) : ℂ)) :
    ∀ (w : EulerMeanSolenoidal.L2) (i : Fin 3) (ψ : SchwartzMap Space ℂ),
      ∫ x, ψ x * ((w x i : ℝ) : ℂ) = 0 := …   -- instantiate z := 0
```
Dropping the hypothesis collapses the statement: **every** `L²` field would pair to zero against
**every** Schwartz test function (which forces every `L²` field to vanish weakly).  So the conclusion
is not derivable without the hypothesis, and E2 is not a disguised tautology.

### (b) `exists_isSobolevDatum_m_of_cylinder` — order budget and what it consumes

```
@…exists_isSobolevDatum_m_of_cylinder : ∀ {q : ℕ} (u : ↥(EulerCylinderSobolevSpace.SobolevSpace 1 (q + 1))),
  (∀ (θ : AddCircle 1), (EulerCylinderSobolevSpace.sobolevTranslation 1 (q + 1) (0, θ)) u = u) →
    ∀ (U : ↥EulerMeanSolenoidal.L2), EulerMeanOrdinaryLift.ordinaryLift U = EulerCylinderSobolevSpace.value 1 u →
        ∀ (m : ℕ), m + 3 ≤ q + 1 → ∃ A, NSFormalization.Section4.D01.IsSobolevDatum (↑m) (↑↑U) A
```
* **The budget is forced, not chosen.**  `exists_descend` needs `n + 3 ≤ q` (the three orders
  `exists_ordinary_value` costs); `hasWeakDerivsL2_of_word` threads it as `n + m + 3 ≤ q`; the top level
  enters at `n = 0` on an array of order `q + 1`, giving exactly `m + 3 ≤ q + 1`, i.e. `m ≤ q − 2`.
  Checked at the boundary (`/tmp/rev140/instantiate.lean`): `4 + 3 ≤ 6 + 1` holds, `5 + 3 ≤ 6 + 1` does not,
  so at `exists_local`'s minimal `q = 6` the top order is `m = 4`.
* **Hypotheses consumed = clause 7 and clause 4 only.**  The angle-invariance hypothesis is
  `exists_local`'s clause 7 verbatim, `hU` is clause 4 verbatim.  Nothing else is assumed — note that
  `EulerPairing.lean` does **not** import `Source.OrdinaryForcedLocal` at all, so it cannot be smuggling
  anything from it; the theorem is stated against the clause shapes.
* **`T` depends on `q`.**  `exists_local {q} (hq : 6 ≤ q)` produces `T` *after* `q` is fixed, so this is
  "each finite order `m ≤ q − 2` on its own horizon `T(q)`", not "all orders on one horizon".  The
  module header and ATTEMPTS both record this; I confirm it from `OrdinaryForcedLocal.lean:32`
  (`∃ (T : ℝ) (hT : 0 < T) (hTS : T ≤ S), …` inside the `{q}`-binder).

### (c) / (d) Non-vacuity — PASS, on the real `exists_local` output

`euler_pairing_nonvacuous` (the lane's own record, on a `SmoothOrbit` field) compiles with standard
axioms.  I went further and instantiated the datum theorem on `exists_local` itself
(`/tmp/rev140/instantiate.lean`, EXIT=0, `[propext, Classical.choice, Quot.sound]`):

```lean
theorem datum_on_exists_local {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ} (hν : 0 < ν) (hS : 0 < S)
    (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space) (hF : ∀ n, Continuous (fun t => (F t).jetLp n)) :
    ∃ (T : ℝ) (hT : 0 < T), T ≤ S ∧
      ∃ U : C(Icc (0 : ℝ) T, EulerMeanSolenoidal.L2), U ⟨0, le_rfl, hT.le⟩ = a.toLp ∧
        ∀ (m : ℕ), m + 3 ≤ q + 1 → ∀ t : Icc (0 : ℝ) T,
          ∃ A : RealVectorSobolev (m : ℝ), IsSobolevDatum (m : ℝ) (⇑(U t)) A := by
  obtain ⟨T, hT, hTS, u, U, _hu, _hi, hU0, h4, _h5, _h6, h7⟩ :=
    NSFormalization.Source.OrdinaryForcedLocal.exists_local hq hν hS a ha F hF
  exact ⟨T, hT, hTS, U, hU0, fun m hm t =>
    exists_isSobolevDatum_m_of_cylinder (u t) (fun θ => h7 θ t) (U t) (h4 t) m hm⟩
```
This is the row the lane claims, wired end to end with nothing left over.  (I used a general `a`/`F`
rather than zero data — strictly stronger, and it avoids needing a zero `SmoothL2Field` witness.)

---

## 3. Consistency

### F6 (INFO) — imports are minimal and correct
`EulerPairing.lean` imports `D01.FiniteOrderConstructor`, `A01.CarrierBridge`, `Euler.LpSmoothApproximation`,
`Euler.MeanSolenoidalTranslation`, `Euler.MeanOrdinaryLift`, `Euler.CylinderSobolevSpace`,
`Source.OrdinaryCylinderDescent`.  **No A04 import** (checked); no `Source.OrdinaryForcedLocal`.
The only `def` in the module is `complexComponentCLM` — **no vendor definition is restated**, so the
"local restatement" policy is not touched.  `make check` green.

### F7 (LOW, MAINT) — `complexComponentCLM` is a verbatim duplicate of lane 124's `componentCLM`
```lean
-- lane 124, Section4/A01/DatumPathContinuity.lean:80
def componentCLM (i : Fin 3) : EulerMeanSolenoidal.L2 →L[ℝ] Lp ℂ 2 (volume : Measure Space) :=
  (Complex.ofRealCLM.comp (EuclideanSpace.proj i)).compLpL 2 volume
-- lane 140, Section4/A01/EulerPairing.lean:69
def complexComponentCLM (i : Fin 3) : EulerMeanSolenoidal.L2 →L[ℝ] Lp ℂ 2 (volume : Measure Space) :=
  ContinuousLinearMap.compLpL 2 (volume : Measure Space) (Complex.ofRealCLM.comp (EuclideanSpace.proj i))
```
Same term, only dot-notation vs. explicit application.  Confirmed in `/tmp/rev140/deadends.lean` (EXIT
on this line: clean):
```lean
example (i : Fin 3) : complexComponentCLM i = componentCLM i := rfl
```
Both live in namespace `NSFormalization.Section4.A01`, in modules that do not import each other, so
there is no ambiguity today (different names) — but a future module importing both gets two names for
one object.  **MAINT item**, not a blocker: drop `complexComponentCLM`, import `DatumPathContinuity`
(or lift `componentCLM` into `CarrierBridge`) and reuse — `coeFn_complexComponentCLM` then duplicates
nothing either, since lane 124 already has `componentLp_eq_compLpL`.  Do NOT fix inside this lane; it
would drag `DatumPathContinuity`'s closure into `EulerPairing`.

### F8 (INFO) — `exists_isSobolevDatum_m_of_ae` does **not** duplicate `datumPath_isSobolevDatum`
Lane 124's `datumPath_isSobolevDatum` is order **0**, bundles `ContinuousOn (datumPath U) (Ico 0 T)`,
and takes the spacetime velocity `v : ℝ × Space → Space` with a per-time a.e. hypothesis.  Lane 140's
is order **m**, pointwise in `t`, no continuity, plain `v : Space → Space`.  The shared move is the
single `IsSobolevDatum.congr_field` line in each.  Not worth deduplicating; note it so the two are not
confused when B1 lands.

### F9 (INFO) — CI closure
`EulerPairing` is imported by nothing under `verification/`, so `make test` (`lake -d verification test`)
does **not** build it.  CI does: `experiments/build_changed_lean.py` maps any changed
`formalization/**.lean` to a module name and runs `lake build` on it (verified by reading the script —
prefix list `['verification/', 'formalization/', 'vendor/NavierStokesAndEuler/']`).  So this PR is
covered; after merge the module is only rebuilt when it or its imports change, which is the normal
state for a research module not yet wired to a contract.  Nothing to do now.

---

## 4. Honesty of `ATTEMPTS_EULER_PAIRING.md` — PASS, both dead ends reproduce verbatim

**Dead end 1** — "`RCLike.inner_apply` gives `inner ℂ a b = b * conj a` (conj on the *first* slot,
product flipped)".  `/tmp/rev140/deadends.lean`:
```
@RCLike.inner_apply : ∀ {𝕜} [RCLike 𝕜] (x y : 𝕜), inner 𝕜 x y = y * (starRingEnd 𝕜) x
/tmp/rev140/deadends.lean:16:49: error: unsolved goals
a b : ℂ
⊢ b * (starRingEnd ℂ) a = a * b
```
Exactly as recorded; the `starRingEnd_apply, star_star` + `ring` cleanup in the proof is necessary.

**Dead end 2** — "`integral_add_right_eq_self` leaves `μ` a metavar (`IsAddRightInvariant ?m` stuck) —
pass `(μ := (volume : Measure Space))`".  Reproduced in the lane's actual *forward* shape (a bare
`have` with no expected type), `/tmp/rev140/deadend2.lean`, EXIT=1:
```
/tmp/rev140/deadend2.lean:6:14: error: typeclass instance problem is stuck
  Measure.IsAddRightInvariant ?m.8
```
Refinement worth recording: the metavariable only bites in forward reasoning.  With an expected type
(`exact integral_add_right_eq_self f a` against a stated goal) it elaborates fine.  The lane uses
`have key := …`, so the explicit `(μ := …)` is genuinely needed there.

Spot-check of the recipe: the lane implements `research/D01/REVIEW_FINITE_ORDER_CLOSE.md` §6 as
written — E2's signature at review lines 307–308 is the lane's theorem verbatim, and the proof takes
the review's own "cheaper route" (line 336: pair through CLMs and differentiate `ψ`'s smooth `L²`
orbit, no cutoff/DCT).  The review's one open worry for E1 — an induction for the angle-invariance of
`ofJet J` — is genuinely sidestepped by `value_injective` as ATTEMPTS claims (`exists_descend:301-305`).

---

## 5. For the lead — what remains after C1b-m-E

### (i) Row **c8** (`ClassicalSolutionR.sobolev`, continuity of the order-`m` datum path) — **unchanged in kind, but strictly reduced**

Lane 140 delivers *existence* of the order-`m` datum at each `t`, not continuity in `t`, and it goes
through lane 125's `isSobolevDatum_raise`, whose `raiseHilbert` (multiplication by `(1+‖ξ‖²)^{1/2}`)
is **unbounded** on `L²` — so there is still no continuous linear operator to bundle, exactly as
`C1B_SPLIT.md` row C1b-c8-m already says.  What *is* new and worth recording:

* **The datum path is now well-defined and canonical.**  Existence at every `t` (F-(d) above) plus
  `D01/ForceClass.lean:286 isSobolevDatum_unique` means "the" order-`m` datum is a genuine function
  of `t` on `Icc 0 T(q)`.  Before this lane one could not even write down the path at `m ≥ 1`; c8-m
  was "does it exist, and is it continuous".  It is now purely **"is the canonical path continuous"**.
* **The remaining obligation is unchanged and still B1/T1-strength**: `continuous_vectorSobolevDatum`
  (`Source/PhysicalIntegerSobolev.lean:61`) wants `∀ j, Continuous (fun t => (A t).jetLp j)` — all `L²`
  jets of the *velocity* path continuous in time.  `exists_local` supplies this only for the force path
  (`OrdinaryForcedLocal.lean:35`), never for `U` (`:38` is a bare `C(Icc 0 T, EulerMeanSolenoidal.L2)`).
  Nothing in lane 140 produces it.
* **Size: M–L, unchanged**, and the cheapest route is still the `smoothAngularDatum` one (all factors
  CLM/CLE, lowering only — it inherits lane 124's order-0 argument wholesale), gated on the velocity
  path being `SmoothL2Field`-valued with continuous jets.  That is a B1/T1 deliverable, not an A01 one.
  Do **not** try to make lane 132's constructor continuous: the raise step is not a bounded operator,
  so it would need hand-made uniform-in-`t` domination.
* One genuinely cheap follow-on now unblocked (**S**): the order-`m` analogue of
  `datumPath_isSobolevDatum`'s *transport* half is already done — `exists_isSobolevDatum_m_of_ae`
  is one `exact` away from the velocity field the moment B1 supplies `velocity t =ᵐ ⇑(U t)`.

### (ii) Row **A3-L1·k** (the order-2 cap) — **the vacuity warning is LIFTED; the comparison is now a real M with a clear route**

The warning was real, and I reproduced it.  `sobolevENorm s z = ⨅ A : {A // IsSobolevDatum s z A}, ‖A.1‖ₑ`
(`Contracts/V1/Data.lean:189`), so with no datum the infimum is over an empty type
(`/tmp/rev140/a3cap2.lean`, EXIT=0, standard axioms):
```lean
theorem trap_enorm (s : ℝ) (z : Space → Space)
    (hempty : IsEmpty {A : RealVectorSobolev s // IsSobolevDatum s z A}) : sobolevENorm s z = ⊤ := by
  simp only [sobolevENorm, iInf_of_isEmpty, sInf_empty]

theorem trap_normAt (s : ℝ) (u : SpaceTimeField) (t : ℝ)
    (hempty : IsEmpty {A : RealVectorSobolev s // IsSobolevDatum s (fun x : Space => u (t, x)) A}) :
    sobolevNormAt s u t = 0 := by
  simp only [sobolevNormAt, trap_enorm s _ hempty, ENNReal.toReal_top]
```
i.e. **no datum ⟹ `sobolevNormAt = 0`**, and `sobolevNormAt 2 (⇑(U t)) ≤ c·‖u t‖` was vacuously true —
the classic ⊤-trap of LESSONS.  Lane 140 closes it, same probe, EXIT=0, standard axioms:
```lean
theorem sobolevENorm_two_finite {q : ℕ} (u : SobolevSpace 1 (q + 1)) (hu : …angle-invariance…)
    (U : EulerMeanSolenoidal.L2) (hU : ordinaryLift U = value 1 u) (hq : 4 ≤ q) :
    sobolevENorm (2 : ℝ) (⇑U) ≠ ⊤ := by
  obtain ⟨A, hA⟩ := exists_isSobolevDatum_m_of_cylinder u hu U hU 2 (by omega)
  rw [show ((2 : ℕ) : ℝ) = (2 : ℝ) by norm_num] at hA      -- cf. LESSONS on the ℕ→ℝ cast
  rw [sobolevENorm_eq hA]; exact enorm_ne_top

theorem sobolevNormAt_two_eq … : ∃ A : RealVectorSobolev (2:ℝ), IsSobolevDatum (2:ℝ) (⇑U) A ∧
      sobolevNormAt 2 v t = ‖A‖ := …
```
Order 2 needs `2 + 3 ≤ q + 1`, i.e. `q ≥ 4`, and `exists_local` gives `q ≥ 6` — comfortably inside.
So for every `t ∈ Icc 0 T(q)`: **`sobolevNormAt 2` of the velocity slice is the honest `‖A‖` of the
constructed datum, not junk `0`.**  `A3_SPLIT.md` rows 70 and 118–126 should be updated: the
"additionally gated by C1b-m-D" clause is discharged.

**Is the comparison `sobolevNormAt 2 (⇑(U t)) ≤ c·‖u t‖_{SobolevSpace 1 (q+1)}` now an M with a clear
route?  Yes — M, with one genuinely missing piece.**  By `A04/Forcing.lean:126 sobolevENorm_eq` the
target is exactly `‖A‖ ≤ c·‖u t‖` for the constructed `A`.  Two of the three ingredients are free
(`/tmp/rev140/wordnorm3.lean`, EXIT=0):
```lean
-- the array-coordinate bound: SobolevSpace is a submodule of `SobolevWord q → LiftL2 1` with the Pi norm
example {q n : ℕ} (u : SobolevSpace 1 q) (hn : n ≤ q) (w : Fin n → Fin 4) :
    ‖word 1 u hn w‖ ≤ ‖u‖ := norm_le_pi_norm u.val _
-- and the descent is an isometry
example (Zw : EulerMeanSolenoidal.L2) : ‖ordinaryLift Zw‖ = ‖Zw‖ := ordinaryLift.norm_map Zw
```
so every descended derivative word satisfies `‖Zw‖ ≤ ‖u t‖`, and `exists_local`'s `‖u‖ ≤ ‖u₀‖ + 1`
then caps all of them uniformly in `t`.  **The missing piece is the third ingredient: a *quantitative*
version of `exists_isSobolevDatum_of_memLp_derivs`** — today it is purely existential and tracks no
norm, so `‖A‖` is not related to the `‖Zw‖`'s at all.  Concretely one needs the Plancherel-side
estimate `‖A‖² ≤ c_m · Σ_{|α| ≤ m} ‖∂^α z‖²_{L²}` along the induction (order-0 seed `orderZeroDatum`,
then `isSobolevDatum_raise`), which is the "`m`-dependent-constant norm comparison" that 119
explicitly disclaimed (F7) and that nobody has written.  **Size: M (~120–200 lines)**, one new lane,
no external input needed, and it is now the *only* thing between `exists_local` and `Kbnd`.  Suggest a
row `A3-L1·k-quant` ("norm-tracking finite-order datum constructor") with D01 as owner, since all the
machinery it touches is `FiniteOrderConstructor`/`FiniteOrderDatum`.

---

## Commands run (all from the worktree, after `. scripts/lean-env.sh`, `lake` from `verification/`)

| command | result |
|---|---|
| `lake build …D01.FiniteOrderConstructor …Source.OrdinaryForcedLocal …A01.EulerPairing` | EXIT=0, "Build completed successfully (9952 jobs)" |
| `lake env lean ../formalization/NSFormalization/Section4/A01/EulerPairing.lean` | EXIT=0, silent (0 bytes) |
| `lake env lean ../research/A01/axioms_euler_pairing.lean` | EXIT=0, 12 × standard 3 axioms |
| `make check` | EXIT=0 (13 policy tests OK; 30 work items consistent) |
| `lake env lean /tmp/rev140/EP250.lean` (250000) | EXIT=0, 7.53 s |
| `lake env lean /tmp/rev140/EP_default.lean` (200000) | EXIT=1, `timeout at whnf` at line 91 |
| `lake env lean /tmp/rev140/check1.lean` (`#check` ×11, `pp.fullNames`) | all as expected |
| `lake env lean /tmp/rev140/fidelity.lean` (F1/F2 shape, sign ×2, negative) | EXIT=0 |
| `lake env lean /tmp/rev140/instantiate.lean` (`datum_on_exists_local`) | EXIT=0, standard axioms |
| `lake env lean /tmp/rev140/deadends.lean` / `deadend2.lean` | both dead ends reproduced verbatim |
| `lake env lean /tmp/rev140/a3cap2.lean` (⊤-trap + its lifting) | EXIT=0, 3 × standard axioms |
| `lake env lean /tmp/rev140/wordnorm3.lean` (coordinate bound) | EXIT=0 |
