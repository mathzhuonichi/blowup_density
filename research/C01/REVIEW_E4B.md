# REVIEW — lane 148-C01-e4b-pressure-jets (row E4b: the `hB` clause of E4)

Reviewer run 2026-09-14, worktree `.claude/worktrees/148-C01-e4b-pressure-jets`, branch
`erenup/148-C01-e4b-pressure-jets`, HEAD `341a01b`.  Read-only: no Lean edited, no git state
touched.  Probes (new): `research/C01/probes/rev148_mutation.lean`,
`research/C01/probes/rev148_leray_hcs.lean`, `research/C01/probes/rev148_nonvacuity.lean`.

## Verdict: **ACCEPT-WITH-NOTES**

Both target statements are token-equivalent to the ones review 146 prescribed, every cited
declaration exists with the cited hypotheses, all 12 declarations carry exactly the standard
three axioms, the module emits zero warnings, and four mutations break (one inconclusive by
timeout, replaced by an equivalent check).  **The N2 correction is right**: there is no
order-1 hole — `D01.isSobolevDatum_sub` genuinely has no order restriction.  Four notes,
none blocking.

---

## 1. What the lane claims

Row **E4b** of `research/C01/ENERGY_SPLIT.md`: on a compact window `[c,S] ⊂ (0,T)`
(`0 < c ≤ S < T`) of a classical solution `w : ClassicalSolutionR ν a f T` with
`hf : MemForceR f`, the `L²` jets of `∇p(t,·)` and of `∂ₜu(t,·)` are continuous in time —
the `hB` hypothesis of the vendor's `EulerOrdinarySobolev.wordEnergy_hasDerivWithinAt`.  The
route is lane 146's momentum-residual path → lane 145's quantitative datum constructor →
`Leray.lerayComplement` → `jetOfDatum`.  Secondary claims: glue (a) rewritten in jet language,
the order-1 hole flagged as N2 in review 146 does not exist, and N3's closed-window design is
discharged at the path level.

## 2. What is in Lean

`formalization/NSFormalization/Section4/C01/PressureJetPath.lean`, 312 lines, namespace
`NSFormalization.Section4.C01`, 12 declarations, 3 imports (`…C01.JetPaths`,
`…D01.FiniteOrderNorm`, `Euler.OrdinaryAdvectionLimit` — the last one is where
`jetLp_fieldSub` lives, `OrdinaryAdvectionLimit.lean:17`).

### 2.1 Target statements — PASS, token-equivalent to review 146

Review 146 ("The exact E4b statement the next lane must prove") wrote

```lean
theorem pressureGradientPath_jetLp_continuous
    (w : ClassicalSolutionR ν a f T) (hf : MemForceR f) (hc : 0 < c) (hcS : c ≤ S)
    (hST : S < T) (n : ℕ) :
    Continuous (fun t : Icc c S =>
      (pressureGradientField w hf (show t.1 ∈ Ioo (0:ℝ) T from
        ⟨lt_of_lt_of_le hc t.2.1, lt_of_le_of_lt t.2.2 hST⟩)).jetLp n)
```

The lane's (`PressureJetPath.lean:237-241`) has the identical binder list in the identical
order and the identical body, with the membership proof factored out as
`mem_Ioo_of_mem_Icc (hc : 0 < c) (hST : S < T) {t} (ht : t ∈ Icc c S) : t ∈ Ioo (0:ℝ) T :=
⟨lt_of_lt_of_le hc ht.1, lt_of_le_of_lt ht.2 hST⟩` (`:223-225`) — character-for-character the
same proof term that review 146 inlined (proof-irrelevant anyway, the slot is a `Prop`).
`temporalSlicePath_jetLp_continuous` (`:287-291`) likewise.  Review 146's prose said
"`0 < c`, `c < S`"; the lane uses the *weaker* `hcS : c ≤ S` that review 146's code block
actually wrote, so the statement is if anything more general.

`pressureGradientField` (`MomentumCarrierB.lean:107-111`) and `temporalSliceField`
(`:119-123`) are lane 143's, both `SmoothL2Field Space` with `ht : t ∈ Ioo (0:ℝ) T` and
`smooth`/`integrable` taken from D01 P2
(`pressureGradient_slice_smoothSquareIntegrableJets_of_memForceR`,
`temporalDerivative_slice_smoothSquareIntegrableJets_of_memForceR`).  `hf : MemForceR f` is
`A02.MemForceR` as `open`ed at `:69`; the membership proofs fed to them are the real ones
(not `Classical.choice` placeholders) — they are built from `hc`/`hST`/`t.2` only.

### 2.2 Glue (a) — PASS; it really produces lane 145's predicate

`D01.HasWeakDerivsL2Bound` (`FiniteOrderNorm.lean:352-359`) is

```
| 0     => MemLp z 2 volume ∧ (eLpNorm z 2 volume).toReal ^ 2 ≤ M
| m + 1 => (… order-0 clause …) ∧ ∀ j : Fin 3, ∃ w, HasWeakDerivsL2Bound w M m ∧
             (∀ i ψ, ∫ ψ·w_i = ∫ (-∂_{coordinateVector j} ψ)·z_i)
```

(the definition quantifies over the *existence* of a weak-derivative field; the coordinate
`directionalField` is what the lane — like 145's own `exists_hasWeakDerivsL2Bound_smooth`
(`:444-459`) — supplies as the witness).  `hasWeakDerivsL2Bound_of_jetLp_sq_le`
(`PressureJetPath.lean:119-142`) builds exactly that shape:
`⟨⟨Z.memLp, _⟩, fun j => ⟨(Z.directionalField (coordinateVector j)).field, _,
fun i ψ => D01.smoothField_weakDeriv_pairing Z j i ψ⟩⟩`, with the pairing leg *verbatim* the
one 145 uses (`FiniteOrderConstructor.lean:306-309`, statement checked: it is the pairing of
`(Z.directionalField (coordinateVector j)).field` against `ψ` versus `Z.field` against
`-∂_{coordinateVector j} ψ`).  The improvement over 145 is real: 145's non-vacuity lemma
produces `M` as a `max` chosen after the field, whereas here `M` is carried *unchanged* down
the recursion, which is what makes it vanish along a path.

The three supporting vendor lemmas exist with the stated hypotheses:

* `jetPostcompose L n = compContinuousMultilinearMapL ℝ (fun _ => Space) V W L`
  (`Euler/LpSmoothFieldAlgebra.lean:20-22`); `norm_jetPostcompose_le` is
  `opNorm_le_bound` + `ContinuousLinearMap.norm_compContinuousMultilinearMap_le`.
* `jetLp_mapField (L) (A) (n) : (mapField L A).jetLp n = (jetPostcompose L n).compLpL 2 volume
  (A.jetLp n)` (`:39-45`) — used with `ContinuousLinearMap.norm_compLpL_le`.
* `directionalField A v = mapField (ContinuousLinearMap.apply ℝ V v) A.derivative` (`:94-95`),
  so the first `calc` step of `norm_directionalField_jetLp_le` (`:104-105`) is honestly `rfl`;
  `norm_derivative_jetLp : ‖A.derivative.jetLp n‖ = ‖A.jetLp (n+1)‖`
  (`Euler/LpSmoothField.lean:94-98`); `norm_jetLp_zero : ‖A.jetLp 0‖ = ‖A.toLp‖` (`:89-92`).

### 2.3 Item 2 — PASS, and the order-1 hole genuinely does not exist

I opened both `isSobolevDatum_sub` lemmas side by side.

```lean
-- A03/VectorTameProduct.lean:186  (the one review 146 N2 looked at)
theorem isSobolevDatum_sub {s : ℝ} (hs : 2 ≤ s) {F G : Space → Space}
    (hF : LocIntField F) (hG : LocIntField G) {A B : RealVectorSobolev s}
    (hA : IsSobolevDatum s F A) (hB : IsSobolevDatum s G B) :
    IsSobolevDatum s (fun x => F x - G x) (A - B)

-- D01/OrderZeroAlgebra.lean:51  (the one the lane uses)
theorem isSobolevDatum_sub {A B : RealVectorSobolev s}
    (hz : SchwartzPairable z) (hw : SchwartzPairable w)
    (hA : IsSobolevDatum s z A) (hB : IsSobolevDatum s w B) :
    IsSobolevDatum s (z - w) (A - B)
```

The D01 version sits under `variable {s : ℝ}` with **no** `hs` of any kind and no
`LocIntField`: the order is a free real, so order 1 (and every other order) is covered.
The module name is misleading — it is filed under "order-zero algebra" because that is the
consumer that motivated it, but nothing in the statement or the proof (`map_sub` on
`angularRealization`, `integral_sub (hz i ψ) (hw i ψ)`) is order-specific.  **Claim verified;
review 146's N2 "order 1 is an uncovered hole" is withdrawn.**

`SchwartzPairable z` (`D01/ForceClass.lean:207-209`) is `∀ i ψ, Integrable (ψ · z_i)` — also
order-free, so "applies at order `m`" is vacuously true.  Note the pairability is required of
the **two fields separately**, not of the difference: the lane feeds
`D01.schwartzPairable_of_memLp (fun i => D01.memLp_component A.memLp i)` and the same for `B`
(`PressureJetPath.lean:160-161`).  `schwartzPairable_of_memLp` (`ForceClass.lean:213-215`,
Hölder on `SchwartzMap.memLp`) and `memLp_component` (`OrderZeroDatum.lean:67-69`, the
`Complex.ofRealCLM ∘ EuclideanSpace.proj i` pushforward of `MemLp`) both apply to any
`SmoothL2Field` via `SmoothL2Field.memLp`, at any order.  So the lane's route needs neither
`A01.orderZeroDatumCLM` nor a raising construction, and `A01.DatumPathContinuity` is indeed
not imported.

The `16^m` is 145's and enters where claimed: `D01.norm_isSobolevDatum_le_of_memLp_derivs
(m) (z) (M) (h : HasWeakDerivsL2Bound z M m) (A) (hA : IsSobolevDatum (m:ℝ) z A) : ‖A‖^2 ≤
16^m * M` (`FiniteOrderNorm.lean:413-418`), applied to the difference field
`A.field - B.field` and to the difference datum.  `isSobolevDatum_unique` is used **inside**
that 145 lemma (`:416`), not by this lane — the lane does not need it, because 145's lemma
already accepts an arbitrary datum.  The `(fieldSub A B).field = A.field - B.field` transport
(`:170-172`, `fieldSub_field` + `Pi.sub_apply`) is honest.

`smoothAngularDatum_path_continuous` (`:180-201`) is a clean per-point squeeze
(`squeeze_zero_norm` on `√(16^m·∑‖Δjet‖²)`, `tendsto_sub_nhds_zero_iff`); it asks
`hP : ∀ k, Continuous …` at every order (more than the `k ≤ m` it uses — harmless).

### 2.4 Leray + pin + jets — PASS, residual slot token-identical

* `D01.Leray.lerayComplement (s : ℝ) : RealVectorSobolev s →L[ℝ] RealVectorSobolev s`
  (`D01/LerayDatum.lean:255-256`, `mkContinuous 1`) — a genuine CLM, so `.continuous.comp`
  is legitimate.  It is **not** the identity: `lerayComplement s h = h` is not even `rfl`
  (probe, §5 M3′), and `lerayComplement_eq_zero_of_transverse` (`:316-319`) sends
  Fourier-transverse data to `0`.
* `D01.isSobolevDatum_pressureGradient_lerayComplement` lives at
  `formalization/NSFormalization/Section4/D01/PressureJets.lean:91-96`.  Its residual slot is
  `IsSobolevDatum (m:ℝ) (fun x : Space => f (t, x) - advection u.velocity t x
  + ν • spatialLaplacian u.velocity t x) Am`, and `residualPathIcc_field`
  (`PressureJetPath.lean:211-215`) is
  `f (t.1, x) - advection w.velocity t.1 x + ν • spatialLaplacian w.velocity t.1 x` —
  **token-identical modulo `t` ↦ `t.1`**, so the `rwa [hfield] at hd` at `:266` is not
  hiding a convention change.  (Same slot lane 146 matched for `residualPath_field`.)
* `jetOfDatum_continuous (m j) (hj : j ≤ m)` is at `C01/Evolution.lean:147-155` and
  `D01.jetOfDatum_ae {m j} (hj) (hz : ContDiff ℝ ∞ z) (hA : IsSobolevDatum (m:ℝ) z A)` at
  `D01/DatumToJets.lean:202-206`.  The `hkey` block (`:268-277`) is the
  `velocityField_jetLp_continuous` / `forcePath_jetLp_continuous` pattern verbatim
  (`Lp.ext` + `(…).integrable n |>.coeFn_toLp` + `jetOfDatum_ae …|>.symm`), at datum order
  `n` = jet order `n`, so no `n+2` detour.
* **`residualPathIcc` re-indexing is honest** (`:207-220`):
  `residualPathIcc … t = residualPath w hf hST ⟨t.1, ⟨le_trans hc.le t.2.1, t.2.2⟩⟩` — the
  same real number `t.1`, the same lane-146 `residualPath`, with `0 ≤ c ≤ t.1` giving the
  `Icc 0 S` membership; `residualPathIcc_field` is literally `residualPath_field` at the
  injected point, and `residualPathIcc_jetLp_continuous` is 146's continuity composed with
  the continuous inclusion `continuous_subtype_val.subtype_mk`.  No new mathematics, no
  silent widening.

### 2.5 Item 4 (the `hB` clause) — PASS

`temporalSlicePath_jetLp_continuous` (`:287-310`) rewrites the field of `temporalSliceField`
as `(fieldSub residualPathIcc pressureGradientField).field` using
`temporalDerivative_eq_residual_sub_pressureGradient` (`JetPaths.lean:275-283`, which itself
rests on `D01.temporalDerivative_slice_eq`, `D01/Pressure.lean:196`), transports along
`EulerLpSmoothCoefficientProduct.jetLp_congr` (`Euler/LpSmoothCoefficientProduct.lean:93-97`,
hypothesis `h : f.field = g.field`), splits with `jetLp_fieldSub`
(`Euler/OrdinaryAdvectionLimit.lean:17`), and closes with `Continuous.sub`.  The interior
guard `htpos : 0 < t.1` is re-derived from `hc`/`t.2.1`, so the PDE is only used on `Ioo`.

### 2.6 N3 (closed window) — PASS, and the endpoint really is excluded

All E4b paths are indexed by `Icc c S` with `0 < c ≤ S < T`, so `pressureGradientField` /
`temporalSliceField` are only ever evaluated at interior times; `hB` is now available on a
closed window off **both** endpoints, which is what review 146's N3 asked for.  Mutation M2
(§5) confirms the left endpoint is load-bearing: instantiating `c = 0` leaves `⊢ False`.

`set_option linter.unusedVariables false in` at `:227` is the **only** `set_option` in the
module (grep), it is scoped to the single following declaration, and the reason is written
into that declaration's docstring (`:235-236`).  No `maxHeartbeats` anywhere.

## 3. Notes (none blocking)

### N1 (low, cleanliness) — dropping `hcS` from `pressureGradientPath_jetLp_continuous` is strictly better

I re-ran the lane's own proof script with the `hcS` binder deleted
(`research/C01/probes/rev148_leray_hcs.lean`, theorem
`pressureGradientPath_jetLp_continuous_noHcS`): **it compiles unchanged**.  So the
`hcS`-free statement is true, strictly more general, and needs no linter suppression — the
`set_option linter.unusedVariables false in` at `:227` would simply disappear.  Keeping
`hcS` is defensible (it is the interface review 146 prescribed, and the E4 assembly needs
`0 ≤ S − c` anyway), so this is a note, not a fix demand.
*One-line fix, if the follow-up simplifier lane wants it:* delete `(hcS : c ≤ S)` from
`:238` and the `set_option` line at `:227`; `temporalSlicePath_jetLp_continuous` then stops
passing it at `:310` (and may keep its own `hcS`, which is likewise inert).

### N2 (low, non-vacuity strength) — the axioms file's window is a single point

`research/C01/axioms_e4b.lean:41,47` instantiates `Icc (1:ℝ) 1`, a **one-point** index type,
on which `Continuous` holds for type-theoretic reasons regardless of the theorem.  The
examples still witness what a non-vacuity check is for (the binders are satisfiable and
`pressureGradientField` is constructible at a genuine interior time), but they do not
exercise the continuity.  Verified replacement (`research/C01/probes/rev148_nonvacuity.lean`,
compiles silently): window `Icc (1/2 : ℝ) 1 ⊂ (0,2)` on the same `A04.zeroSol 1 2`, at jet
orders `0` and `2`.
*One-line fix:* `Icc (1 : ℝ) 1` → `Icc (1/2 : ℝ) 1` in both examples (the four `by norm_num`
side goals still discharge).

### N3 (low, record accuracy) — the ATTEMPTS "exact target" for E4 has the vendor value already simplified

`research/C01/ATTEMPTS_E4B.md` writes the E4 target's derivative value as
`2·⟪(A t).toLp, (B t).toLp⟫_ℝ`.  What `wordEnergy_hasDerivWithinAt` literally produces
(`Euler/OrdinaryWordTime.lean:86-89`) is

```
2*(∑ n ∈ range (s+1), ∑ w : Fin n → Fin 3, ⟪(wordField (A t) w).toLp,(wordField (B t) w).toLp⟫_ℝ)
```

At `s = 0` this collapses to `2·⟪(A t).toLp,(B t).toLp⟫_ℝ` only after the empty-word bridge
(`wordField_zero : wordField A (w : Fin 0 → Fin 3) = A := rfl`,
`OrdinarySmoothWords.lean:35-36`, plus `Fintype.card (Fin 0 → Fin 3) = 1`), and the same
bridge is needed on the left to turn `wordEnergy 0 X` (`:94-95`) into `‖X.toLp‖²`.  There is
**no `wordEnergy_zero` simp lemma in the vendor** (grep of `OrdinarySmoothWords.lean`: only
`wordEnergy`, `wordEnergy_nonneg`, `norm_toLp_sq_le_wordEnergy`, `wordBound_sqrt`), so this
is a real, if small, obligation.  Fold it into the E4 list as item 4 below.

### N4 (low, record accuracy) — the pointwise `hd` is not exported anywhere

ATTEMPTS item 2 says `hd` comes "from `velocity_smooth`".  True, but the only existing copy
of that argument is **inline inside** `A04.timeDeriv_isSobolevDatum`
(`Section4/A04/TimeDerivative.lean:182-206`, the `hvelx` block), a theorem that carries
`hm : 2 ≤ m` and `hGc : ContDiffOn ℝ ∞ G (Ico 0 T)` — neither is available from
`ClassicalSolutionR` (its `sobolev` field gives only `ContinuousOn G`).  So the next lane
must re-prove the 7-line `hvelx` (unconditional:
`w.velocity_smooth.comp (contDiff_id.prodMk contDiff_const).contDiffOn hsub` →
`.differentiableOn … (Ico_mem_nhds ht.1 ht.2) |>.hasDerivAt`), or lift it out of
`timeDeriv_isSobolevDatum` first.  Helpful fact: `temporalDerivative u t x =
deriv (fun s => u (s,x)) t` is `rfl` (`ProblemStatement.lean:55-56` vs `deriv f x = fderiv ℝ f x 1`).

## 4. Gaps — what E4 still owes, with the exact assembly statement

The lane's three-item list is right in substance; it is missing N3's word-bridge and the
`velocityField`/`velocitySliceField` identification, and understates N4.  Complete list, in
the vendor's variable order (`OrdinaryWordTime.lean:69-75`:
`(T) (hT : 0 ≤ T) (A B : Icc 0 T → SmoothL2Field Space) (hA) (hB) (hd)`, then `(s) (t)`):

1. **Window translation.**  `T' := S − c`, `hT' : 0 ≤ T'` (from `hcS`), and the continuous
   shift `σ : Icc (0:ℝ) T' → Icc c S`, `σ r := ⟨r.1 + c, _⟩`, composed with
   `Icc c S ↪ Icc 0 S` for the velocity.
2. `hA` = `C01.velocityField_jetLp_continuous w hST` (`Evolution.lean:164`) composed with the
   shift; `hB` = **this lane's** `temporalSlicePath_jetLp_continuous w hf hc hcS hST`
   composed with the shift.
3. `hd` (three sub-steps, cf. N4): (a) pointwise `HasDerivAt (fun s => w.velocity (s,x))
   (temporalDerivative w.velocity s x) s` at interior `s`, re-proved from `velocity_smooth`;
   (b) the `+c` chain rule (`(hasDerivAt_id r).add_const c`, derivative `1`); (c) the
   `projIcc` step — near an interior `r`, `projIcc 0 T' hT' ρ = ⟨ρ,_⟩`, so
   `HasDerivAt.congr_of_eventuallyEq` on `Ioo 0 T' ∈ 𝓝 r`.  `(B ⟨r,…⟩).field x =
   temporalDerivative w.velocity (r+c) x` is `temporalSliceField_field` (`rfl`).
4. **The `s = 0` word bridge** (N3): `wordEnergy 0 X = ‖X.toLp‖²` and
   `∑ n ∈ range 1, ∑ w : Fin n → Fin 3, ⟪…⟫ = ⟪(A t).toLp,(B t).toLp⟫_ℝ`, both via
   `wordField_zero` + the singleton `Fin 0 → Fin 3`.
5. **`HasDerivWithinAt → HasDerivAt`**: `HasDerivWithinAt.hasDerivAt` with
   `Icc_mem_nhds hr.1 hr.2` at `r ∈ Ioo 0 T'`.
6. **Hand-off**: identify `A ⟨r,…⟩` with `MomentumCarrierB.velocitySliceField w _` — both are
   `SmoothL2Field` records with `field = fun x => w.velocity (σ,x)` and `Prop`-valued
   `smooth`/`integrable` (`Euler/LpSmoothField.lean:31-34`), so this should be `rfl`; a
   one-line check the next lane should do first.

**Exact statement the next lane must prove** (the value fact that
`C01.energyIdentity_classical`, `MomentumCarrierB.lean:254-258`, takes as its `hd`
hypothesis — `hd : d = 2 * ⟪(velocitySliceField w _).toLp, (temporalSliceField w hf ht).toLp⟫`):

```lean
/-- E4.  On a window `[c,S] ⊂ (0,T)`, the `L²` energy of the velocity is differentiable in
time at every interior point, with derivative `2⟪u(t,·), ∂ₜu(t,·)⟫`. -/
theorem energyDerivative_hasDerivAt
    (w : ClassicalSolutionR ν a f T) (hf : MemForceR f)
    (hc : 0 < c) (hcS : c ≤ S) (hST : S < T)
    {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) (S - c)) :
    HasDerivAt
      (fun ρ : ℝ =>
        ‖(velocityField w hST
            ⟨(projIcc (0:ℝ) (S - c) (by linarith) ρ).1 + c, by constructor <;> …⟩).toLp‖ ^ 2)
      (2 * ⟪(velocitySliceField w (Ioo_subset_Ico_self
                (mem_Ioo_of_mem_Icc hc hST ⟨by linarith, by linarith⟩))).toLp,
            (temporalSliceField w hf
                (mem_Ioo_of_mem_Icc hc hST ⟨by linarith, by linarith⟩)).toLp⟫_ℝ)
      r
```

(with the two membership proofs at the time `r + c ∈ Icc c S`).  Composed with
`energyIdentity_classical` this discharges the last input of row **energyIdentity**
(`ENERGY_SPLIT.md`), i.e. `d = −2ν·∫∑ᵢ‖∂ᵢu‖² + 2·∫⟪u,f⟫`.

## 5. Commands and results

All from the lane worktree after `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, `lake` only
from `verification/`, one `lake` at a time.

| command | result |
|---|---|
| `lake build NSFormalization.Section4.C01.PressureJetPath` | **exit 0**, `Build completed successfully (10301 jobs)`; 50 `warning:` lines, **0** from `Section4`, **0** mentioning `PressureJetPath` |
| `lake env lean ../formalization/NSFormalization/Section4/C01/PressureJetPath.lean` | **exit 0**, output **0 bytes** |
| `lake env lean ../research/C01/axioms_e4b.lean` | **exit 0**; **12/12** `#print axioms` = `[propext, Classical.choice, Quot.sound]`; both `A04.zeroSol` `example`s elaborate silently |
| `grep -nE 'sorry\|admit\|native_decide\|maxHeartbeats\|^[[:space:]]*axiom ' PressureJetPath.lean axioms_e4b.lean` | no output (exit 1) |
| `grep -n set_option PressureJetPath.lean` | one line, `:227 set_option linter.unusedVariables false in` |
| `make check` | **exit 0** — plan check (only the known `Paper1/BoundaryCorollary.lean:90` `sorry`), `check_contracts.py` 24 contracts, `test_contract_policy.py` `Ran 13 tests … OK`, `check_work_queue.py` `30 work items: … consistent` |
| `git diff --stat origin/erenup/integration...HEAD` | 4 files, 514 insertions, 2 deletions; no `verification/` or `Contracts/` file touched, so no `scripts/gates.sh` mutation run is owed |
| `lake env lean ../research/C01/probes/rev148_nonvacuity.lean` | **exit 0**, 0 bytes (non-degenerate window `[1/2,1] ⊂ (0,2)` at orders 0 and 2 — N2) |

### Negative checks — `research/C01/probes/rev148_mutation.lean`, `rev148_leray_hcs.lean`

**M1a — `16^m` weakened to `4^m` in `norm_smoothAngularDatum_sub_sq_le`, lane's proof verbatim.**

```
error: Type mismatch
  D01.norm_isSobolevDatum_le_of_memLp_derivs m (A.field - B.field) M hbnd (…) hsub
has type
  ‖D01.smoothAngularDatum m ↑m ⋯ A - D01.smoothAngularDatum m ↑m ⋯ B‖ ^ 2 ≤ 16 ^ m * M
but is expected to have type
  ‖D01.smoothAngularDatum m ↑m ⋯ A - D01.smoothAngularDatum m ↑m ⋯ B‖ ^ 2 ≤ 4 ^ m * M
```

**M1b — hardened (not proof-script fragility): take the *proved* lemma and try to push the
constant down by arithmetic.**

```
error: linarith failed to find a contradiction
h  : ‖…‖ ^ 2 ≤ 16 ^ m * ∑ k ∈ Finset.range (m + 1), ‖A.jetLp k - B.jetLp k‖ ^ 2
hS : 0 ≤ ∑ k ∈ Finset.range (m + 1), ‖A.jetLp k - B.jetLp k‖ ^ 2
a✝ : 4 ^ m * ∑ … < ‖…‖ ^ 2
⊢ False
failed
```

So the `16^m` is genuinely the constant this route yields; it is not arithmetic slack.

**M2 — the window pushed onto the endpoint `c = 0`** (the N3 design point).  Instantiating
`pressureGradientPath_jetLp_continuous` at `c = 0` over `Icc (0:ℝ) S`:

```
rev148_mutation.lean:64:48: error: unsolved goals   …  ⊢ False      -- mem_Ioo_of_mem_Icc's 0 < c
rev148_mutation.lean:65:50: error: unsolved goals   …  ⊢ False      -- the hc slot
rev148_mutation.lean:65:64: error: unsolved goals   …  ⊢ 0 ≤ S      -- the hcS slot
```

The left endpoint is unreachable, exactly as review 146's N3 predicted; the closed interior
window is load-bearing, not decoration.

**M3 — `lerayComplement` replaced by the identity in the pin step: INCONCLUSIVE BY TIMEOUT.**
Asking the elaborator to unify `Leray.lerayComplement (n:ℝ) ?Am` against a non-Leray datum
blows up `whnf` on the `Lp`-multiplier term (`(deterministic) timeout at whnf, maximum number
of heartbeats (1000000)` — the lesson-110 `isDefEq`-on-big-`Lp`-terms failure mode), so the
error is a budget exhaustion, not a rejection.  Replaced by **M3′**, which is decisive and
fast:

```
rev148_leray_hcs.lean:24:81: error: Type mismatch
  rfl
has type ?m.4 = ?m.4
but is expected to have type (D01.Leray.lerayComplement s) h = h
```

i.e. the Leray step is not a definitional no-op; and `lerayComplement_eq_zero_of_transverse`
(`LerayDatum.lean:316-319`) shows it annihilates Fourier-transverse data, so it is not the
identity extensionally either.

**M4 — glue (a) order bookkeeping: order-`m` jet control must not yield an order-`m+1` bound.**

```
error: Application type mismatch: The argument
  h
has type      ∀ k ≤ m, ‖Z.jetLp k‖ ^ 2 ≤ M
but is expected to have type
              ∀ k ≤ m + 1, ‖Z.jetLp k‖ ^ 2 ≤ M
in the application
  C01.hasWeakDerivsL2Bound_of_jetLp_sq_le (m + 1) Z M h
```

**N1 check (expected to SUCCEED)** — the lane's proof with the `hcS` binder deleted compiles:
`rev148_leray_hcs.lean` reports no error for
`pressureGradientPath_jetLp_continuous_noHcS`.

### Citations opened at the cited lines (all confirmed)

`D01/OrderZeroAlgebra.lean:51` · `D01/OrderZeroDatum.lean:67` · `D01/ForceClass.lean:207,213` ·
`D01/FiniteOrderNorm.lean:352,413,444` · `D01/FiniteOrderConstructor.lean:306` ·
`D01/SmoothDatum.lean:260,278` · `D01/LerayDatum.lean:255,281,316` ·
`D01/PressureJets.lean:91,112,126` · `D01/DatumToJets.lean:196,202` · `D01/Pressure.lean:196` ·
`A03/VectorTameProduct.lean:186` · `A02/SolutionClass.lean:79` (`ClassicalSolutionR`) ·
`A04/TimeDerivative.lean:182-206` · `C01/Evolution.lean:115,147,164` ·
`C01/MomentumCarrierB.lean:93,107,119,254` · `C01/JetPaths.lean:243,249,275` ·
`Euler/LpSmoothField.lean:31,89,94` · `Euler/LpSmoothFieldAlgebra.lean:20,39,94` ·
`Euler/LpSmoothCoefficientProduct.lean:93` · `Euler/OrdinaryFieldAlgebra.lean:57` ·
`Euler/OrdinaryAdvectionLimit.lean:17` · `Euler/OrdinarySmoothWords.lean:31,35,94` ·
`Euler/OrdinaryWordTime.lean:69-75,86-89` · `NavierStokes/ProblemStatement.lean:55` ·
`research/C01/REVIEW_JET_PATHS.md` §N2, §N3, "The exact E4b statement".
