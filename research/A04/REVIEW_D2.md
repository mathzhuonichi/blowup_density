# Review (round 2) — lane 056, A04 unit **D2** / G1 sub-lemma SL1

Reviewer run in worktree `.claude/worktrees/056-A04-g1-split`, commit `0017175`
("D2 proved …").  Scope: **only the new/changed material** of that commit —
`formalization/NSFormalization/Section4/A04/TimeDerivative.lean` (new),
the `hlap` weakening in `formalization/NSFormalization/Section4/A04/HighEnergy.lean`,
`research/A04/axioms_g1.lean`, `research/A04/G1_SPLIT.md`, `research/A04/ATTEMPTS_G1.md`.
Round 1 is `research/A04/REVIEW_G1.md` (ACCEPT-WITH-NOTES).

## Verdict

**ACCEPT-WITH-NOTES.**

D2 is genuinely closed.  `timeDeriv_isSobolevDatum` is the real statement, not a
tautology: `IsSobolevDatum` is the *distributional realization* predicate, so the
second conjunct says that the tempered distribution realized by the Hilbert-space
derivative `deriv G t` pairs with every Schwartz `ψ` as `∫ ψ·∂ₜu(t,·)`.  Its two
hypotheses `hGd`/`hGc` are *exactly* the unfolding of `Spec.lean:247`
`HasSmoothSobolevPath` at order `m`, and `energyIdentityHigh`'s `3 ≤ m` covers
the `2 ≤ m` restriction; I checked the plug-in compiles with nothing left over.
The vendor's `temporalDerivative` is `rfl`-equal to the `deriv` used in the
statement, so the momentum-equation consumer needs no bridge lemma.  The proof
route is the one round 1 proposed, and `d2_scalar` is round 1's compiled proof
lifted **verbatim** (all 53 non-blank lines byte-identical).  The `hlap`
weakening leaves both conclusions unchanged and the round-1 sanity instantiation
still holds, tightly.

The two notes are **documentation-only** and neither blocks the merge: a wrong
field name (`ClassicalSolutionR.equation`, which does not exist — the field is
`momentum`) repeated in three places, and a stale `(L, …)` in an SL2 section
heading whose table row now correctly says `M`.

## Findings

### 1. (INFO) Everything mechanical passes

Build rc=0; **no warning originates in either A04 file** (`lake env lean` on each
file alone prints nothing — the 15 warnings in the full build are replayed
`Source/`, `Paper3/` modules); all **six** `#print axioms` are exactly
`[propext, Classical.choice, Quot.sound]`; the forbidden-token grep is clean in
both Lean sources and hits only the docstring word "axiom" and the six
`#print axioms` *commands* in `research/A04/axioms_g1.lean`; `make check` rc=0.
See "Commands and results".

`TimeDerivative.lean` is not imported by `formalization/NSFormalization.lean` —
neither is any other `Section4/*` module (0 of 281 root imports), so this follows
repo convention and is **not** a finding.

### 2. (INFO — confirmed) The D2 statement is the real one

`timeDeriv_isSobolevDatum` (`TimeDerivative.lean:164`) has exactly the requested
shape: `w : ClassicalSolutionR ν a f T`, `{m : ℕ} (hm : 2 ≤ m)`,
`hGd : ∀ t ∈ Ico 0 T, IsSobolevDatum (m:ℝ) (fun x => w.velocity (t,x)) (G t)`,
`hGc : ContDiffOn ℝ ∞ G (Ico 0 T)`, `ht : t ∈ Ioo 0 T`, concluding

```
(∀ x, HasDerivAt (fun r => w.velocity (r,x)) (deriv (fun r => w.velocity (r,x)) t) t)
  ∧ IsSobolevDatum (m:ℝ) (fun x => deriv (fun r => w.velocity (r,x)) t) (deriv G t)
```

**(a) is not vacuous.**  `HasDerivAt f (deriv f t) t` is `DifferentiableAt ℝ f t`
unfolded; it is proved from `w.velocity_smooth` (`A02/SolutionClass.lean:122`)
restricted along `r ↦ (r,x)`, not assumed.

**(b) is not a tautology.**  `IsSobolevDatum` is D01's predicate
(`Section4/D01/SmoothDatum.lean:237`, a verbatim restatement of
`Contracts/V1/Data.lean:160`):

```lean
def IsSobolevDatum (s : ℝ) (z : Space → Space) (A : RealVectorSobolev s) : Prop :=
  ∀ (i : Fin 3) (ψ : SchwartzMap Space ℂ),
    angularRealization s ((A i : FourierData)) ψ = ∫ x, ψ x * ((z x i : ℝ) : ℂ)
```

i.e. the `realization A = field` pairing, quantified over all Schwartz tests.  So
(b) genuinely identifies the tempered distribution realized by the **Hilbert-space**
derivative `deriv G t` with the **pointwise** time-derivative field
`x ↦ ∂ₜu(t,x)`.  It is the non-trivial half; it is where round 1's bounded
representative does all the work.  (`angularRealization` is the honest pairing —
`A03.representative_ae`'s docstring records that local integrability is exactly
what rules out the junk-`0` totalization of `Contracts/V1/Data.lean:148-155`.)

**Hypotheses match the spec exactly.**  `Spec.lean:247`:

```lean
def HasSmoothSobolevPath (T : ℝ) (u : SpaceTimeField) : Prop :=
  ∀ m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
    (∀ t ∈ Ico (0:ℝ) T, IsSobolevDatum (m:ℝ) (fun x => u (t,x)) (G t)) ∧
      ContDiffOn ℝ ∞ G (Ico (0:ℝ) T)
```

— `hGd ∧ hGc` is its body.  I compiled the `energyIdentityHigh`-shaped consumer
(`3 ≤ m`, `obtain ⟨G, hGd, hGc⟩ := hsp m`, `omega` for `2 ≤ m`) with no residual
goal; see scratch (2c) in the command table.

### 3. (INFO — confirmed) `temporalDerivative` is `rfl`-equal to the statement's `deriv`

`NavierStokes.ProblemStatement.temporalDerivative`
(`vendor/NavierStokesAndEuler/NavierStokes/ProblemStatement.lean:55`) is
`fderiv ℝ (fun s => u (s,x)) t 1`, and `deriv f t` is *by definition*
`fderiv ℝ f t 1`.  Both of these compile:

```lean
example (u : VelocityField) (t : ℝ) (x : Space) :
    temporalDerivative u t x = deriv (fun r : ℝ => u (r, x)) t := rfl
example … := by rw [temporalDerivative, deriv]     -- (`fderiv_deriv` does not exist at this pin)
```

Consequently the D2 conclusion restated in the vendor's vocabulary needs **no
glue at all** — this compiles as written:

```lean
example … : IsSobolevDatum (m:ℝ)
      (fun x => temporalDerivative w.velocity t x) (deriv G t) :=
  (timeDeriv_isSobolevDatum w hm hGd hGc ht).2
```

So an A04/C01 consumer can feed `deriv G t` straight into
`ClassicalSolutionR.momentum`'s residual (`navierStokesResidual` is built from
`temporalDerivative`) without a transport lemma.  Scratch deleted.

### 4. (INFO — confirmed) The proof route is the one round 1 proposed, verbatim

`d2_scalar` is round 1's finding-2 proof **lifted byte-for-byte**: I extracted the
```lean fence from `REVIEW_G1.md` and checked every non-blank line (53 of them)
occurs verbatim in `TimeDerivative.lean` — 0 missing (the only edit is dropping
the redundant `noncomputable` on `evalRep`, which is inside a
`noncomputable section`).  The chain is as specified:

* `evalRep` = `BoundedContinuousFunction.evalCLM ℝ x ∘L angularBoundedRepresentative s hs ∘L subtypeL`
  — `Paper3.angularBoundedRepresentative` (`Paper3/AngularTameProduct.lean:141`)
  is a CLM `Lp ℂ 2 →L[ℝ] BoundedContinuousFunction Space ℂ` requiring `2 ≤ s`;
* `hasDerivAt_rep` = `(evalRep …).hasFDerivAt.comp_hasDerivAt t h` ✓;
* `representative_eq` = `A03.representative_ae` (`A03/ScalarTameProduct.lean:156`)
  + `Continuous.ae_eq_iff_eq` ✓;
* imaginary part killed by `(hasDerivAt_const t 0).unique h1` ✓;
* back to the datum by `Paper3.angularRealization_boundedRepresentative`
  (`AngularTameProduct.lean:146`) ✓.

The vector glue is honest: existence from `velocity_smooth` (the real vector
derivative), components via `PiLp.proj … |>.hasFDerivAt.comp_hasDerivAt` and
`A03.isSobolevDatum_iff` (`A03/VectorTameProduct.lean:54`, `Iff.rfl`), and
`(hveli x).deriv` to rewrite `(deriv vec t) i = deriv (component) t`.  No
difference quotients, no dominated convergence, no `isSobolevDatum_smul`, no A01
clause — as claimed.

### 5. (INFO) `2 ≤ m` is harmless for A04; **C01 needs a different route** (note for the C01 lane)

* **A04**: `energyIdentityHigh` (`Spec.lean:427`) quantifies over `3 ≤ m`, so
  `2 ≤ m` is free (`omega`).  Harmless.
* **C01**: works at orders **0** (`L²`, eq:RL2) and **1** (`Ḣ¹`, eq:RH1) —
  `research/C01/COMPARISON.md:172` unit U2 is explicitly "fixed order `m = 0`".
  The `2 ≤ s` is **essential** to this route, not cosmetic: it is the hypothesis
  of `angularBoundedRepresentative`, i.e. the `H^s(R³) ↪ C_b` Sobolev embedding
  (`s > 3/2`).  At `s ∈ {0,1}` a datum has no bounded continuous representative
  and the whole argument is unavailable.  **C01 cannot reuse
  `timeDeriv_isSobolevDatum` as stated.**

  *Suggested bridge, not required by this lane*: prove D2 once at `m = 2` and
  push down by order lowering.  `A03.lowerDatum` (`A03/RealAngularProduct.lean:140`)
  already has `IsScalarSobolevDatum.lower` (`ScalarTameProduct.lean:114`), and
  it is built on `Paper3.angularOrderLowering` (`AngularTameProduct.lean:39`),
  which **is** a CLM — so `deriv (lowerDatum ∘ G) t = lowerDatum (deriv G t)`
  once `lowerDatum` is packaged as a `→L[ℝ]`; datum uniqueness
  (`IsSobolevDatum.unique`, `VectorTameProduct.lean:64`) then identifies C01's
  own order-0/1 path with the lowering of the order-2 one.  The only missing
  piece is the CLM packaging of `lowerDatum` (currently a plain function) and a
  vector analogue of `IsScalarSobolevDatum.lower`.  Worth a line in C01's
  COMPARISON so the C01 lane does not rediscover the `2 ≤ s` wall.

### 6. (INFO) The `hlap` weakening is sound; conclusions unchanged; sanity instantiation still holds

Both conclusions are untouched (they are context lines in the diff):

```
inner_energy_assembly : (1/2)*d + ν*grad^2 ≤ NLbound + fNorm*uNorm
inner_energy_Rhigh    : (1/2)*d + ν*grad^2 ≤ C*u2*uNorm*grad + fNorm*uNorm
```

Only `hlap : ⟪G,L⟫ = -grad^2` → `⟪G,L⟫ ≤ -grad^2` plus the new `hν : 0 ≤ ν`.
`hν` is genuinely needed (multiplying `hlap` by `ν` reverses for `ν < 0`) and is
free at the call site (`energyIdentityHigh` has `0 < ν`).  Round 1's finding-7
instantiation — `N = P = F = 0`, `L = -G`, `grad = ‖G‖`, `C = u2 = fNorm = 0`,
`d = -2ν‖G‖²` — still typechecks against the new signature (`hlap` holds with
equality) and both sides evaluate to `0`, so the bound is still **attained** and
the factor `½` and the dissipation sign are still pinned.  Compiled; scratch
deleted.

One honest caveat on the round-1 argument, not a defect: finding 7 also used
"the lemma has no sign hypothesis on `ν`" to rule out a flipped dissipation sign
at `ν < 0`.  That half of the argument is gone now that `hν : 0 ≤ ν` is present.
The attained-equality at `ν ≥ 0` still does the pinning on its own.

### 7. (MINOR — documentation) `ClassicalSolutionR.equation` does not exist; the field is `momentum`

`A02/SolutionClass.lean:130`:

```lean
  momentum : ∀ t ∈ Ioo (0:ℝ) T, ∀ x : Space,
    NavierStokesR3.ProblemStatement.navierStokesResidual ν velocity pressure t x = f (t, x)
```

There is no `equation` field on `ClassicalSolutionR` (grep: no hits anywhere in
`research/` or `formalization/`).  The name is wrong in **three** places:

* `research/A04/G1_SPLIT.md:45` — SL2 table row, blocker column;
* `research/A04/G1_SPLIT.md:117` — SL2 prose, "the residual equation
  `ClassicalSolutionR.equation`";
* `research/A04/ATTEMPTS_G1.md` — "Frontier" SL2 bullet, "`ClassicalSolutionR.equation`
  (a field, not an A01 clause)".

The *content* claimed is right (the residual field rearranges to
`∂ₜu = νΔu − (u·∇)u − ∇p + f` on `Ioo 0 T`); only the name is wrong, and a
follow-up lane greping for `equation` will find nothing.

**Fix:** `s/ClassicalSolutionR.equation/ClassicalSolutionR.momentum/` in those
three spots, optionally adding the `A02/SolutionClass.lean:130` line reference.
Doc-only; no code change.

### 8. (MINOR — documentation) `G1_SPLIT.md:111` SL2 heading still says `(L, A01/A02)`

The SL2 table row (`:45`) now correctly rates SL2 **M**, and the SL2 prose says
"Now needs only SL1 (done) + … `M`, not L" (`ATTEMPTS_G1.md`).  But the section
heading immediately above that prose still reads

```
### SL2 — momentum equation in datum form (L, A01/A02)
```

**Fix:** heading → `### SL2 — momentum equation in datum form (M, A02 + datum linearity)`
(A01 is no longer an input: the momentum field is A02's).  Doc-only.

### 9. (INFO — optional, for the follow-up lane) Two hypotheses stronger than the proof needs

Neither is wrong — both mirror the spec's own shape — but a general-field version
would be reusable by C01/R43/R44, which want the same statement without a
`ClassicalSolutionR` in hand:

* `hGc : ContDiffOn ℝ ∞ G (Ico 0 T)` is used only through
  `hGc.differentiableOn … |>.differentiableAt (Ico_mem_nhds …) |>.hasDerivAt`, i.e.
  `DifferentiableWithinAt ℝ G (Ico 0 T) t` would do;
* `w : ClassicalSolutionR ν a f T` is used only through `w.velocity_smooth` — the
  lemma is really about a `ContDiffOn ℝ ∞ u (Ico 0 T ×ˢ univ)` field.

`d2_scalar` is already stated at that generality on the scalar side, so the
vector lemma could be too, with the `ClassicalSolutionR` version a one-line
corollary.  Not required for this lane.

### 10. (INFO) Documentation is otherwise accurate

`G1_SPLIT.md` SL1 is now **DONE** with the correct statement quoted (it matches
`TimeDerivative.lean` token for token, including the existence conjunct that
round 1 said was missing); the "L frontier" list at the end of both `G1_SPLIT.md`
and `ATTEMPTS_G1.md` no longer contains SL1; round 1's finding 3 (SL6
`MemHmVector` needs `velocity_smooth`, not `.sobolev` alone) is recorded with the
correct one-liner; `ATTEMPTS_G1.md`'s new "Review fixes" section records the
failed `PiLp.continuousLinearEquiv` sub-approach honestly — and that failure is
consistent with the shipped proof, which routes existence through
`velocity_smooth` and only the components through `PiLp.proj`.  Nothing in the
new material is overclaimed.

## Commands and results

All Lake commands from `WT/verification/` after `. ../scripts/lean-env.sh`,
`LEAN_NUM_THREADS=6`, no `-j`, one lake at a time.

| command | result |
|---|---|
| `bash scripts/lean-install.sh` (from WT root) | `== OK` |
| `lake build NSFormalization.Section4.A04.TimeDerivative NSFormalization.Section4.A04.HighEnergy` | **rc=0**, `Build completed successfully (9891 jobs).`; `grep "Section4/A04\|Section4\.A04"` over the full log → **no match** (no diagnostic from either file) |
| `lake env lean ../formalization/NSFormalization/Section4/A04/TimeDerivative.lean` | **rc=0, no output** |
| `lake env lean ../formalization/NSFormalization/Section4/A04/HighEnergy.lean` | **rc=0, no output** |
| `lake env lean ../research/A04/axioms_g1.lean` | **rc=0**; **6** lines, `inner_energy_assembly`, `inner_energy_Rhigh`, `outerSobolevNormAt_le`, `outerNormAt_le`, `d2_scalar`, `timeDeriv_isSobolevDatum`, each `[propext, Classical.choice, Quot.sound]` |
| `grep -nE "sorry\|admit\|native_decide\|axiom\|maxHeartbeats\|set_option"` on `TimeDerivative.lean` | **no hits** |
| same on `HighEnergy.lean` | **no hits** |
| same on `research/A04/axioms_g1.lean` | 3 docstring hits ("axiom"/"axioms") + the 6 `#print axioms` **commands**; no `axiom` declaration |
| `make check` (WT root) | **rc=0** — plan check, contract check, `Ran 13 tests … OK`, `30 work items: ownership, contract registration and task cards consistent.` |
| scratch (2a): `temporalDerivative u t x = deriv (fun r => u (r,x)) t := rfl` | compiles (also by `rw [temporalDerivative, deriv]`); deleted |
| scratch (2b): D2 conclusion restated with `temporalDerivative`, proved by `(timeDeriv_isSobolevDatum …).2` | compiles, no glue; deleted |
| scratch (2c): `HasSmoothSobolevPath` (inlined) + `3 ≤ m` ⟹ the `temporalDerivative` datum | compiles; deleted |
| scratch (6): round-1 SL8 sanity instantiation against the **new** `inner_energy_Rhigh` signature | compiles, both sides `0` (bound attained); deleted |
| verbatim check: round-1 `d2_scalar` block vs `TimeDerivative.lean` | 53 non-blank lines, **0 missing** |
| `grep -rn "\.equation" research/ formalization/` | no such field; `momentum` at `A02/SolutionClass.lean:130` |

## Paper / spec conformance

`timeDeriv_isSobolevDatum`'s hypotheses are `HasSmoothSobolevPath`'s body at
order `m` (`research/A04/Spec.lean:247-251`), its interior-time hypothesis is
`energyIdentityHigh`'s `t ∈ Ioo 0 T` (`:427`), and its order restriction `2 ≤ m`
is implied by `energyIdentityHigh`'s `3 ≤ m`.  The identified object is the
manuscript's `∂ₜu(t,·)` in the vendor's own spelling
(`NavierStokes.ProblemStatement.temporalDerivative`, `rfl`, finding 3), which is
precisely what `ClassicalSolutionR.momentum`'s `navierStokesResidual` contains —
so SL2 can now pair D2 with the momentum field with no interface friction.
