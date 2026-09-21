# REVIEW — lane 146-C01-jet-paths (row E4a: time-continuous carrier-B jet paths)

Reviewer run 2026-09-14, worktree `.claude/worktrees/146-C01-jet-paths`, branch
`erenup/146-C01-jet-paths`, HEAD `6ab29f3`.  Read-only: no Lean edited, no git state
touched.  Probe: `research/C01/probes/rev146_mutation.lean` (new).

## Verdict: **ACCEPT-WITH-NOTES**

The mathematics is right, the citations are real, the axioms are standard, both mutations
break.  Four notes, none blocking: one duplication (N1, a lemma the module re-proves is
already in its own import closure), one accuracy fix to the E4b record (N2), and one
genuine design obstruction for E4b that the ATTEMPTS file does not mention (N3) — the
`hB` shape it writes down is **not constructible at `t = 0`**.

---

## 1. What the lane claims

Row **E4a** of `research/C01/ENERGY_SPLIT.md` — the cheap half of route (a) for row E4
(`REVIEW_E3E4.md` §6(c)).  On a compact subwindow `[0,S] ⊂ [0,T)` of a classical solution
`w : ClassicalSolutionR ν a f T` with `hf : MemForceR f`, build the three carrier-B
(`SmoothL2Field Space`) paths of the momentum residual `h = f − (u·∇)u + νΔu`, prove each
has `L²` jets continuous in time (the `hB` shape of
`EulerOrdinarySobolev.wordEnergy_hasDerivWithinAt`), and record that the only remaining E4
obligation is the jet-continuity of `∇p` (booked E4b).

## 2. What is in Lean

`formalization/NSFormalization/Section4/C01/JetPaths.lean`, 283 lines, namespace
`NSFormalization.Section4.C01`, 18 declarations.  Claim by claim:

### 2.1 Force path — PASS, horizon handling honest

* `forcePath hf t := forceSliceField hf t.2.1` (`JetPaths.lean:86`) over `forceSliceField`
  (`MomentumCarrierB.lean:131`, which takes `ht : 0 ≤ t`).  `t.2.1 : 0 ≤ t.1` is the left
  half of `t.2 : t.1 ∈ Icc 0 S`.
* `forcePath_field` (`:89`) is `rfl`; `forceSliceField_field` (`MomentumCarrierB.lean:137`)
  is `rfl` too, so the representative is literally `fun x => f (t.1, x)`.
* `forcePath_jetLp_continuous` (`:99`) destructures `hf.2 n` as `⟨G, hpath, hGc, _, _⟩`,
  which matches `MemForceR` (`D01/ForceClass.lean:158-164`:
  `ContDiffOn ℝ ∞ f futureDomain ∧ ∀ m, ∃ G, IsSobolevPath ∧ ContDiffOn ℝ ∞ G futureTimes ∧
  MemLp G 1 ∧ MemLp G 2`).  The two `MemLp` legs are dropped — correct, they are not needed
  for continuity.
* The proof is the line-by-line mirror of `velocityField_jetLp_continuous`
  (`Section4/C01/Evolution.lean:164`), with `jetOfDatum_continuous`
  (`Evolution.lean:147`) used identically: `Lp.ext` + `(…).integrable n |>.coeFn_toLp` +
  `D01.jetOfDatum_ae`, then `(jetOfDatum_continuous n n (le_refl n)).comp …`.  The only
  difference is the membership fed to the composition: the velocity uses
  `mem_Ico_of_mem_Icc hST t.2` (needs `hST`), the force uses `t.2.1` and `futureTimes = Ici 0`
  (`ForceClass.lean:143`) — so **the force leg genuinely needs neither `w` nor `S < T`**, and
  `hGc.continuousOn` is strictly weaker than the `ContDiffOn ℝ ∞` the class provides.
* **`Icc 0 S` index is honest.**  `S` is an implicit variable inferred from `t : Icc 0 S`
  with no constraint to `T`; it is there only so the force path can be `addField`ed to the
  velocity-derived paths, which do carry `hST : S < T`.  (If `S < 0` the index type is empty
  and every statement in the module is vacuous — but that is the same convention
  `Evolution.velocityField` already uses, and the axioms file instantiates `S = 1 < T = 2`,
  so non-vacuity is witnessed.)

### 2.2 Laplacian / viscous paths — PASS, no `rfl` masking a different Laplacian

* Vendor lemmas exist at the cited lines, with the cited hypotheses:
  `continuous_jetLp_mapField` (`Euler/LpSmoothFieldAlgebra.lean:119`),
  `continuous_jetLp_addField` (`:128`),
  `continuous_jetLp_directionalField` (`:147`, signature
  `(A : K → SmoothL2Field V) (hA : ∀ n, Continuous …) (v : Space) (n : ℕ)`).
* `continuous_jetLp_sumField` (`JetPaths.lean:156`) is the `V`-general form; proof is the
  `Finset.induction_on` with `field_ext` + `continuous_jetLp_addField`, identical to the ℂ
  version it cites.  See **N1** — that ℂ version is already imported.
* `laplacianField_jetLp_continuous` (`:185`) really composes
  `continuous_jetLp_directionalField` twice (`continuous_jetLp_directionalField _
  (continuous_jetLp_directionalField A hA (axis i)) (axis i) m`) and feeds
  `continuous_jetLp_sumField`, matching `laplacianField`'s definition
  `sumField Finset.univ (fun i => (W.directionalField (axis i)).directionalField (axis i))`
  (`Source/OrdinaryViscousStability.lean:12`).
* **The Laplacian is the manuscript one, not a look-alike.**  `laplacianPath_field` (`:201`)
  goes `laplacianField_field` (`OrdinaryViscousStability.lean:16`, `= Laplacian.laplacian
  W.field`) → `vector_laplacian_eq_sum` (`Euler/MeanVectorIdentities.lean:36`,
  `Δ f = fun x => ∑ i, vectorPartial (vectorPartial f i) i x`) → `rfl`.  The closing `rfl`
  is honest: `vectorPartial f i x = fderiv ℝ f x (EuclideanSpace.single i 1)`
  (`MeanVectorIdentities.lean:14`), `coordinateVector i = EuclideanSpace.single i 1`
  (`NavierStokes/ProblemStatement.lean:39`) and `spatialDerivative u t y = fderiv ℝ (u(t,·)) y`
  (`:59`), so `∑ i, vectorPartial (vectorPartial f i) i x` and
  `spatialLaplacian u t x = ∑ i, fderiv ℝ (fun y => spatialDerivative u t y (coordinateVector i))
  x (coordinateVector i)` (`:76`) are definitionally the same term.  This is the same two-step
  bridge that `laplacianField_velocitySlice_field` (`MomentumCarrierB.lean:185`) already uses —
  consistent, not a second convention.
* `viscousPath := mapField (ν • ContinuousLinearMap.id ℝ Space) ∘ laplacianPath` (`:221`);
  `viscousPath_field` (`:225`) unfolds to `ν • spatialLaplacian …` through `mapField_field`,
  `smul_apply`, `id_apply`.  Jet continuity is `continuous_jetLp_mapField` (`:233`).

### 2.3 Advection path — PASS, vendor hypotheses are exactly the velocity jet continuity

* `EulerSmoothEulerEvolution.advection_jet_continuous` is at
  `vendor/NavierStokesAndEuler/Euler/SmoothEulerEvolution.lean:29` (the file is in the
  **NavierStokesAndEuler** vendor package, not HeliCorgi — the module cites only the file
  name, which is fine).  Its full hypothesis package is the section variables
  `{K} [TopologicalSpace K] [CompactSpace K]` plus
  `(U : K → SmoothL2Field Space) (hU : ∀ n, Continuous (fun t => (U t).jetLp n)) (n : ℕ)`.
  **No `pressure_continuous`, no evolution/PDE hypothesis, no extra structure** — the
  docstring of the file ("once the actual velocity and pressure-gradient L² jets are
  continuous") refers to `sobolev_evolution` further down (`:59`), not to this lemma.
  `CompactSpace (Icc (0:ℝ) S)` is found by instance search.
* The transport is honest: `jetLp_congr` is at
  `Euler/LpSmoothCoefficientProduct.lean:93` with hypothesis `h : f.field = g.field`, and the
  field equality is discharged by `advectionField_field`
  (`Euler/OrdinaryFieldAlgebra.lean:121`) vs `advection_field`
  (`SmoothEulerEvolution.lean:23`), both `fderiv ℝ (U t).field x ((U t).field x)`.
* `advectionPath_field` (`:123`) → `advection w.velocity t.1 x` by `rfl` after
  `advectionField_field`; same bridge as `advectionField_velocitySlice_field`
  (`MomentumCarrierB.lean:174`).

### 2.4 Residual path — PASS, sign convention matches E3, `hAm` matches token-for-token

* `residualPath := addField (fieldSub forcePath advectionPath) viscousPath` (`:243`).
  `fieldSub A B = addField A (fieldNeg B)` and `fieldNeg = mapField (-(id))`
  (`OrdinaryFieldAlgebra.lean:51,56`), which is exactly how `residualPath_jetLp_continuous`
  (`:259`) peels it: two `continuous_jetLp_addField` + one `continuous_jetLp_mapField`.
* `residualPath_field` (`:249`):
  `f (t.1, x) - advection w.velocity t.1 x + ν • spatialLaplacian w.velocity t.1 x`.
* **Sign convention vs `momentum_split_toLp`** (`MomentumCarrierB.lean:199`): that theorem
  states `(∂ₜu).toLp = ν•(Δu).toLp − (adv).toLp − (∇p).toLp + f.toLp`, i.e.
  `∂ₜu = f − adv + νΔu − ∇p` — the same rearrangement of
  `D01.temporalDerivative_slice_eq` (`D01/Pressure.lean:196`, verified verbatim) that
  `temporalDerivative_eq_residual_sub_pressureGradient` (`:275`) uses.  Consistent.
* **Token-for-token vs `pin_pressureGradient_datum`** (`D01/PressureJets.lean:112`): its
  `hAm` slot is
  `IsSobolevDatum (m:ℝ) (fun x => f (t, x) - advection u.velocity t x + ν • spatialLaplacian
  u.velocity t x) Am` (`PressureJets.lean:115-116`).  Character for character the same
  expression as `residualPath_field`'s right-hand side (modulo `t` vs `t.1`).  **Claim
  verified.**
* `temporalDerivative_eq_residual_sub_pressureGradient` (`:275`) correctly re-derives
  `ht : t.1 ∈ Ioo 0 T` from `htpos : 0 < t.1` and `lt_of_le_of_lt t.2.2 hST` — the interior
  guard is real and load-bearing (the PDE `ClassicalSolutionR.momentum` holds on `Ioo` only).

### 2.5 Non-vacuity, hygiene

`research/C01/axioms_jet_paths.lean` covers all 18 declarations and instantiates the whole
stack on `A04.zeroSol 1 2 _ _ : ClassicalSolutionR 1 0 0 2` with `A04.memForceR_zero`
(`Section4/A04/ZeroSolution.lean:70,91`) at `S = 1 < T = 2`; both `example`s elaborate.  No
`sorry/admit/axiom/native_decide/maxHeartbeats` anywhere in the lane's two Lean files.  The
module's own lines emit **zero warnings** (`lake env lean` on it is byte-empty).

## 3. Gaps and notes

### N1 (low, duplication + future ambiguity hazard) — `continuous_jetLp_sumField` is already in the import closure

The module re-proves `continuous_jetLp_sumField` (`JetPaths.lean:156`) and
`laplacianField_jetLp_continuous` (`:185`) as `V`-general copies of
`Source.PhysicalBesselSobolev.continuous_jetLp_sumField` (`:83`) and
`continuous_jetLp_laplacianField` (`:105`), whose only obstruction is that they are stated for
`SmoothL2Field ℂ`.  The docstrings say so honestly — but
`NSFormalization.Source.PhysicalBesselSobolev` **is already in `JetPaths`' transitive import
closure** (107 `NSFormalization` modules; verified by walking the `import` graph), so the
copies cost an import of nothing and the tree now carries the same proof twice.

Also a lesson-109 hazard: `D01/SmoothDatum.lean:91` already does
`open NSFormalization.Source.PhysicalBesselSobolev`, so any future Section-4 module that
`open`s that namespace **and** `NSFormalization.Section4.C01` will get `Ambiguous term` on the
bare name `continuous_jetLp_sumField`.

*One-line fix (for the follow-up simplifier lane, not for this merge):* generalise
`Source/PhysicalBesselSobolev.lean:83` in place — `(A : ι → K → SmoothL2Field ℂ)` →
`{V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (A : ι → K → SmoothL2Field V)`, same for
`:105` with `basis i` kept — and delete `JetPaths.lean:156` and `:185` in favour of it.

### N2 (medium, record accuracy) — what lane 145 actually supplies is **not** the jet-norm bound

`research/C01/ATTEMPTS_JET_PATHS.md:70-74` says Direction A "is closed" by lane 145's
`FiniteOrderNorm.lean` supplying
`‖smoothAngularDatum m (m:ℝ) _ A‖ ≤ C_m · ∑_{j≤m} ‖A.jetLp j‖`.
Reading 145 (`.claude/worktrees/145-D01-quantitative-constructor/formalization/NSFormalization/Section4/D01/FiniteOrderNorm.lean`,
read-only), what is actually there is:

```
HasWeakDerivsL2Bound z M : ℕ → Prop                                   (:352)
  | 0     => MemLp z 2 volume ∧ (eLpNorm z 2 volume).toReal ^ 2 ≤ M
  | m + 1 => (… same at order 0 …) ∧ ∀ j : Fin 3, ∃ w, HasWeakDerivsL2Bound w M m ∧
               (∀ i ψ, ∫ ψ·w_i = ∫ (-∂_{coordinateVector j} ψ)·z_i)
norm_isSobolevDatum_le_of_memLp_derivs (m z M) (h : HasWeakDerivsL2Bound z M m)
    (A) (hA : IsSobolevDatum (m:ℝ) z A) : ‖A‖ ^ 2 ≤ (16:ℝ) ^ m * M      (:413)
```

Three differences from what ATTEMPTS claims, all of them real work:

1. **Quadratic, `max`-form, not a linear jet bound.**  `M` is a *single uniform* bound on
   `(eLpNorm · 2).toReal ^ 2` of every **coordinate weak derivative** field up to order `m`
   (`exists_hasWeakDerivsL2Bound_smooth`, `:444`, builds it as a `max` of the finitely many
   `(Z.directionalField (coordinateVector j))` norms).  Getting to `C_m·∑_{j≤m}‖A.jetLp j‖`
   needs the bridge **`eLpNorm (iterated coordinate directionalField of order j) 2 |>.toReal
   ≤ ‖Z.jetLp j‖`**, which is *not in tree* (grepped `norm_directionalField`,
   `norm_jetLp`, `norm_toLp_mapField`: nothing).  It is small — `directionalField A v =
   mapField (apply ℝ V v) A.derivative` (`LpSmoothFieldAlgebra.lean:94`),
   `jetLp_mapField` (`:39`), `norm_derivative_jetLp : ‖A.derivative.jetLp n‖ = ‖A.jetLp (n+1)‖`
   (`LpSmoothField.lean:94`) — but it has to be written.
2. **No linearity.**  145 bounds one datum of one field; continuity needs the estimate on
   *differences*, i.e. `smoothAngularDatum m s hs (fieldSub A B) = smoothAngularDatum … A −
   smoothAngularDatum … B`.  That is obtainable from `isSobolevDatum_unique` plus
   `D01.isSobolevDatum_sub`, **but that lemma carries `hs : 2 ≤ s`**
   (`Section4/A03/VectorTameProduct.lean:186`), so orders `m = 0, 1` are not covered — order 0
   has `A01.orderZeroDatumCLM` (`DatumPathContinuity.lean:103`, confirmed) and **order 1 is an
   uncovered hole**.  Alternatively prove additivity structurally: `smoothAngularDatum`
   (`SmoothDatum.lean:260`) is `cyclesToAngularRealVector ∘ WithLp.toLp ∘ realProjectionTo ∘
   sobolevOrderLowering ∘ integerSobolevDatum ∘ componentField`, every stage linear on the
   underlying `Lp`.
3. `sobolevENorm_le_norm_smoothAngularDatum` (`SmoothDatum.lean:349`) is indeed the *other*
   direction, as ATTEMPTS says — that part is accurate.

*Fix:* replace ATTEMPTS' "This is lane 145's forthcoming `FiniteOrderNorm.lean`" with
"lane 145 supplies `‖A‖² ≤ 16^m·M` for `M` a uniform bound on the coordinate weak-derivative
`L²` norms (`norm_isSobolevDatum_le_of_memLp_derivs`); E4b must still (i) bridge those norms
to `‖A.jetLp j‖`, and (ii) supply additivity of `smoothAngularDatum` at every order (the
`2 ≤ s` gap at order 1)."

### N3 (medium, design) — the `hB` shape ATTEMPTS writes is not constructible at `t = 0`

`ATTEMPTS_JET_PATHS.md:48-50` states the E4 target as
`∀ n, Continuous (fun t : Icc 0 S => (∂ₜu(t.1,·) packaged as SmoothL2Field).jetLp n)`.
The vendor consumer really does demand the closed interval: in
`Euler/OrdinaryWordTime.lean:70-75` the paths are `A B : Icc (0:ℝ) T → SmoothL2Field Space`
with `hA hB` on all of `Icc 0 T` and only `hd` restricted to `Ioo 0 T`.  But the tree's
packaging of `∂ₜu` and of `∇p` — `temporalSliceField` (`MomentumCarrierB.lean:119`) and
`pressureGradientField` — both require `ht : t ∈ Ioo (0:ℝ) T`, because their `H^∞` proofs run
through `D01.pressureGradient_slice_smoothSquareIntegrableJets_of_memForceR`
(`PressureJets.lean:126`), which uses the PDE and therefore the interior.  **`B 0` does not
exist in tree.**  (`residualPath` itself is fine at `t = 0`: the force needs only `0 ≤ t` and
`velocityField` only `t ∈ Ico 0 T` — this lane's E4a output has no endpoint problem.)

Cheapest way out, recommended for the E4b lane: **shift the window off the endpoint**.  Pick
`0 < c < S < T`, set `T' := S − c`, and feed the vendor
`A t := velocityField w hST ⟨t.1 + c, _⟩`, `B t := temporalSliceField w hf _` on
`Icc (0:ℝ) T'`; `hd` at `t ∈ Ioo 0 T'` then corresponds to genuine interior times
`(c, S) ⊂ (0,T)`, and `HasDerivWithinAt (Icc 0 T')` at an interior point upgrades to
`HasDerivAt`, which is what row E4 owes.  The alternative — extending `∇p(t,·) ∈ H^∞` to
`t = 0` — is not available, since `ClassicalSolutionR.momentum` holds on `Ioo` only.

### The exact E4b statement the next lane must prove

With `0 < c`, `c < S`, `hST : S < T`, `w : ClassicalSolutionR ν a f T`, `hf : MemForceR f`:

```lean
/-- E4b.  The pressure-gradient path has jets continuous in time on a window
    strictly inside `(0,T)`. -/
theorem pressureGradientPath_jetLp_continuous
    (w : ClassicalSolutionR ν a f T) (hf : MemForceR f) (hc : 0 < c) (hcS : c ≤ S)
    (hST : S < T) (n : ℕ) :
    Continuous (fun t : Icc c S =>
      (pressureGradientField w hf (show t.1 ∈ Ioo (0:ℝ) T from
        ⟨lt_of_lt_of_le hc t.2.1, lt_of_le_of_lt t.2.2 hST⟩)).jetLp n)
```

and its immediate corollary, which is the `hB` that `wordEnergy_hasDerivWithinAt` consumes:

```lean
theorem temporalSlicePath_jetLp_continuous (… same binders …) (n : ℕ) :
    Continuous (fun t : Icc c S => (temporalSliceField w hf (… ∈ Ioo 0 T …)).jetLp n)
```

obtained from this lane's `residualPath_jetLp_continuous` **minus** the above, via
`continuous_jetLp_addField` + the negation `mapField`, using
`temporalDerivative_eq_residual_sub_pressureGradient` (`JetPaths.lean:275`) plus
`jetLp_congr` to identify the fields.

The proof of the first theorem is the three-step chain the ATTEMPTS file lays out, with the
two repairs of **N2**:

1. *jets ⟹ order-`m` datum* (the cost): `∀ m, Continuous (fun t : Icc c S =>
   D01.smoothAngularDatum m (m:ℝ) (le_refl _) (residualPath w hf hST' t))` — needs 145's
   `norm_isSobolevDatum_le_of_memLp_derivs` **plus** the `eLpNorm(∂^α) ≤ ‖jetLp |α|‖` bridge
   **plus** additivity of `smoothAngularDatum` (order-1 gap);
2. *Leray*: compose with the CLM `D01.Leray.lerayComplement (m:ℝ)`
   (`D01/LerayDatum.lean:255`, `mkContinuous 1` — confirmed), and pin it to `∇p`'s datum with
   `D01.pin_pressureGradient_datum` (`PressureJets.lean:112`), whose `hAm` is exactly
   `residualPath_field`;
3. *order-`m` datum ⟹ jets* (exists): `jetOfDatum_continuous` (`Evolution.lean:147`) +
   `D01.jetOfDatum_ae`, verbatim the pattern of `forcePath_jetLp_continuous`.

### N4 (cosmetic)

`ENERGY_SPLIT.md` row E4a writes "`pin_pressureGradient_datum`s `hAm`" (apostrophe dropped
inside backticks).  Harmless; fix when the row is next touched.

## 4. Commands and results

All from the lane worktree, after `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, `lake` only
from `verification/`, one `lake` at a time.

| command | result |
|---|---|
| `lake build NSFormalization.Section4.C01.JetPaths` | **exit 0**, `Build completed successfully (10191 jobs)`; 50 `warning:` lines, **0** of them from `Section4`, **0** mentioning `JetPaths` |
| `lake env lean ../formalization/NSFormalization/Section4/C01/JetPaths.lean` | **exit 0**, output **0 bytes** |
| `lake env lean ../research/C01/axioms_jet_paths.lean` | **exit 0**, 22 lines = 18 `#print axioms`, every one `[propext, Classical.choice, Quot.sound]`; both `A04.zeroSol` `example`s elaborate silently |
| `grep -nE 'sorry\|admit\|native_decide\|maxHeartbeats\|^[[:space:]]*axiom ' JetPaths.lean axioms_jet_paths.lean` | no output (exit 1) |
| `make check` | **exit 0** — `check_formalization_plan.py --check` OK (only the known `Paper1/BoundaryCorollary.lean:90` `sorry`), `check_contracts.py` 24 contracts, `test_contract_policy.py` `Ran 13 tests … OK`, `check_work_queue.py` `30 work items: … consistent` |
| `git diff --stat origin/erenup/integration...HEAD` | 4 files, **451 insertions, 0 deletions**; no `verification/` or `Contracts/` file touched, so no `scripts/gates.sh` mutation run is owed |

### Negative check (two substantive mutations)

`research/C01/probes/rev146_mutation.lean` — the lane's own proof scripts run against
mutated statements:

**M1** `residualPath_field` with the advection sign flipped (`f + adv + νΔu`):

```
../research/C01/probes/rev146_mutation.lean:33:91: error: unsolved goals
⊢ (fun x => f (↑t, x)) x - advection w.velocity (↑t) x + ν • spatialLaplacian w.velocity (↑t) x =
    f (↑t, x) + advection w.velocity (↑t) x + ν • spatialLaplacian w.velocity (↑t) x
```

**M2** `viscousPath_field` with `ν •` replaced by the identity:

```
../research/C01/probes/rev146_mutation.lean:40:73: error: unsolved goals
⊢ ν • spatialLaplacian w.velocity (↑t) x = spatialLaplacian w.velocity (↑t) x
```

Hardened (so this is not proof-script fragility): re-run with the *proved* lemma rewritten in
first and then `abel` / `simp`:

```
error: unsolved goals
⊢ f (↑t, x) + (-1 • advection w.velocity (↑t) x + ν • spatialLaplacian w.velocity (↑t) x) =
    f (↑t, x) + (advection w.velocity (↑t) x + ν • spatialLaplacian w.velocity (↑t) x)
error: `simp` made no progress
```

Both mutations are genuinely unreachable (they would need `advection ≡ 0`, resp. `ν = 1`), so
the sign of the nonlinear term and the viscosity factor are both pinned by the module.

### Citations opened at the cited lines (all confirmed)

`Evolution.lean:147,164` · `D01/ForceClass.lean:158` · `D01/Pressure.lean:196` ·
`D01/PressureJets.lean:112` · `D01/SmoothDatum.lean:260,349` · `D01/LerayDatum.lean:255` ·
`A01/DatumPathContinuity.lean:103,127` · `Source/OrdinaryViscousStability.lean:12,16` ·
`Source/PhysicalBesselSobolev.lean:83,105` · `Euler/SmoothEulerEvolution.lean:23,29` ·
`Euler/LpSmoothFieldAlgebra.lean:119,128,147` · `Euler/MeanVectorIdentities.lean:14,36` ·
`Euler/LpSmoothCoefficientProduct.lean:93` · `Euler/OrdinaryFieldAlgebra.lean:51,56,118,121` ·
`Euler/OrdinaryWordTime.lean:70-75,87` · `MomentumCarrierB.lean:119,131,174,185,199` ·
`A04/ZeroSolution.lean:70,91` · `REVIEW_E3E4.md` §6(c).
One correction: `SmoothEulerEvolution.lean` lives in `vendor/NavierStokesAndEuler/Euler/`,
not in `vendor/HeliCorgi/` (the module cites only the bare file name, so nothing to change).
