# REVIEW — lane 131-C01-energy-split (C01 energy/enstrophy split-and-start)

Reviewer run 2026-09-13, worktree `.claude/worktrees/131-C01-energy-split`,
branch `erenup/131-C01-energy-split`, one commit `b5dc27c` on top of merge-base
`a016bf6` (`origin/erenup/integration`).  Probes in `/tmp/rev131/`; every error /
success line quoted below was produced by the command shown above it.

## Verdict: **ACCEPT-WITH-NOTES**

The committed Lean (`Section4/C01/EnergyIdentity.lean`) is correct, clean, faithful
to eq:RL2 and useful: it compiles, the two theorems carry only the standard three
axioms, the signs are right (checked against concrete numbers, and the wrong-sign
variant is provably false), and the derivative form matches the spec field
`energyIdentity` token-for-token modulo the named vocabulary bridge.  Nothing in
the Lean needs to change.

The **table** `ENERGY_SPLIT.md` is where the notes are.  Its headline — "carrier B
(vendor jet `SmoothL2Field`) has every ingredient, with no order hypothesis" — is
**not accurate as stated**: two of the five hypotheses of the lane's own `E0`
(`hpr`, and `hd` via the derivative path) are gated on a single open item that
C01's *own* `Section4/C01/Evolution.lean` already documents (all-order jets of
`∇p(t,·)`, D01 unit **L9(c)**), and the table never mentions it.  The table also
omits `Evolution.lean` entirely, although that module already proves most of its
row E1.  One recorded negative example in `ATTEMPTS_ENERGY.md` does not reproduce.
These are planning-artifact defects, not proof defects, hence ACCEPT-WITH-NOTES
rather than REJECT: fix the table (findings 5–9) before the next C01 lane is
briefed off it.

---

## 1. Compiles / axioms / hygiene — **PASS**

```
cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.C01.EnergyIdentity
EXIT=0
Build completed successfully (1945 jobs).

cd verification && lake env lean ../formalization/NSFormalization/Section4/C01/EnergyIdentity.lean
EXIT=0   BYTES=0        (silent — no warning, no linter hit)

cd verification && lake env lean ../research/C01/axioms_energy.lean
EXIT=0
'NSFormalization.Section4.C01.inner_energy_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.C01.inner_energy_identity_deriv' depends on axioms: [propext, Classical.choice, Quot.sound]

make check    → EXIT=0 ("30 work items: ownership, contract registration and task cards consistent.", 13/13 policy tests OK)
make test     → EXIT=0 (10123 jobs replayed; every registered contract "checked; standard logical axioms only")

grep -nE 'sorry|admit|axiom|native_decide|maxHeartbeats|set_option' on both files
  → EnergyIdentity.lean: no hits.
  → axioms_energy.lean: only the docstring words and the two `#print axioms` lines.
```

No `set_option`, no heartbeat bumps, no forbidden import (the module imports only
`Mathlib.Analysis.InnerProductSpace.Basic`; it is a leaf, imported by nothing).

## 2. Statement fidelity and usefulness — **PASS**, with two consumer-side notes

`#check` (`/tmp/rev131/sign.lean`), verbatim:

```
@inner_energy_identity : ∀ {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {G Gt N P L F : E} {ν grad d : ℝ},
  d = 2 * ⟪G, Gt⟫ → Gt = ν • L - N - P + F → ⟪G, L⟫ = -grad ^ 2 → ⟪G, P⟫ = 0 → ⟪G, N⟫ = 0 →
    1 / 2 * d + ν * grad ^ 2 = ⟪G, F⟫
@inner_energy_identity_deriv : … → d = -2 * ν * grad ^ 2 + 2 * ⟪G, F⟫
```

**Finding 1 (info).  It *is* exactly the `m = 0` specialization of A04's
`inner_energy_assembly`, and it could *not* have been derived from it.**
`#check @NSFormalization.Section4.A04.inner_energy_assembly` returns the same
`hd`/`hmom`/`hpr` verbatim, `hlap : ⟪G,L⟫ ≤ -grad^2` (here `=`), `hnl : -⟪G,N⟫ ≤ NLbound`
(here `⟪G,N⟫ = 0`), plus `hν`, `hG`, `hF`, and concludes
`… ≤ NLbound + fNorm * uNorm`.  The force pairing is consumed *inside* the A04
lemma by Cauchy–Schwarz (`real_inner_le_norm`), and `hG : ‖G‖ = uNorm`,
`hF : ‖F‖ = fNorm` pin `fNorm * uNorm = ‖F‖‖G‖ ≥ ⟪G,F⟫` with equality only for
collinear `G, F`.  So the identity is *not* recoverable from the assembly's
conclusion at any instantiation — the new lemma is necessary.  What *is* duplicated
is the five-line `hexpand` block (`rw [hmom]; simp only [inner_add_right,
inner_sub_right, real_inner_smul_right, hpr]; ring`), byte-identical in
`HighEnergy.lean:109-113` and `EnergyIdentity.lean:87-91`.  A later simplifier lane
may want to factor it out as `inner_momentum_expand`; **note, not a change** (the
brief's own instruction, and `HighEnergy.lean` is outside this lane's scope).

**Finding 2 (info).  Sign conventions are right — concrete check, plus a false
wrong-sign variant.**  `/tmp/rev131/sign.lean` instantiates `E = ℝ` with
`G = 1, L = -1, N = 0, P = 0, F = 3, ν = 2`, so `⟪G,L⟫ = -1 = -(1)^2` (`grad = 1`),
`Gt = ν•L - 0 - 0 + F = 1`, `d = 2⟪G,Gt⟫ = 2`; both theorems close, i.e.
`½·2 + 2·1 = 3 = ⟪G,F⟫` and `2 = -2·2·1 + 2·3`.  The same file proves the
opposite-sign reading false: with `L = +1` (so `⟪G,L⟫ = +grad^2`) one gets
`Gt = 5, d = 10`, and `¬(½·10 + 2·1 = ⟪(1:ℝ),(3:ℝ)⟫)` is proved by `norm_num`.
`EXIT=0`, only two `unusedSimpArgs`/`unnecessarySeqFocus` linter warnings on the
probe's own tactic script.

**Finding 3 (info).  Derivative form matches the spec field token-for-token; here
is exactly what row E2 must prove.**  Spec (`research/C01/Spec.lean:344-350`):

```
HasDerivAt (fun s => l2Sq (slice w.velocity s))
  (-2 * ν * gradientSq (slice w.velocity t) + 2 * pairing (slice w.velocity t) (slice f t)) t
```

E0 gives `d = -2 * ν * grad ^ 2 + 2 * ⟪G, F⟫`: identical shape, identical argument
order (`pairing u f`, i.e. `⟪G,F⟫` with `G` the velocity and `F` the force).  The
spec vocabulary is (`Spec.lean:167,172,177,185,196`)

```
slice z t = fun x => z (t, x)
l2Sq z      = ∫ x, ‖z x‖ ^ 2
gradientSq z = ∫ x, ‖gradientTensor z x‖ ^ 2      -- gradientTensor z x : WithLp 2 (Fin 3 → Space)
pairing w z = ∫ x, ⟪w x, z x⟫_ℝ
l2Norm z    = Real.sqrt (l2Sq z)
```

so on carrier B, with `Z : Icc 0 S → SmoothL2Field Space` the velocity path and
`W t` the force slice, **E2 must prove exactly three equations**:

* (E2a) `‖(Z s).toLp‖ ^ 2 = l2Sq (slice u s)` — **for `s` in a neighbourhood of `t`,
  not only at `t`** (it sits under the `fun s => …` binder);
* (E2b) `∑ i, ‖((Z t).directionalField (axis i)).toLp‖ ^ 2 = gradientSq (slice u t)`;
* (E2c) `⟪(Z t).toLp, (W t).toLp⟫_ℝ = pairing (slice u t) (slice f t)`.

(E2a) and (E2c) are `EulerOrdinarySobolev.field_inner` plus
`real_inner_self_eq_norm_sq`.  (E2b) is *cheaper than the table rates it*: the
table calls the Frobenius identity "the only non-trivial piece" and rates E2 **M**,
but `Contracts.V1.gradientTensor v x = Data.spatialGradient (lift v) 0 x
= WithLp.toLp 2 (fun i => spatialDerivative … (coordinateVector i))` lands in
`WithLp 2 (Fin 3 → Space)` (`Data.lean:453`, `GradientL6.lean:89`), whose norm is
already the `ℓ²` assembly — `PiLp.norm_sq_eq_of_L2` — and
`coordinateVector i = EuclideanSpace.single i 1 = EulerOrdinarySobolev.axis i`
(`ProblemStatement.lean:39`, `OrdinarySmoothWords.lean:17`) while
`directionalField_field … = fderiv ℝ A.field x v := rfl`
(`LpSmoothFieldAlgebra.lean:97-98`).  **E2 is S–M, not M.**

**Finding 4 (minor, consumer-side friction).  E0's `-grad ^ 2` does not fit
carrier B's dissipation shape without a square root.**  `laplacian_pairing`
(`#check`ed) returns

```
NSFormalization.Source.OrdinaryViscousStability.laplacian_pairing : ∀ (W : SmoothL2Field Space),
  inner ℝ W.toLp (laplacianField W).toLp = -∑ i, ‖(W.directionalField (axis i)).toLp‖ ^ 2
```

— a *sum* of squares, not the square of one real.  E0 inherited `-grad ^ 2` from
`inner_energy_assembly`, where `grad` is the genuine norm
`gradientSobolevNormAt (m:ℝ) u t` and the shape is natural.  On carrier B the
assembly lane must instantiate `grad := Real.sqrt (∑ i, ‖…‖^2)` and discharge
`Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)`.  Two lines, no blocker —
but it belongs in the plan, and the table does not mention it.

**Joint satisfiability of `hd`/`hmom`/`hlap`/`hpr`/`hnl` in the intended carrier B**
is the substance of finding 5 below: three of the five are delivered today, two are
not.

## 3. Validating the table — the key judgement

### (a) The carrier-A dead-end claim — **substantially correct**, one nuance

`#check` (`/tmp/rev131/checks.lean`, `checks2.lean`) confirms every claim of §0:

* `A04.momentum_datum` : `… (w : ClassicalSolutionR ν a f T) → MemForceR f → ∀ {m : ℕ}, 2 ≤ m → …`
* `A04.timeDeriv_isSobolevDatum` : `… {m : ℕ}, 2 ≤ m → …`  ⇒ the momentum equation on
  carrier A really is unavailable below order 2 *by the existing lemmas*.
* `A04.inner_datum_laplacian` : an **equality** `⟪G, laplacianDatum m A⟫ = -∑ j, ‖derivDatumStep m j A'‖^2`,
  **no order hypothesis** (data at `m`, `m+1`, `m+2`).
* `A04.inner_datum_laplacian_le'` : `… ≤ -gradientSobolevNormAt (↑m) u t ^ 2`, **no order hypothesis**
  — note this one already has E0's `-grad^2` shape (cf. finding 4).
* `A04.pressure_drop` : `… ∀ {m : ℕ} {t : ℝ}, t ∈ Ioo 0 T → … ⟪G, P⟫ = 0`, **no order hypothesis**.
* `D01/OrderZeroDatum.lean:40-53` reads verbatim "## Scope: the norm identity is NOT
  proved here … The Plancherel **norm identity** `‖orderZeroDatum hz‖ = ‖z‖_{L²}` … is
  deliberately **not** proved here … needing two pieces absent from the tree"
  (the vector isometry `cyclesToAngularRealVector_symm_norm_le` and the Euclidean
  Pythagorean `L²` identity).  The table cites `:43-52`; the section is `:40-53`.

Lane 124's work (`A01/DatumPathContinuity.lean:103,117,127`) gives
`orderZeroDatumCLM : L2 →L[ℝ] RealVectorSobolev 0`, `orderZeroDatum_memLp_eq`,
`continuous_orderZeroDatum`, `datumPath`, `continuousOn_datumPath`; the
integration-branch probe `research/A01/probes/orderZeroDatumCLM_injective_probe.lean`
adds `orderZeroDatumCLM_injective` (a probe file, not a library module).

**Nuance the table gets slightly wrong.**  The table explains the carrier-A block as
structural ("the datum time-derivative uses `angularBoundedRepresentative s hs`,
`hs : 2 ≤ s`").  With lane 124's CLM that reason is *not* structural at `m = 0`: a
continuous linear map commutes with derivatives, so `deriv (orderZeroDatumCLM ∘ U) t
= orderZeroDatumCLM (U' t)` needs no bounded representative — what it needs instead is
`HasDerivAt` of the velocity path **in `L²`**, which is a different (and equally real)
analytic obligation, and which carrier B's `wordEnergy_hasDerivWithinAt` sidesteps by
taking the *pointwise* `HasDerivAt` plus jet continuity.  So the table's *conclusion*
(carrier A is not the route) stands, but the *binding* reason is the **Plancherel/Parseval
bridge**, which is open in both directions (`‖·‖_{H⁰} ↔ l2Sq` and `⟪·,·⟫_{H⁰} ↔ pairing`,
and `gradientSobolevNormAt 0 ↔ gradientSq` on top), not the `2 ≤ m` of `momentum_datum`.
Recommend rewording §0 accordingly, so a later lane does not "unblock" `momentum_datum`
at `m = 0` and think carrier A has opened up.

Conversely — see finding 5 — carrier A's **pressure** handling at `m = 0` is
*unconditional* (`pressure_drop` + `D01.exists_isSobolevDatum_zero_of_memLp`, both
`#check`ed, the latter needing only `MemLp z 2`, which `ClassicalSolutionR.pressure_gradient`
supplies), while carrier B's is the blocked one.  The table asserts the opposite
asymmetry.

### (b) Citations and sizes

Every `file:line` was opened and every named declaration `#check`ed.  Correct:
`HighEnergy.lean:100`, `LaplacianAssembly.lean:306` and `:353`, `PressureDrop.lean:216`,
`OrdinaryTransportCancellation.lean:42`, `Source/OrdinaryViscousStability.lean:32`,
`OrdinaryL2Integration.lean:33`, `OrdinaryWordTime.lean:87`,
`OrdinaryPressureCancellation.lean:84`, `OrdinaryEulerKineticEnergy.lean:17`,
`AngularGradientIdentity.lean:92` (and it does carry `HasCompactSupport F`, confirming
the **L** rating of `sobolevTwoFourier`), `Paper1/ScalarEnergy.lean:22` (and it does
require `E 0 = 0` *and* `N 0 = 0`, confirming the generalization the `l2Bound` row asks for).

**Finding 5 is the substantive one; first the small citation slips:**

| cited | actual |
|---|---|
| `OrdinaryL2Integration.lean:8` for `⟪A.toLp,B.toLp⟫ = ∫⟨A.field,B.field⟩` | line 8 is a docstring line; the theorem is `field_inner` at **`:26`** |
| `OrdinaryEulerKineticEnergy.lean:25` for `kineticEnergy_hasDerivWithinAt` | blank line; the theorem is at **`:26`** |
| `MomentumDatum.lean:140` for `momentum_datum` | the `theorem` line is **`:138`** (`:140` is its `hm : 2 ≤ m`) |
| `D01/OrderZeroDatum.lean:43-52` | the scope section is **`:40-53`** |

None is load-bearing, but `logs/LESSONS.md` (2026-09-14, "论文行号引用会代代相传") is
explicit that line numbers propagate into frozen contract strings; fix them now.

Sizes: E2 is over-rated (finding 3: **S–M**).  E1 is mis-rated for the opposite reason
(finding 6).  E4, E5, E6, `enstrophyDifferentialBound`, `enstrophyIntegralBound`,
`l2Bound`, `sobolevTwoFourier` ratings look right to me; `energyDifferentialBound` is
**S only after E2's norm half** (`l2Norm z = ‖Z.toLp‖`), which the row does not list
among its inputs.

### (c) Carrier consistency with what C01 and A04 have registered — **consistent; exactly one crossing**

`verification/Contracts/V1/EnergyAbsorptionPartial.lean` is *carrier-neutral where it
matters and carrier-B-friendly elsewhere*: `velocityJets` asserts each velocity slice is
`H^∞` **in both forms** — `Data.MemHInfty` (datum/carrier A) *and*
`Contracts.V1.SmoothSquareIntegrableJets` (`GradientL6.lean:106`, which is field-for-field
`EulerLpTranslation.SmoothL2Field`: `ContDiff ℝ ∞ v ∧ ∀ n, MemLp (iteratedFDeriv ℝ n v) 2 volume`) —
so the registered clause is precisely the bridge that lets a velocity slice be *packaged*
on carrier B.  `trilinearHolder`, `trilinearAbsorbed`, `laplacianSqENorm` are physical
(`eLpNorm` / Bochner), never datum.  **So choosing carrier B is consistent with C01's
registered half, and the table is right to say so.**

A04's contract is carrier A (datum/Fourier), and the two C01 halves will meet at exactly
one place: `sobolevTwoFourier` (`Spec.lean:555-558`) has `sobolevENorm 2 z ^ (2:ℝ)` on the
left (D01 datum norm, `ℝ≥0∞`) and `l2Sq z + laplacianSq z` (physical, real) on the right.
`h2TimeIntegral` / `h2TimeIntegralZeroDatum` (`:576`, `:599`) also carry `sobolevENorm 2`
in their `∫⁻`, but they consume `sobolevTwoFourier` to get there, so the crossing stays
localized in that one field.  The table states this correctly; I confirm it, and confirm
that this crossing re-opens the same norm-identification family as the *order-0* Plancherel
item — at order 2 (`Source.vectorAngularSobolevNorm` ↔ `D01.sobolevENorm 2`) plus a
de-compactification of `vectorAngularSobolev_succ`.  **L is the right rating.**

### (d) Missing rows — **finding 5 (major) and findings 6–8**

**Finding 5 (MAJOR — the table's headline claim is wrong for the pressure).**
The table says carrier B has "every ingredient … with no order hypothesis" and lists
the pressure as "`OrdinaryPressureCancellation.gradient_mem` (`:84`) + solenoidal
orthogonality".  In fact:

* the ready-made lemma is better than cited — `EulerOrdinarySobolev.gradient_pairing_zero`
  (`OrdinaryPressureCancellation.lean:98`; `#check`ed), and `…_of_differentiable` (`:115`):
  ```
  gradient_pairing_zero : ∀ (A U : SmoothL2Field Space) (p : Space → ℝ), ContDiff ℝ ⊤ p →
    (∀ x, A.field x = gradient p x) → (∀ x, divergence U.field x = 0) → inner ℝ A.toLp U.toLp = 0
  ```
  — so the *shape* is exactly `hpr`, and `hdiv` for `U := u` is already proved in
  `C01/Evolution.lean:130` (`velocityField_solenoidal`);
* **but its first argument is `A : SmoothL2Field Space` with `A.field = ∇p(t,·)`**, and
  `SmoothL2Field` is `field` + `smooth` + `integrable : ∀ n, MemLp (iteratedFDeriv ℝ n field) 2 volume`
  (`LpSmoothField.lean:31-34`) — *all-order* jets of `∇p` in `L²`.  The class gives only
  order-zero `MemLp` of `∇p` (`Data.lean:647` `pressure_gradient`) and smoothness of the
  slice.  This is **D01 unit L9(c)**, and **C01's own `Section4/C01/Evolution.lean:60-76`
  already documents it as "a **single** root gap"**, together with the observation that the
  *derivative path* (`hB` of `wordEnergy_hasDerivWithinAt`, i.e. the table's E4) "reduces to
  the root gap above plus routine work".
* I checked there is no other whole-space producer of `gradientSpace` membership: grepping
  `∈ gradientSpace` over `vendor/.../Euler/*.lean` and `formalization/` returns
  `testGradient_mem` (compact support — inapplicable), `gradient_mem` (the above),
  `sub_solenoidalProjection_mem_gradient`, and otherwise only the **torus/lifted**
  `gradientSpace period κ m`, a different object.  `pressure_pairing_zero`
  (`MeanSolenoidalSpace.lean:129`, pure `L²`: `p ∈ gradientSpace → u ∈ solenoidalSpace → ⟪p,u⟫ = 0`)
  is available, but only once that membership is in hand.

So **two of E0's five hypotheses are not deliverable on carrier B today** — `hpr`, and
`hd` through the derivative path — and both bottom out in the same open item.  The table
must say so; as written it would send the next lane into E1→E4→assembly and it would
stall at the pressure.  (`Evolution.lean` records L9(c) as "blocked on toolchain task
U05"; per `CLAUDE.md`/`PLAN.md`, **U05 is now done** (lanes 004/010, PR #8/#11), and
`Formal.R3HelmholtzPressure` is a registered root of the `Formal` library
(`formalization/lakefile.toml:105`) with `r3LerayComplementL2` (`:228`) and
`r3HelmholtzPressure_gradient` (`:259`) present — i.e. the `L²`-level witnesses now
compile under this pin.  The `H^m`-level Leray boundedness that L9(c) also needs is
still work.)

**Finding 6 (moderate — the table omits `C01/Evolution.lean`, and mis-sizes E1).**
Row E1 is "package the slice as a `SmoothL2Field`: `∃ Z, Z.field = slice w.velocity t`,
S–M, inputs `C01.velocity_slice_smoothL2` …".  But `formalization/NSFormalization/Section4/C01/Evolution.lean`
(unit **U3**, already on integration, in the same directory) proves the *path* version and
more:

* `velocityField (u) (hST : S < T) : Icc 0 S → SmoothL2Field Space` (`:115`);
* `velocityField_field` (`:123`, `@[simp]`, the representative is literally the slice);
* `velocityField_solenoidal` (`:130` — the `hdiv` of `advection_inner_zero` *and* of
  `gradient_pairing_zero`);
* `velocityField_jetLp_continuous` (`:164`) — **this is exactly the `hA` hypothesis of
  `wordEnergy_hasDerivWithinAt`**, i.e. half of row E4, already closed.

E1 as written is therefore essentially **done**; the real remaining content of E4 is the
**derivative path** `B : Icc 0 S → SmoothL2Field Space` with `jetLp` continuity and the
pointwise `HasDerivAt` — which is finding 5's root gap.  The table should replace E1 by a
"consume `Evolution.velocityField`" line and add the derivative-path row explicitly.

**Finding 7 (minor — a missing bookkeeping obligation in E4).**  `wordEnergy_hasDerivWithinAt`
(`#check`ed) concludes
`HasDerivWithinAt (fun r => wordEnergy s (A (Set.projIcc 0 T hT r))) (2 * ∑_{n ∈ range (s+1)} ∑_w ⟪wordField (A t) w, wordField (B t) w⟫) (Icc 0 T) t`.
Reaching the spec's `HasDerivAt (fun s => l2Sq (slice u s)) … t` needs, besides the
`Icc → Ioo` upgrade the table does mention, a **function-level** congruence on a
neighbourhood of `t` (`fun r => wordEnergy 0 (A (projIcc … r))` vs `fun s => l2Sq (slice u s)`,
i.e. E2a for every nearby `s`, plus disposing of `projIcc`).  `HasDerivAt.congr_of_eventuallyEq`
is the tool; it is a row, not a remark.

**Finding 8 (minor — `energyDifferentialBound`'s input list).**  The row lists
`HasDerivAt.unique` + Cauchy–Schwarz, but the conclusion is stated in `l2Norm`
(`= Real.sqrt (l2Sq …)`), so it also needs E2a in the form `l2Norm (slice z t) = ‖(Z t).toLp‖`
before `real_inner_le_norm` applies.  Still **S**, but after E2, not in parallel with it.

## 4. Honesty of `ATTEMPTS_ENERGY.md` — one recorded negative example is **false**

**Finding 9 (moderate for process, harmless for the proof).**  `ATTEMPTS_ENERGY.md`
records, under "Paths considered and rejected":

> **`linarith` for `inner_energy_identity_deriv`.**  Not used: after substitution the goal
> mixes the atom `ν*grad^2` with `-2*ν*grad^2` = `(-2*ν)*grad^2`, which `linarith` does not
> recognise as the same atom.  Used `linear_combination (2:ℝ) * inner_energy_identity …`
> instead — compiles.

This does not reproduce.  `/tmp/rev131/linarith.lean` and `/tmp/rev131/linarith2.lean`
prove `inner_energy_identity_deriv`'s statement three ways with `linarith`:

```
cd verification && lake env lean /tmp/rev131/linarith.lean    → EXIT=0   (no output)
   have h := inner_energy_identity hd hmom hlap hpr hnl ; linarith
cd verification && lake env lean /tmp/rev131/linarith2.lean   → EXIT=0   (no output)
   (B) rw [hd, hexpand, hlap, hnl]; linarith          -- the from-scratch shape
   (C) linarith [h]                                    -- the term-argument shape
```

`linarith`'s preprocessing ring-normalizes, so `ν * grad ^ 2` and `-2 * ν * grad ^ 2` *are*
the same monomial to it.  `linear_combination` is a perfectly good choice and the committed
proof is fine — but per `logs/LESSONS.md` (2026-09-14, "worker 声称的编译级堵点必须由
reviewer 用 /tmp 探针复现后才能进计划" and the 073 precedent), a *false* negative example in
`ATTEMPTS` is worse than none.  **Delete or correct that bullet.**

**Finding 10 (positive — the brief's own assumption was indeed wrong, and the lane is right).**
The lane's claim that the nonlinear vanishing already exists is correct:

```
EulerOrdinarySobolev.advection_inner_zero : ∀ (A B : SmoothL2Field Space),
  (∀ x, EulerSmoothLimit.divergence A.field x = 0) → inner ℝ (advectionField A B).toLp B.toLp = 0
```

— `vendor/.../Euler/OrdinaryTransportCancellation.lean:42`, **hypotheses: two
`SmoothL2Field`s and pointwise divergence-freeness of the first, nothing else** (no compact
support, no order, no smallness).  At `A = B = u` it gives `⟪N, G⟫ = 0`, hence E0's
`hnl : ⟪G,N⟫ = 0` by `real_inner_comm`; `hdiv` is `Evolution.velocityField_solenoidal`'s
input, available from `ClassicalSolutionR.divergence`.  The vendor's own kinetic-energy
identity uses it exactly this way (`OrdinaryEulerKineticEnergy.lean:19-21`).  The lane's
namespace corrections in `ATTEMPTS` (`NSFormalization.Source.OrdinaryViscousStability.laplacian_pairing`,
`EulerOrdinarySobolev.field_directional_ibp`) are both confirmed correct by `#check`.

## 5. Recommended next C01 lane

**Primary: row E2 — the carrier-B vocabulary bridge.**  It is the one row with *no* open
input, it unblocks every physical field, and finding 3 shows it is cheaper than rated.
Exact statements (module `Section4/C01/Vocabulary.lean`, namespace `NSFormalization.Section4.C01`):

```lean
theorem toLp_inner_eq_pairing (A B : SmoothL2Field Space) :
    ⟪A.toLp, B.toLp⟫_ℝ = ∫ x, ⟪A.field x, B.field x⟫_ℝ        -- = field_inner, verbatim
theorem toLp_norm_sq_eq_l2Sq (A : SmoothL2Field Space) :
    ‖A.toLp‖ ^ 2 = ∫ x, ‖A.field x‖ ^ 2
theorem sum_directional_norm_sq_eq_gradientSq (A : SmoothL2Field Space) :
    ∑ i : Fin 3, ‖(A.directionalField (EulerOrdinarySobolev.axis i)).toLp‖ ^ 2
      = ∫ x, ‖Contracts.V1.gradientTensor A.field x‖ ^ 2
```

Inputs, all `#check`ed above: `EulerOrdinarySobolev.field_inner`
(`OrdinaryL2Integration.lean:26`), `real_inner_self_eq_norm_sq`,
`EulerLpTranslation.SmoothL2Field.directionalField_field`
(`LpSmoothFieldAlgebra.lean:97-98`, `rfl`), `PiLp.norm_sq_eq_of_L2` on
`WithLp 2 (Fin 3 → Space)`, and the definitional chain
`Contracts.V1.gradientTensor = Data.spatialGradient ∘ lift` with
`coordinateVector i = axis i` (both `EuclideanSpace.single i 1`).
Size **S–M** (~60–90 lines, no open input).  Deliver with the `Real.sqrt` adapter of
finding 4 (`grad := Real.sqrt (∑ i, ‖…‖^2)`) so the assembly can feed `laplacian_pairing`
straight into `inner_energy_identity_deriv`.

**Must start in parallel (it is the real critical path): D01 unit L9(c) — `∇p(t,·) ∈ H^∞`,
i.e. `SmoothSquareIntegrableJets (pressureGradient p t)`,** so that `∇p(t,·)` packages as a
`SmoothL2Field`.  Statement: for `w : ClassicalSolutionR ν a f T` and `t ∈ Ico 0 T`,
`∀ n, MemLp (iteratedFDeriv ℝ n (fun x => pressureGradient w.pressure t x)) 2 volume`.
Inputs: eq:Rpressure `∇p = (I−P)(f − ∇·(u⊗u))` (`02-preliminaries.tex:89-91`), `u ⊗ u ∈ H^∞`
by the registered tame products (`Contracts/V1/TameProduct.lean`), Leray boundedness on
every `H^m`, and — newly available since U05 — `Formal.r3LerayComplementL2` /
`Formal.r3HelmholtzPressure_gradient` (`vendor/HeliCorgi/Formal/R3HelmholtzPressure.lean:228,259`,
a registered root of the `Formal` library) for the `L²` level.  Size **L**.  Without it,
E0's `hpr` and the derivative path of E4 have no proof on carrier B, and the whole eq:RL2
assembly stalls — this is the single fact `ENERGY_SPLIT.md` most needs to add.

## 6. Commands run (all from the worktree, after `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`)

| command | result |
|---|---|
| `cd verification && lake build NSFormalization.Section4.C01.EnergyIdentity` | EXIT=0, "Build completed successfully (1945 jobs)." |
| `cd verification && lake env lean ../formalization/NSFormalization/Section4/C01/EnergyIdentity.lean` | EXIT=0, 0 bytes |
| `cd verification && lake env lean ../research/C01/axioms_energy.lean` | EXIT=0, both theorems `[propext, Classical.choice, Quot.sound]` |
| `make check` | EXIT=0 |
| `make test` | EXIT=0, 10123 jobs, all contracts "standard logical axioms only" |
| `grep -nE 'sorry\|admit\|axiom\|native_decide\|maxHeartbeats\|set_option' <both files>` | no hits in the Lean module |
| `cd verification && lake env lean /tmp/rev131/sign.lean` | EXIT=0 (2 `#check`, 2 positive instances, 1 refuted wrong-sign instance) |
| `cd verification && lake env lean /tmp/rev131/checks.lean` | EXIT=0 after adding the two missing imports (18 `#check`s) |
| `cd verification && lake env lean /tmp/rev131/checks2.lean` | EXIT=0 (`inner_datum_laplacian`, `…_le'`, `pressure_drop`, `vectorAngularSobolev_succ`) |
| `cd verification && lake env lean /tmp/rev131/linarith.lean`, `linarith2.lean` | EXIT=0 — **refutes the `ATTEMPTS` claim, finding 9** |
| `cd verification && lake build Euler.OrdinaryEulerKineticEnergy Euler.OrdinaryWordTime Euler.OrdinaryPressureCancellation` | EXIT=0 (4682 jobs) — needed before the vendor `#check`s |

Probes are in `/tmp/rev131/` and are volatile; the error/success text that matters is quoted
inline above (`logs/LESSONS.md`, 2026-09-14).
