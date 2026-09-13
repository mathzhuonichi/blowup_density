# C01 units U1 & U3 — attempts and outcomes (lane 050)

Worktree `.claude/worktrees/050-C01-units-u1-u3`. New modules:
`formalization/NSFormalization/Section4/C01/VelocityJets.lean` (U1),
`.../C01/Evolution.lean` (U3). Conformance/audit: `research/C01/axioms_u1u3.lean`.
No `sorry`/`axiom`/`native_decide`; every public theorem audits to
`[propext, Classical.choice, Quot.sound]`.

## U1 — `velocityJets` (was rated L, now S)

**Target.** `research/C01/Spec.lean:295-300`: for `u : ClassicalSolutionR ν a f T`
and `t ∈ Ico 0 T`, `MemHInfty (slice u.velocity t) ∧ SmoothSquareIntegrableJets (slice u.velocity t)`.

**Why it was L, why it is now S.** `COMPARISON.md:171` rated U1 `L` because D01 unit
L2's *datum ⟹ jet* direction was open (`BoundedRepresentative.lean:71-74`). Lanes
020/025 closed it: `D01.smoothSquareIntegrableJets_slice` (`DatumToJets.lean:396`)
produces the jet form of a velocity slice from `velocity_smooth` + the datum half
of `sobolev`, and `D01.memHInfty_iff_smoothSquareIntegrableJets` (`DatumToJets.lean:298`)
recovers the datum form. Both are bound into the merged contract
`D01.datum_lemmas` (`Bindings/DatumLemmas.lean`) as `solution_slice_smoothJets` /
`memHInfty_iff_smoothJets`.

**Proof (final).** `velocity_slice_memHInfty_and_smoothL2`:
```
have hjets := D01.smoothSquareIntegrableJets_slice u.velocity_smooth
                (fun m => (u.sobolev m).imp fun _ h => h.2) ht
exact ⟨D01.memHInfty_iff_smoothSquareIntegrableJets.mpr hjets, hjets⟩
```
The `.imp fun _ h => h.2` discards the `ContinuousOn G` conjunct of `sobolev`,
exactly the hypothesis shape `smoothSquareIntegrableJets_slice` asks for; this is
also how the binding discharges `solution_slice_smoothJets`.

**Vocabulary / rfl bridges.** The formalization module states the conclusion with
the canonical local restatements `A02.MemHInfty` (`Section4/A02/SolutionClass.lean:74`)
and `A05.SmoothL2` (`Section4/A05/SmoothJets.lean:44`). Both are *definitionally*
the contract predicates (`Data.MemHInfty` = `ContDiff ∧ ∀ m, ∃ A, IsSobolevDatum …`;
`SmoothSquareIntegrableJets` = `ContDiff ∧ ∀ n, MemLp (iteratedFDeriv n) 2`), so the
conformance `example` in `research/C01/axioms_u1u3.lean` discharges by a single
`exact`, after converting the *contract* `ClassicalSolutionR` into the A02 one
field-by-field (`toA02`; a `rfl` bridge is impossible for the structure itself, two
separately declared structures being distinct inductive types, but every field type
is defeq so the copy typechecks). Conformance compiles with no error.

**Failed / rejected approaches.**
* Discharging the conformance example directly by the bound `datumLemmas` API was
  rejected: the task wants it discharged by *my* theorem, and routing through
  `toA02 w + velocity_slice_…` keeps a single owner for the clause.
* First build failed with `Space` resolving to the wrong namespace (a `Space` from
  another open); fixed by `open NavierStokes.ProblemStatement`.

## U3 — evolution packaging (M; provable core closed, two clauses left open)

**Target (task).** Package `u : ClassicalSolutionR ν a f T` on `[0,S] ⊂ [0,T)`
(`S < T`) as `Icc 0 S → EulerLpTranslation.SmoothL2Field Space`
(`Euler/LpSmoothField.lean:31`) with the hypotheses the vendor energy machinery
consumes: `jetLp` continuity in time (`hWc`/`hA`), pointwise time-derivative
(`hTime`/`hd`), `u(t) ∈ solenoidalSpace` (`hW`), `∇p(t) ∈ gradientSpace` (`hP`).

**The real C01 consumer is `wordEnergy_hasDerivWithinAt`, not `difference_energy_bound`.**
`COMPARISON.md:173` cites `difference_energy_bound:71` only as evidence that "the shape
is proven usable"; the U4/U7 consumers it actually names are
`EulerOrdinarySobolev.wordEnergy_hasDerivWithinAt` (`Euler/OrdinaryWordTime.lean:86`) and
`ordinaryWord_hasDerivWithinAt` (`:78`), whose hypothesis package is **only** `hA`
(jetLp continuity of the path), `hB` (jetLp continuity of the derivative path) and `hd`
(pointwise `HasDerivAt`) — **no** `hK`, `hdiv`, `hW`, `hP`. The pressure enters U4/U7 not as
`hP` but through the pressure-cancellation lemmas, where `EulerOrdinarySobolev.gradient_mem`
(`Euler/OrdinaryPressureCancellation.lean:84`) consumes the `SmoothL2Field` structure on
`∇p`. So `difference_energy_bound` is a *shape witness* here, and the hypotheses U3 actually
owes the real consumer are the path-side `hA`/`hW` (closed below for the velocity) plus the
derivative-side `hB`/`hd`.

**Read of `difference_energy_bound`.** Its full hypothesis package is four paths
`U W P D : Icc 0 T → SmoothL2Field Space`, `hWc`/`hDc` (jetLp-continuity of `W`/`D`),
`hTime` (pointwise `HasDerivAt` of `W.field` with derivative `D.field`), `hK`, `hdiv`,
`hW` (`W.toLp ∈ solenoidalSpace`), `hP` (`P.toLp ∈ gradientSpace`), and `hD` tying
`D` to `differenceRhs + ν • laplacianField`. For C01's single forced solution the
relevant sub-package is the velocity path with `hWc`, `hTime`, `hW` and the pressure
`hP`.

**Proved (Evolution.lean).**
1. `velocityField u hST t : SmoothL2Field Space`, field `= fun x => u.velocity (t.1, x)`,
   with `smooth`/`integrable` supplied by U1's `velocity_slice_smoothL2`. Well-defined
   because `t ≤ S < T` puts `t.1 ∈ Ico 0 T` (`mem_Ico_of_mem_Icc`).
2. `velocityField_field` — the representative is literally the velocity slice (`rfl`).
3. `velocityField_solenoidal` (clause `hW`): `(velocityField t).toLp ∈ solenoidalSpace`.
   Route: `EulerMeanSolenoidal.smooth_mem_solenoidal` (`MeanSolenoidalSpace.lean:187`)
   from `ClassicalSolutionR.divergence`, with the divergence bridge
   `spatialDivergence u.velocity t x = EulerSmoothLimit.divergence (u(t,·)) x`
   discharged by `EulerSmoothLimit.divergence_eq_coordinate_sum` and unfolding
   `spatialDivergence`/`spatialDerivative`/`coordinateVector` — the two divergences are
   the *same* coordinate sum (`coordinateVector i := EuclideanSpace.single i 1`).
4. `jetOfDatum_continuous` + `velocityField_jetLp_continuous` (clause `hWc`):
   `∀ n, Continuous (fun t : Icc 0 S => (velocityField t).jetLp n)`. **This is the clause
   the task flagged as possibly needing more than `sobolev`'s `ContinuousOn`; it is
   closed for the velocity.** `D01.jetOfDatum n n (le_refl n)` reconstructs the order-`n`
   `L²` jet from the datum and is continuous because it is `Source.physicalJetLp n`
   (`→L[ℝ]`) applied componentwise to `Paper3.sobolevOrderLowering` (`→L[ℂ]`) of
   `(Paper3.cyclesToAngular n).symm` (`≃L[ℂ]`) of the closed-`L²`-subspace coercion
   (`continuous_subtype_val`) of the `PiLp` component (`PiLp.continuous_apply 2 _ i`) —
   every stage continuous. `(velocityField t).jetLp n = jetOfDatum n n _ (G_n t.1)` as
   `Lp` elements by `D01.jetOfDatum_ae` + `MemLp.coeFn_toLp` + `Lp.ext`, and the
   order-`n` datum path `G_n` of `sobolev` is `ContinuousOn (Ico 0 T)`, transported to
   the subtype by `ContinuousOn.comp_continuous continuous_subtype_val`.

**The gap: ONE root gap — the all-order jets of `∇p(t,·)`.** The time-derivative
clause is **not** an independent gap; it reduces to this one plus routine work.

* **Root gap: `SmoothSquareIntegrableJets (∇p(t,·))` (i.e. `∇p(t,·)` an `SmoothL2Field`).**
  Both `EulerOrdinarySobolev.gradient_mem` (`OrdinaryPressureCancellation.lean:84`, the
  `gradientSpace`/pressure-cancellation consumer) and the derivative field below need
  `∇p(t,·)` to have **every Fréchet jet in `L²`**. The class *as written* supplies only
  order-zero `MemLp` of `∇p` (`ClassicalSolutionR.pressure_gradient`, `Data.lean:647`) and
  spatial smoothness of the slice (`D01.contDiff_pressureGradient_slice`,
  `DatumToJets.lean:504`), so this lane does **not prove** `∇p(t,·)` an `SmoothL2Field`.

  **This is a theorem of the paper's class, not a hypothesis to add.**
  `paper/sections/02-preliminaries.tex:89-91` specifies the whole-space pressure gradient
  by eq:Rpressure `∇p = (I−P)(f − ∇·(u⊗u))`, elliptic form **`Δp = div f − ∂ᵢ∂ⱼ(uᵢuⱼ)`**
  (note the force term — the unforced `−Δp = div((u·∇)u)` is wrong for C01, which is the
  *forced* theory). Since `u(t) ∈ H^∞` (class, `:29-30`) and `f(t) ∈ H^∞` (`F_R`), the
  `H^m` algebra gives `u⊗u ∈ H^∞`, the Leray projection is bounded on every `H^s` and
  commutes with derivatives (`:80-81`), so `∇p(t,·) ∈ H^∞`, which by `memHInfty_iff_smoothJets`
  is exactly `SmoothSquareIntegrableJets (∇p(t,·))`. `Data.lean:621-623` deliberately omits
  eq:Rpressure as a field ("for a smooth solenoidal solution it follows from `momentum` and
  `divergence` with `∇p ∈ L²`; deriving it is a lemma") and books it as **D01 unit L9(c)**.

  **Owner and blocker.** Unit **L9(c)** (`research/D01/RECONCILIATION.md:160`,
  `COMPARISON_A.md:105`, `REVIEW_DATUM_TO_JETS.md:148`, `ATTEMPTS_DATUM_TO_JETS.md:280`):
  eq:Rpressure at the `L²` level, reusable from HeliCorgi `MNS2.r3HelmholtzPressure_gradient`
  (`vendor/HeliCorgi/Formal/R3HelmholtzPressure.lean:259`) and `r3LerayComplementL2` (`:228`),
  **blocked on toolchain task U05** (HeliCorgi is Lean 4.32.1, this project 4.34.0-rc2). L9(c)
  gives eq:Rpressure at order zero; the *all-order jet* statement additionally needs `(I−P)`
  bounded on every `H^m` and the `H^∞` algebra for `u⊗u` (tame products,
  `Contracts/V1/TameProduct.lean`).

  **Rejected: a D01-V2 pressure-datum class field.** Adding `∇p`'s Sobolev data as a new
  `ClassicalSolutionR` field would make the Lean class **strictly stronger than the paper's**
  (fewer solutions satisfy it, and the burden moves onto whoever *constructs* a solution,
  prop:local). The elliptic-regularity route (L9(c) + `H^m` algebra) is the only honest one.

* **Pointwise time-derivative (clause `hTime`/`hd`) reduces to the root gap.** Not
  independent. `ClassicalSolutionR.momentum` (`Data.lean:640`) pins the time derivative
  **algebraically** on `Ioo 0 T` — exactly where `hTime` is demanded — via
  `navierStokesResidual ν u p t x = temporalDerivative u t x + advection u t x
  − ν • spatialLaplacian u t x + pressureGradient p t x` (`NavierStokes/R3/ProblemStatement.lean:57-62`,
  `temporalDerivative u t x = fderiv ℝ (fun s => u (s,x)) t 1`): so
  `∂_t u = f − (u·∇)u + νΔu − ∇p`. The `HasDerivAt` in time comes from `velocity_smooth`'s
  `ContDiffOn ℝ ∞ u (Ico 0 T ×ˢ univ)` (with `projIcc` bookkeeping); jet-continuity of the
  summands `f`, `(u·∇)u`, `Δu` is within reach of `sobolev`'s `ContinuousOn` conjunct (now
  usable via `velocityField_jetLp_continuous`) plus tame products. The **only** summand not
  yet all-order `L²` is `∇p` — so this clause = root gap + routine work.

  **Force caveat for U4 (do not inherit an off-by-force `D`).** In the shape witness
  `difference_energy_bound`, `hD` with `U := 0`, `P := ∇p` forces
  `D = differenceRhs 0 W (∇p) + νΔW = −(u·∇)u − ∇p + νΔu`, which by `momentum` equals
  `∂_t u − f`, **not** `∂_t u`. That estimate is the *unforced* one; a forced solution's
  derivative field is `∂_t u`, off by `f`. U4 must use `∂_t u` (from `momentum`), not the
  `difference_energy_bound` `D`, unless `f = 0`.

**Failed / rejected approaches for U3.**
* Building the `∇p` `SmoothL2Field` from `pressure_gradient` alone: blocked, it is order-zero
  `MemLp` only. The honest route is L9(c) + the `H^m` algebra (above), not a stronger class field.
* Writing the elliptic relation without the force (`−Δp = div((u·∇)u)`): wrong for C01;
  corrected to `Δp = div f − ∂ᵢ∂ⱼ(uᵢuⱼ)` (eq:Rpressure).
* Treating the time-derivative as an independent gap needing its own datum: wrong; `momentum`
  supplies `∂_t u`, so it collapses to the pressure gap.
* Proving `jetLp` continuity via a Lipschitz bound from `D01.norm_jetOfDatum_le`
  (would need `jetOfDatum` bundled as a `LinearMap`/`ContinuousLinearMap`, hitting the
  ℝ-vs-ℂ realification of `cyclesToAngular`). Rejected in favour of the direct
  composition-of-continuous-maps proof, which needs only `.continuous` of each CLM/CLE
  plus `PiLp.continuous_apply` and `continuous_subtype_val` (both found by `exact?`).

## Commands
* Seed: `bash scripts/lean-install.sh` → `== OK`.
* `cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.C01.VelocityJets` → built.
* `… lake build NSFormalization.Section4.C01.Evolution` → built (imports VelocityJets).
* `… lake env lean ../research/C01/axioms_u1u3.lean` → conformance example accepted; all 8
  public theorems `[propext, Classical.choice, Quot.sound]`.

## Review fixes (lane 050, `research/C01/REVIEW_U1U3.md`, ACCEPT-WITH-NOTES)

Docs-only, no code change; `lake env lean` on `Evolution.lean` stayed silent (exit 0)
after the header edit, and the eight `#print axioms` are unchanged.

* **Finding 4 (stale header).** `Evolution.lean` header rewritten: "What is proved here"
  now lists all five deliverables (adds `jetOfDatum_continuous` and
  `velocityField_jetLp_continuous`); removed the sentence claiming the `jetLp`-continuity
  ingredients "neither exist in tree today" — the file proves that clause.
* **Finding 1 (time derivative not independent).** Header and this file now state the ONE
  root gap (all-order jets of `∇p`); the time-derivative clause reduces to it because
  `momentum` pins `∂_t u = f − (u·∇)u + νΔu − ∇p` on `Ioo 0 T`. Recorded the force caveat:
  with `U := 0`, `P := ∇p`, `difference_energy_bound`'s `hD` forces `D = ∂_t u − f` (unforced),
  so U4 must read `∂_t u` off `momentum`, not off that `D`.
* **Finding 2 (V2-datum branch rejected).** Dropped the "or a Sobolev datum for `∇p` at every
  order / D01 V2 pressure-datum clause" alternative; recorded that eq:Rpressure is a *theorem*
  of the paper's class and that a V2 class field would make the Lean class stronger than the paper's.
* **Finding 3 (named owner).** The gap is unit **L9(c)** (`RECONCILIATION.md:160`,
  `COMPARISON_A.md:105`), blocked on toolchain task **U05**; the all-order jets additionally
  need `(I−P)` bounded on every `H^m` + the `H^∞` algebra for `u⊗u` (tame products).
* **Finding 5 (force in the elliptic relation).** Corrected `−Δp = div((u·∇)u)` to
  `Δp = div f − ∂ᵢ∂ⱼ(uᵢuⱼ)` (eq:Rpressure with the force).
* **Finding 6 (real consumer).** Named `wordEnergy_hasDerivWithinAt` /
  `ordinaryWord_hasDerivWithinAt` (`OrdinaryWordTime.lean:86,78`) as C01's actual U4/U7
  consumer (package: `hA`, `hB`, `hd` only); `difference_energy_bound` is the shape witness.
* **Finding 7 (obsolete rating).** U1 is now **S, closed** in three lines; `COMPARISON.md:171`'s
  `L` rating and its "D01 unit L2 direction open" cell are obsolete and should be updated to
  S at merge (D01's datum ⟹ jet direction is closed and bound as `solution_slice_smoothJets` /
  `memHInfty_iff_smoothJets`).
