# D01 unit L9(c)-partial: the pressure package — attempts and scope

Target module: `formalization/NSFormalization/Section4/D01/Pressure.lean`
(namespace `NSFormalization.Section4.D01`).
Conformance: `research/D01/axioms_l9c.lean`.

Obligation (`RECONCILIATION.md:160`, `COMPARISON_A.md:108`, unit **L9(c)**):
eq:Rpressure `∇p = (I−P)(f − ∇·(u⊗u))` — even at the `L²` (order-zero) level — and
the regularity of the pressure gradient of a classical solution.

**This lane is L9(c)-partial.**  No form of eq:Rpressure `∇p = (I−P)(f − ∇·(u⊗u))`
is proved — not the `(I−P)` identity, not even its order-zero `L²` version (the
Leray complement on whole-space physical fields is unavailable in tree; see the
gap section).  What is discharged is the projection-free part: the momentum
rearrangement, the `H^∞` regularity of the nonlinear/viscous/force slices, and
the conditional equivalence below.  L9(c) stays open in `RECONCILIATION.md` and
the work queue.  Exact consumer (C01 U3/U7,
`research/C01/COMPARISON.md:220`, `REVIEW.md:209-237`): for
`u : ClassicalSolutionR ν a f T` and `t ∈ Ioo 0 T`, the slice `∇p(t,·)` must be in
`Contracts.V1.SmoothSquareIntegrableJets` (smooth, every Fréchet jet in `L²`).

`SmoothSquareIntegrableJets`, `IsSobolevDatum`, `sobolevENorm`, `MemForceR`,
`ClassicalSolutionR` are reached through the A02/D01 restatements (defeq to the
`Contracts/V1` declarations; `NSFormalization` cannot import `Contracts`).
`SmoothSquareIntegrableJets v ↔ A05.SmoothL2 v` is `Iff.rfl` (checked in the
conformance file).

---

## Result: what closed

Everything below is `sorry`/`axiom`-free; `#print axioms` on all eleven theorems
is `[propext, Classical.choice, Quot.sound]`.

- **Step 1 — algebraic identity (unconditional).** `pressureGradient_slice_eq`:
  for `t ∈ Ioo 0 T`, `∇p = f − ∂ₜu − (u·∇)u + νΔu` pointwise.  Proof: `u.momentum`
  with `NavierStokesR3.ProblemStatement.navierStokesResidual` unfolded, then
  `rw [← h]; abel`.  This is the identity C01 re-derives at `REVIEW.md:209`.

- **Nonlinear + viscous slices are `H^∞` (discharged from the class).**
  - `laplacian_slice_smoothL2`: `Δu(t,·) = ∑ᵢ ∂ᵢ∂ᵢu(t,·)`; each `∂ᵢ∂ᵢu` by two
    `A05.SmoothL2.dir` on the velocity slice, three-term sum by `smoothL2_add`.
    The field identity `spatialLaplacian u t · = ∑ᵢ dirDeriv i (dirDeriv i us)`
    closes by `simp only [spatialLaplacian, Fin.sum_univ_three]; rfl`.
  - `advection_slice_smoothL2` / `advectionOf_smoothL2`: `(u·∇)u(t,·)` in the jet
    class.  `ContDiff` by `ContDiff.clm_apply` on `fderiv us` and `us`; each jet
    in `L²` because `A03.advectionTame m hm2 hus hus` bounds
    `sobolevENorm m (advectionOf us us)` by a finite quantity for every `m ≥ 2`
    (the four factors are `≠ ⊤` via `sobolevENorm_ne_top_of_contDiff_memLp` and
    `A03.columnsSobolevENorm_le_sum` + `ENNReal.sum_ne_top`), which yields an
    order-`m` datum (`exists_isSobolevDatum_of_sobolevENorm_ne_top`), and
    `DatumToJets.memLp_iteratedFDeriv_of_isSobolevDatum` turns the order-`m` datum
    into the order-`j` jet for every `j ≤ m` (take `m = max n 2`).
    `advection u.velocity t · = A03.advectionOf us us` holds by `rfl`.

- **Velocity slice.** `velocity_slice_smoothL2` = `smoothSquareIntegrableJets_slice`
  (`DatumToJets`) fed with `velocity_smooth` + `sobolev`.

- **Force slice from `MemForceR`.** `forceSlice_smoothL2_of_memForceR`: `f(t,·)`
  in the jet class for `t ≥ 0`.  `ContDiff` reuses `D01.contDiff_futureSlice`
  (`ForceClass.lean:301`) on `ContDiffOn ℝ ∞ f futureDomain`
  (`futureDomain = Ici 0 ×ˢ univ`); the datum at each order `m` is `G t` from the
  `IsSobolevPath` field of `MemForceR`, then `memHInfty_jets`.

- **The conditional equivalence (main theorem) and its packaging.**  All stated
  in the contract spelling `SmoothSquareIntegrableJets` (hypotheses and
  conclusions), so a consumer holding the contract class applies them with no
  transport.
  - `pressureGradient_slice_smoothL2_of`: given `f(t,·)` and `∂ₜu(t,·)` in the
    jet class, then `∇p(t,·)` is — advection and Laplacian discharged internally,
    combined by `smoothL2_add`/`smoothL2_sub`/`smoothL2_const_smul` through
    `pressureGradient_slice_eq`.
  - `temporalDerivative_slice_smoothL2_of`: the symmetric converse, from `f(t,·)`
    and `∇p(t,·)` to `∂ₜu(t,·)`, through `temporalDerivative_slice_eq`.
  - `pressureGradient_slice_smoothL2_iff_temporalDerivative`: for `MemForceR f`,
    `SmoothSquareIntegrableJets (∂ₜu(t,·)) ↔ SmoothSquareIntegrableJets (∇p(t,·))`.
    This is a **repackaging** of the pressure-regularity obligation C01 books as
    **P2**, *not a reduction of the Leray gap*: the two sides are interderivable
    in one line each way through `momentum`, so the net new content is the three
    `H^∞`-slice lemmas.
  - `pressureGradient_slice_smoothSquareIntegrableJets`: the forward `.mp`
    corollary, kept for consumers that want it.  Conclusion is literally
    `SmoothSquareIntegrableJets (fun x => pressureGradient u.pressure t x)`, the
    C01 target.

New reusable helpers: `smoothL2_add`, `smoothL2_sub`, `smoothL2_neg`,
`smoothL2_const_smul` (additive/scalar closure of `A05.SmoothL2`; a grep of
`formalization` and `verification` for `smoothL2_add|smoothL2_sub|smoothL2_neg|
smoothL2_const_smul|SmoothL2.add|SmoothL2.sub|SmoothL2.neg|SmoothL2.const_smul`
returns only this lane — the class had only *derivative* closure `A05.SmoothL2.dir`
before), and `exists_isSobolevDatum_of_sobolevENorm_ne_top`.  Also
`temporalDerivative_slice_eq` and the converse packaging
`temporalDerivative_slice_smoothL2_of`, giving the `Iff`
`pressureGradient_slice_smoothL2_iff_temporalDerivative`.

---

## The single root gap, precisely

The unconditional statement "`SmoothSquareIntegrableJets (∇p(t,·))` for every
`ClassicalSolutionR ν a f T`" is **false**.  `ClassicalSolutionR` gives `u` an
`H^m` datum at every order (`sobolev`), smoothness on the slab, `div u = 0`, and
`∇p(t,·) ∈ L²` at order **zero only** (`pressure_gradient`); nothing constrains
`f` (it is a bare parameter fixed by `momentum` on `Ioo 0 T`) or gives `∂ₜu` /
`∇p` a datum at positive order.  Counterexample: pick smooth divergence-free `u`
with all slices `H^∞`, a smooth scalar `p` with `∇p ∈ L² \ H¹`, and *define* `f`
by the momentum equation; every field holds and `∇p(t,·) ∉ SmoothSquareIntegrableJets`.
So a force hypothesis is mandatory; `DatumToJets.contDiff_pressureGradient_slice:504`
already records that only spatial smoothness of `∇p(t,·)` is cheap.

With `MemForceR f`, write `h := f − (u·∇)u + νΔu`; then `h ∈ H^∞` (force slice by
`forceSlice_smoothL2_of_memForceR`, advection and Laplacian by this module), and
`momentum` gives `∂ₜu + ∇p = h`.  Here `∂ₜu` is solenoidal (`div ∂ₜu = ∂ₜ div u = 0`)
and `∇p` is a gradient, both `L²` at order 0 (`∇p` from the class, `∂ₜu = h − ∇p`).
By uniqueness of the Helmholtz/Leray decomposition in `L²`, `∂ₜu = P h` and
`∇p = (I−P)h`, and `(I−P)` bounded on every `H^m` gives `∇p ∈ H^∞` — this is
eq:Rpressure (`(u·∇)u = ∇·(u⊗u)` for `div u = 0`).

**Exact missing lemma(s).**  Closing the gap — proving eq:Rpressure and
discharging `∂ₜu(t,·) ∈ SmoothSquareIntegrableJets` — needs, on `Space → Space`
in the manuscript's **angular** convention:

- (i) the `L²` Helmholtz/Leray **decomposition itself**, `L² = L²_σ ⊕ G` with its
  projection `P` — absent in tree for whole-space angular fields;
- (ii) placing the pointwise-solenoidal `∂ₜu(t,·) ∈ L²` into the *closed*
  solenoidal subspace `L²_σ`, i.e. `IsSolenoidal z ∧ MemLp z 2 → z ∈ L²_σ`, which
  is D01 unit **L3** (`RECONCILIATION.md` L3 row, booked separately and open);
- (iii) `div ∂ₜu = ∂ₜ div u` (routine from `velocity_smooth`, but unproved in
  tree), so that `∂ₜu` is solenoidal;
- (iv) `(I−P)` bounded on every `H^m` (a zero-order Fourier multiplier), for the
  `H^∞` upgrade.

The `∂ₜu(t,·) ∈ SmoothSquareIntegrableJets` hypothesis and
`∇p(t,·) ∈ SmoothSquareIntegrableJets` are interderivable given `f, (u·∇)u, νΔu`
are `H^∞` (through `momentum`), and the `Iff`
`pressureGradient_slice_smoothL2_iff_temporalDerivative` names this — so the
hypothesis/root-gap framing is about that one input.  No `L²` order-0 form of
`(I−P)` on whole-space physical angular fields exists in the main tree, so even
the fallback "`∇p(t) = (I−P)(f − ∇·(u⊗u))` in `L²`" of the task is blocked by
(i) + the HeliCorgi bridge (below): producing it would require importing the
HeliCorgi operator and identifying its distributional gradient with our classical
`pressureGradient`.

**The in-tree Leray inventory.**  There *are* Leray projections in tree, but only
periodic ones, which do not transfer: `Source.ForcedCylinderLocal.leray`
(`ForcedCylinderLocal.lean:26`) is a CLM `SobolevSpace period q →L[ℝ] SobolevSpace period q`
(carrying "`(I−P)` bounded on `H^q`" at the periodic scale), and
`Paper1.PeriodicLeray{CoeffCore,Divergence,WeightedNorm,…}` carry the periodic
Fourier correction.  Both are periodic / cylinder.  The **only whole-space-`ℝ³`
Leray construction in tree is HeliCorgi's** (below).

---

## What the HeliCorgi port offers, and why it does not close the gap here

The U05 port (`Section4/HeliCorgiPort.lean`, `formalization` `Formal` library,
compiles at this pin — Lean 4.34.0-rc2) exposes:

- `MNS2.r3LerayComplementL2 (F : R3L2Velocity) : R3L2Velocity := F − r3LerayL2Operator F`
  (`vendor/HeliCorgi/Formal/R3HelmholtzPressure.lean:228`), the `L²` Leray
  complement `(I−P)F`, with `fourier_r3LerayComplementL2_ae` its frequency symbol.
- `MNS2.r3HelmholtzPressure (F : R3L2Velocity) : 𝓢'(R3, ℂ)` (`:223`) and
  `MNS2.r3HelmholtzPressure_gradient (F) (j) :`
  `∂_{r3StdBasis j} (r3HelmholtzPressure F) = −(postcomp (proj j) ((r3LerayComplementL2 F : R3L2Velocity) : 𝓢'(R3, R3C)))`
  (`:259`), i.e. `∇p = −(I−P)F` componentwise **in `𝓢'`**, for an arbitrary `L²`
  source `F` (its own docstring flags "edge 2a only: nothing identifies `F` with
  `(u·∇)u`").

Why it is not directly usable as the missing lemma:

1. **Convention.** HeliCorgi uses the cycles Fourier transform `𝓕`
   (`e^{-2πi⟨x,ξ⟩}`); Section 4 / D01 use the manuscript's angular
   `angularRealization` (`(2π)^{-3/2}∫ e^{-i x·ξ}`).  Transport costs the tracked
   `(2π)`-factors (as in `DatumToJets`).
2. **Distributional vs classical.** `r3HelmholtzPressure_gradient` is stated for
   the tempered line-derivative `∂_{r3StdBasis j}` of a `𝓢'` object; the target is
   the classical pointwise `pressureGradient p t x` on `EuclideanSpace ℝ (Fin 3)`.
   Identifying the two needs the distributional-to-classical derivative bridge for
   a smooth `L²`-jet field.
3. **Type / real-vs-complex.** `R3L2Velocity` is HeliCorgi's complex-valued `L²`
   velocity (`R3C`); the manuscript field is real `Space → Space`.  The
   `R3LerayRealLinearBridge` is the intended real-linear adapter but was not
   wired to `pressureGradient` here.
4. **Order.** The statement is `L²` (order 0).  The consumer needs `H^m` at every
   `m`; the port has no `(I−P) : H^m → H^m` boundedness.

Assembling (1)–(4) into
`pressureGradient p t · = (I−P)(f(t) − ∇·(u⊗u)(t))` and its `H^m` upgrade is a
self-contained follow-up unit (a real-linear + convention + distributional↔classical
bridge, then the multiplier bound); it is the exact remaining work and is what
`RECONCILIATION.md:160` L9(c) marks as "gap … reusable at the distributional level
as HeliCorgi".

---

## Commands

From `WT/verification` (`. ../scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`):

- `lake build NSFormalization.Section4.D01.Pressure` → `Build completed successfully`.
- `lake env lean ../research/D01/axioms_l9c.lean` → all six theorems
  `[propext, Classical.choice, Quot.sound]`; the `SmoothSquareIntegrableJets ↔
  A05.SmoothL2` `Iff.rfl` example typechecks.

### Failed / rejected approaches

- **Unconditional `∇p(t,·) ∈ H^∞` from the class alone** — impossible (the
  counterexample above); needs a force hypothesis.  Not attempted in code.
- **Deriving `∂ₜu(t,·) ∈ H^∞` from the class + `MemForceR f`** — blocked: it is
  the Leray/Helmholtz `H^m` regularity, absent in tree (see the gap section).
  Kept as the one hypothesis of the main theorem.
- **`simp only [spatialLaplacian, spatialDerivative, A05.dirDeriv, Fin.sum_univ_three]`
  to close the Laplacian field identity** — left an unsolved defeq goal because
  the `A05.dirDeriv` equation lemma does not fire on the unapplied
  `A05.dirDeriv i us` under `fderiv`.  Fixed by `simp only [spatialLaplacian,
  Fin.sum_univ_three]; rfl` (letting the kernel discharge the `spatialDerivative`/
  `dirDeriv`/`us` unfolding definitionally).

---

## Review fixes (applied after `research/D01/REVIEW_L9C.md`, ACCEPT-WITH-NOTES)

The reviewer rebuilt the counterexample `sorry`-free and confirmed it; all
findings were bookkeeping/presentational (no correctness defect).  Applied:

1. **Finding 2 (LOW) — `Iff`.**  Added `temporalDerivative_slice_eq`,
   `temporalDerivative_slice_smoothL2_of`, and the main theorem
   `pressureGradient_slice_smoothL2_iff_temporalDerivative`
   (`∂ₜu(t,·) ∈ H^∞ ↔ ∇p(t,·) ∈ H^∞` for `MemForceR f`).  Docstring states it is a
   repackaging of obligation **P2**, not a reduction of the gap.  The forward
   `pressureGradient_slice_smoothSquareIntegrableJets` is now the `.mp` corollary.
2. **Finding 3 (LOW) — Leray inventory.**  The Lean docstring no longer says "the
   only in-tree Leray construction is HeliCorgi's"; it now records the periodic
   `Source.ForcedCylinderLocal.leray` (`:26`, a CLM on `SobolevSpace period q`)
   and `Paper1.PeriodicLeray*`, and narrows the claim to "the only whole-space-`ℝ³`
   Leray construction in tree is HeliCorgi's".  Same fix in this note.
3. **Finding 4 (LOW) — reuse.**  `forceSlice_smoothL2_of_memForceR` now imports
   `NSFormalization.Section4.D01.ForceClass` and calls `contDiff_futureSlice hf.1 ht`
   (`ForceClass.lean:301`) instead of re-proving the slice smoothness.
4. **Finding 5 (LOW) — citations.**  `r3LerayComplementL2` at `:228` (was 224),
   `r3HelmholtzPressure` at `:223` (was 218); the additive-closure novelty is now
   backed by the grep result rather than the (derivative-closure) passage at
   `A03/SmoothJets.lean:40-43`; consumer named "U3/U7".
5. **Finding 6 (LOW) — vocabulary.**  All public `Space → Space` lemmas now use
   the contract spelling `SmoothSquareIntegrableJets` in both hypotheses and
   conclusions; only the general-`F` closure helpers stay `A05.SmoothL2` (the
   `SmoothSquareIntegrableJets` name is `Space → Space`-only).  They are defeq, so
   the closure helpers apply to the contract-spelled terms without transport.
6. **Findings 1, 7 (MEDIUM/LOW) — scope.**  Header and prose now read
   **L9(c)-partial**: no form of eq:Rpressure (even order-0 `L²`) is proved; L9(c)
   stays open.  The gap section names (i) the `L²` Helmholtz decomposition in the
   angular convention, (ii) unit **L3** (`IsSolenoidal ∧ MemLp 2 → L²_σ`), (iii)
   `div ∂ₜu = ∂ₜ div u`, (iv) `(I−P)` on `H^m`.
7. **Finding 8 (merge gate).**  The branch is behind integration; the lead will
   rebase before merge (`check_contracts --base-ref` staleness on
   `Contracts/V2/DatumLemmas.lean`, which this lane does not touch).

### Commands after the fixes (from `WT/verification`, `LEAN_NUM_THREADS=6`)

- `lake build NSFormalization.Section4.D01.Pressure` → `Build completed successfully (9886 jobs)`.
- `lake env lean ../research/D01/axioms_l9c.lean` → all **11** theorems
  (`pressureGradient_slice_eq`, `temporalDerivative_slice_eq`,
  `velocity_slice_smoothL2`, `laplacian_slice_smoothL2`, `advectionOf_smoothL2`,
  `advection_slice_smoothL2`, `forceSlice_smoothL2_of_memForceR`,
  `pressureGradient_slice_smoothL2_of`, `temporalDerivative_slice_smoothL2_of`,
  `pressureGradient_slice_smoothL2_iff_temporalDerivative`,
  `pressureGradient_slice_smoothSquareIntegrableJets`) report
  `[propext, Classical.choice, Quot.sound]`; the `SmoothSquareIntegrableJets ↔
  A05.SmoothL2` `Iff.rfl` example typechecks.
- `make check` → exit 0.
