# Review — lane 028, task D01: force-class closure (`ForceClass.lean`)

`…/Section4/D01/ForceClass.lean` (421 lines) at `erenup/028-D01-forceclass-closure` HEAD `d430211`,
base `erenup/integration`. Proof lane, no contract registration. Nothing was modified.

## Verdict: **accept**

Builds clean; hygienic; all 23 theorems carry exactly the three standard axioms; every restated
predicate is `Iff.rfl`/`rfl`-identical to its `Contracts.V1.Data` counterpart; and — the check that
matters — **both R42 consumer lemmas apply to the real `InsertionFamilyAPI` fields by bare term
application**, verified by building against a copy of the PR #30 contract, not by inspection. The
three rulings are sound; issues are prose-level plus one non-blocking contract-coverage
observation, none touching the Lean.

## 1. Gates

| command | result |
|---|---|
| `cd verification && lake build NSFormalization.Section4.D01.ForceClass` | **exit 0**, 9877 jobs. Warnings only from pre-existing `Source/RealSobolev`, `Paper3/SpatiallyCompactTime`, `Paper3/RealPositiveDensity`, `Paper3/RealVectorPositiveDensity`, `Paper3/SobolevDirectionalDerivative` (unused simp arg, `<;>` style, deprecated `sub_apply`/`smul_apply`, unused variable). **No warning originates in `ForceClass.lean`.** |
| `make check` | **exit 0** (plan, contract, 13 policy tests, 30 work items consistent) |
| `build_changed_lean.py --base-ref erenup/integration --dry-run` | `Changed Lean modules: NSFormalization.Section4.D01.ForceClass` — exactly the module |
| `build_changed_lean.py --base-ref erenup/integration` | **exit 0**, 9877 jobs |

Hygiene grep (`sorry|admit|native_decide|axiom |@[implemented_by|unsafe |partial def|set_option
…maxHeartbeats/skipKernelTC/debug|trust`): **no hits**. Declarations: **31** = 23 `theorem` + 6
`def` + 2 `abbrev`, matching the claim.

## 2. Axioms

Scratch `verification/Bindings/ZZScratchD01Review.lean`, `#print axioms` on all 23 theorems of §6:
every one is `[propext, Classical.choice, Quot.sound]`. No `sorryAx`, no project axiom. Scratches
and build artifacts deleted; `git status` clean.

## 3. Definitional agreement with `Contracts.V1.Data`

All seven accepted in that scratch: `rfl` for `futureTimes` (`Data.lean:113`) and
`forceTimeMeasure` (`:118`); `Iff.rfl` for `IsSobolevDatum` (`:160`, via `SmoothDatum.lean`),
`IsSobolevPath` (`:174`), `MemForceR` (`:544`), `MemForceCompact` (`:559`), `AgreesOnFuture`
(`:128`) — e.g. `example (f : Data.SpaceTimeField) : MemForceR f ↔ Data.MemForceR f := Iff.rfl`. So
the statements are the exact `Data.lean` predicates, not paraphrases. Set membership discharges
through the module too: `example (f) (h : Data.MemForceCompact f) : f ∈ Data.forceClassR :=
memForceR_of_memForceCompact h`.

## 4. Consumer shape against the *real* `InsertionFamilyAPI`

`Contracts/V1/InsertionFamily.lean` is absent here (PR #30), but its four dependencies (`Data`,
`Scaling`, `Packet`, `Correction`) are **byte-identical** to the copies here, so I copied the 027
file in, built a second scratch, then deleted both. All three shapes type-check by bare term
application — route 1 `memForceR_of_compact_difference hg (A.forceDifference_compact ε hε) :
Data.MemForceR (A.force ε)`, route 2 `memForceR_of_force_formula hg hH hF (A.force_formula ε)`, and
`memForceCompact_of_smooth_support (C.force_smooth ε hε) (C.force_compactSupport ε hε)
(C.force_positive_time ε hε) : Data.MemForceCompact (C.forceCorrection ε)`.
`forceDifference_compact` (`InsertionFamily.lean:265`) unifies with `hd` unmassaged;
`force_formula` (`:187`) has the same left-associated `g + H + F` grouping as `hform`; the three
`CorrectionAPI` fields (`Correction.lean:426,429,440`) are character-for-character the three
hypotheses of `memForceCompact_of_smooth_support`.

## 5. Mathematical rulings

**(a) `contDiff_angularPath` transport chain — sound.** Every link is genuinely bounded linear
and every `.comp` is a *definitional* composition, so the kernel checks it.
`realCompactSobolevTimeSlice` (`RealPositiveDensity.lean:54-60`) is literally `realProjectionTo s ∘
compactSobolevTimeSlice s (ofReal ∘ F)`, `realProjectionTo` (`:21`) being a real `→L[ℝ]` via
`codRestrict` onto the closed real subspace; `realVectorSlice`
(`RealVectorPositiveDensity.lean:46-49`) is `WithLp.toLp 2` of the three components, and
`(contDiff_piLp 2).mpr` is exactly the finite-product characterization; `angularRealVectorSlice`
(`AngularRealVectorBochner.lean:47-50`) is `cyclesToAngularRealVector s ∘ realVectorSlice`, that
map (`:15`) being a genuine `≃L[ℝ]`; and `I03.angularPath` (`Angular.lean:90-92`) *is*
`angularRealVectorSlice s (components F) …`, so the last step adds no content. The only analysis is
upstream `contDiff_compactSobolevTimeSlice` (`CompactSobolevTime.lean:18`); no circularity, no
vacuity.

**(b) `isSobolevDatum_add` integrability — diagnosis correct, fix sound, hypothesis genuinely
free.** Mathlib's Bochner `∫` totalizes to `0`, so `integral_add` does require both integrands
integrable; the `ATTEMPTS` §3.2 counterexample is right and no one-sided variant exists.
`SchwartzPairable` is consumed at exactly one point. Freeness chain, every link checked:
`MemForceR.2 0` gives an order-`0` datum path → `contDiff_futureSlice` makes the `t ≥ 0` slice
`Continuous` (`ContDiffOn.comp_contDiff` with `x ↦ (t,x)`, range in `Ici 0 ×ˢ univ`, so `t = 0`
needs no one-sided case) → `compactRep_cyclesComponent` (sound: `IsSobolevDatum` pairs with
*every* `ψ`, `CompactRep` only with compactly supported ones — strengthening→weakening) →
`physicalLp_ae` (`FourierPhysicalJets.lean:28`, needs only `0 ≤ s` and `Continuous`) → `MemLp _ 2
volume` → Hölder `1/2+1/2=1` via `MemLp.integrable_mul` against `SchwartzMap.memLp`. Instantiated
at `s = ((0:ℕ):ℝ)`, so `0 ≤ s` holds; `SchwartzPairable z` is order-independent, so the order-`0`
derivation serves the order-`m` addition — precisely the escape the `Data.lean:148-155`
totalization caveat anticipates.

**(c) `memForceR_add` needs no extra hypothesis — confirmed mechanically**, not by reading:
`example {f g} (hf : Data.MemForceR f) (hg : Data.MemForceR g) : Data.MemForceR (f + g) :=
memForceR_add hf hg` compiles. Both pairability arguments come from the class's own `m = 0` clause;
the `ContDiffOn ℝ ∞ f futureDomain` clause that `REVIEW_A` issue 1 forced into `MemForceR` is
load-bearing a second time here.

## 6. Reuse spot-check — 9 of 9 exact

Every cited line lands on the named declaration: `CompactSobolevTime.lean:18`,
`RealPositiveDensity.lean:21`, `AngularRealVectorBochner.lean:15`, `I03/Angular.lean:97`
(`angularPath_pairing`, character-for-character the `Data.IsSobolevDatum` pairing) and `:108`,
`AngularFourierDilation.lean:203`, `FourierPhysicalJets.lean:28`, `AngularTameProduct.lean:11` and
`:30`. No citation drifted.

## 7. `ATTEMPTS_FORCECLASS.md`

Gap claims **accurate**. (1) `ClassicalSolutionR.sobolev` (`Data.lean:643-645`) wants `ContinuousOn
G (Ico 0 T)` plus a datum at every `t ∈ Ico 0 T` for `velocity`; `u_ε` is not compactly supported
and `I03.angularPath` requires `HasCompactSupport` (`Angular.lean:59`). (2) Norms absent — the only
`forceSobolevENorm|sobolevENorm|eLpNorm` match is a docstring at line 69. (3) `F_rd` untouched. (4)
`MemForceCompact` is rightly not `AgreesOnFuture`-invariant: `CompactPositiveTimeSupport`
(`Packet.lean:134`) forces `f = 0` at `t ≤ 0` — a contract property, not a gap.

**Lane-025 name clash avoided, verified mechanically:** diffing the 31 `ForceClass` declarations
against the 37 in `025-D01-datum-to-jets/…/DatumToJets.lean` gives **zero** collisions, and zero
against the imported `SmoothDatum.lean` in the same namespace. Lane 025's `contDiff_slice` is real
(`DatumToJets.lean:366`, on `Ico 0 T ×ˢ univ`); `contDiff_futureSlice` is the right rename.

## 8. Issues, ranked

1. **(Medium, prose only) Provenance of `MemForceR g` is misstated.** `ATTEMPTS` §3 route 1 says
   the contract carries "only `Data.MemForceR g` through `ClassicalSolutionR`". It does not:
   `Data.ClassicalSolutionR` (`Data.lean:624`) has no force-class field, and neither does
   `InsertionFamilyAPI`. `g ∈ F_R` (`04-whole-space.tex:32`) must be an added hypothesis or a new
   contract field on R42's side. The Lean is unaffected — the module takes `MemForceR g` as a
   hypothesis, the right shape — but R42 cannot project it out of `reference`.
2. **(Low) Route 2 is not currently dischargeable by R42.** `memForceR_of_force_formula` needs
   `MemForceCompact (scaling.F ε)`, and `ScalingAPI.F ε = scaledForce P.force x₀ T ε = dilateField
   (ε⁻¹)^3 (ε⁻¹)^2 ε⁻¹ (T-ε²) x₀ P.force` (`Scaling.lean:115,448`). `PacketAPI` states
   `force_smooth`/`force_support` for the **unscaled** packet force only (`Packet.lean:209,214`);
   nothing transports them through `dilateField`. Not blocking — route 1 is a direct contract field
   needing nothing extra — but the docstring presents both routes as equally available. A
   `MemForceCompact (scaledForce …)` lemma is a small follow-up.
3. **(Informational)** `isSobolevDatum_add`/`isSobolevPath_add` keep `SchwartzPairable` explicit —
   correct, since at general real order there is no class to derive it from. A future `MemHInfty`
   consumer gets it free the same way (`Data.lean:152`); `F_rd` will need its own.
4. **(Nit)** `ATTEMPTS` §6 records the dry run against `--base-ref main`; re-run against `erenup/integration`, identical single-module result.

## 9. What remains for R42's lifespan clause

`InsertionLifespanAPI` (`InsertionFamily.lean:419-437`, unregistered) needs, for `lifespan :
maximalLifespanR ν a (force ε) = ofReal T`, a full `Data.ClassicalSolutionR ν a (force ε) T` plus
maximality:

* `g_ε ∈ F_R` — **closed here**, one term, given `MemForceR g` (issue 1).
* `ClassicalSolutionR.sobolev` for `u_ε` — **open**; a continuous-in-time order-`m` datum path
for a *non*-compactly-supported smooth field on `Ico 0 T`. Nothing in the tree has it and §2.1's
transport does not reach it. Now the largest remaining blocker.
* `pressure_gradient` for `p_ε` — **open**, untouched.
* `≥ T` uniqueness (`A02`), `≤ T` continuation (`A02` + `A03`), `referenceLifespan` (`A02`) —
**open**, no contract.

This lane closes one of five prerequisites — the one `research/R42/COMPARISON.md` §4.3 named first.
