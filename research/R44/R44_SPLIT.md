# R44 — Proposition 4.4 proof-route split (`prop:Rcritical2`)

Paper statement `paper/sections/04-whole-space.tex:136-144`; proof `:145-174`.
Reconciled API `research/R44/Spec.lean`
(`BlowupDensity.R44.Draft.RCritical2API`, nine fields); source gap table
`research/R44/COMPARISON.md` §4; decisions `RECONCILIATION.md`.

This table distinguishes the registered contract registry from research specs.
“Blocks stating” below means either the final nine-field R44 API or a clean
PDE-level intermediate.  The final API itself is already fully statable from
`Contracts.V1.Data`; all remaining hard items block its proof/binding, not its
well-formedness.

Lean delivered in this lane is
`NSFormalization.Section4.R44.Pieces`: three R44-specific scalar/constant
theorems.  The identical `ℝ≥0∞` power pin and C01 gate discharge are reused from
`R43.Pieces`, not copied.

## 0. Registration audit at this branch

`verification/contracts.json` has 26 entries.  The relevant scopes are:

| need | registry result | exact registered supply / exclusion |
|---|---|---|
| finite `L²_t H^{-1/2}` norm for `f ∈ 𝓕_ℝ` | **registered** | `D01.datum_lemmas_v2`, **V2**, field `forceSobolevENorm_ne_top`, with `s := -1/2`, `m := 0`, `q := 2`; inherited by `D01.datum_lemmas_v3`, V3 |
| C01 constant `C₁`, `criticalL3`, and the exact `ℝ≥0∞` nonlinear gate vocabulary | **registered** | `C01.energy_absorption_partial`, **V1**, fields `C₁`, `C₁_pos`, `trilinearAbsorbed`; this does not include eq:RH1 |
| ordinary energy bound eq:RL2 | **registered** | `C01.energy_absorption_partial_v3`, **V3**, field `l2Bound` (and `energyDifferentialBound`) |
| eq:RH1, `sobolevTwoFourier`, `h2TimeIntegralZeroDatum` | **not registered** | expressly excluded by the V3 scope; these are proposed **C01 V4** fields (`research/C01/Spec.lean:532,555,599`) |
| `‖u‖₃ ≤ Cemb‖u‖_{H^{1/2}}`, derivative/J `L³` embeddings | **not registered** | `A05.gradient_l6`, **V1**, contains only `gradientLSix`; the critical clauses in `research/A05/Spec.lean:366,384,406` require **A05 V2** |
| continuation `extendsBeyond` at finite `S` | **not proved or registered on this branch** | `A04.energy_high_partial_v2`, **V2**, stops at `highContinuationIntegral`; `extendsBeyond` is the proposed **A04 V3** field (`research/A04/Spec.lean:613`) |
| maximal solution family | **registered, conditional** | `A02.maximal_partial_v2`, **V2**, field `exists_maximal`; its A01 local-solution clause remains an explicit hypothesis |
| `J`, exact Bessel-weight identity, `H^{-1/2}` duality | **proved locally; not registered** | lane 218: `Section4/R44/JWeight.lean` defines the weighted-carrier `Jmul`, `Y/Z/B`, proves `weight_identity`, `force_pairing_le`, and `force_pairing_le'`; a later contract/binding lane is still owed |
| eq:Rcritical2 and first-exit closure | **absent as PDE result** | C01 V1–V3 explicitly exclude eq:Rcritical2; its scalar closure is now in `R44.Pieces`, but the PDE inequality is R44-owned gap G2 |

This corrects one stale statement in the reconciled comparison: registration gap
G6 there is now closed by `D01.datum_lemmas_v2` V2.  The registered field proves
finiteness only; it does not provide the time-slice/integral identity needed by
the energy argument.

## 1. Proof rows

Write, on a presingular interval,

```lean
Y t = ‖u(t)‖_{H^(1/2)}
Z t = ‖∇u(t)‖_{H^(1/2)}
B t = ‖f(t)‖_{H^(-1/2)}
```

as finite real norms coming from the appropriate Sobolev data.  These equations
are notation for the proposed datum-path definitions, not existing declarations.

### S1 — `J`-weighted identity and eq:Rcritical2 (G1 + G2, L)

Paper `:145-164`.  The clean PDE-level target is:

```lean
∀ t ∈ Set.Ioo (0 : ℝ) T,
  ∃ E' : ℝ,
    HasDerivAt (fun s => Y s ^ 2) E' t ∧
    (Y t ≤ theta * ν →
      E' + ν * Z t ^ 2 ≤
        C₂ * ν * Y t ^ 2 + C₃ * ν⁻¹ * B t ^ 2)
```

with `0 < theta`, `0 ≤ C₂`, `0 < C₃`, all universal.  Its analytic subrows are:

| subrow | exact need | owner / size / dependencies | blocker |
|---|---|---|---|
| S1a | define `J=(I-Δ)^(1/2)` on the datum carrier and prove `‖u‖²_{H^(3/2)} = Y² + Z²`, i.e. the exact weight identity, plus `abs ⟪f,Ju⟫ ≤ B * sqrt (Y²+Z²)` | **closed in lane 218**, `Section4/R44/JWeight.lean`; one satisfiable `JWeightDatum` restriction | no longer a proof blocker; registration remains |
| S1b | differentiate `Y²`, identify the `J`-weighted momentum pairing, remove pressure, and evaluate dissipation | **closed in lane 222**, `Section4/R44/EnergyIdentity.lean`; `energy_identity` for every classical solution, no extra analytic hypothesis | no longer a proof blocker; registration remains |
| S1c | `abs ⟪(u·∇)u,Ju⟫ ≤ C₀ * Y * (Y²+Z²)` | **R44-own G2**, L; depends on **A05 V2** (`velocityCriticalL3`, derivative/J critical embeddings) and G1 | blocks proving |
| S1c status | **closed (lane 220, `Section4/R44/TrilinearJ.lean`)**: `advection_pairing_le : abs (advectionJPairing h ha) ≤ trilinearConstJ * Y * (Y² + Z²)`, `trilinearConstJ = 3·criticalL3Const³`; carrier package `AdvectionJDatum` | R44 | — |
| S1d | Young/absorption under `Y ≤ theta*ν`, producing the displayed target | **R44-own G2**, S once S1a–c exist | blocks proving |

To feed S2 this must be assembled as one `E' : ℝ → ℝ` with
`IntervalIntegrable E' volume 0 T`; the pointwise existential alone does not
discharge `Pieces.lean:162-163`.

No registered field supplies S1.  The unregistered implementation now supplies
S1a and S1b, while S1c--S1d remain open on this baseline.  `C01.energy_absorption_partial` V1 concerns
the `-Δu` test used by eq:RH1, not the `Ju` test.

### S2 — Grönwall, radius scaling, and first-exit bootstrap (closed conditionally, S–M)

Paper `:165-169`.  Once S1 and the force-square prefix bound are supplied, the
exact scalar input now accepted by Lean is
`criticalSquaredNormBound_radius` (`Pieces.lean:153`):

```lean
hsmall : C₃ * ν⁻¹ * R * exp (C₂ * ν * T) < (theta * ν)^2 / 4
henergy : ∀ t ∈ Ioo 0 T, Y t ≤ theta * ν →
  E' t + ν * Z t ^ 2 ≤ C₂ * ν * Y t ^ 2 + C₃ * ν⁻¹ * B t ^ 2
⊢ ∀ t ∈ Icc 0 T, Y t ≤ theta * ν / 2
```

It uses the tree lemma `A04.gronwall_deriv` and reuses
`Paper1.continuous_bootstrap`; the first possible crossing of `theta*ν` is
therefore closed without dividing by `Y`.
Instantiation also owes either global `Continuous Y` or a continuous extension
of the PDE norm path from `Icc 0 T`, because `Pieces.lean:158` inherits global
continuity from `Paper1.continuous_bootstrap`.
Unlike R43, no regularized square-root division is mathematically needed here:
eq:Rcritical2 is already a linear differential inequality for `Y²`.  The
shared part of the requested “regularized division / bootstrap” row is the
same `continuous_bootstrap`; importing `critical_norm_bound` would impose the
wrong `b*Y` energy shape.

Two further new theorems close the universal arithmetic:

* `exists_rcritical2_constants` chooses one `theta`, radius coefficient `c`,
  and exponent `C=C₂+1`, before all `ν,S`, satisfying both nonlinear shrinkings,
  the C01 gate shrinking, and `C₃*c² < theta²/4`.
* `radius_forces_gronwall_small` proves that
  `F < c*ν^(3/2)*exp (-(C₂+1)*ν*S)` implies the `hsmall` inequality above.
  Its proof pins the exponent as real `rpow`, obtains `ν³` after squaring, and
  leaves a nonpositive exponential.

Remaining input **G3** is not scalar arithmetic: identify `R` with the square of
`forceSobolevENormL2 (-1/2) f`.  Owner C01/D01, M; see S0/G3 below.  It blocks
proving R44, not stating it.

### S3 — critical embedding and C01 absorption gate (A05 V2; arithmetic closed)

Paper `:148-160,171`.  Needed slice estimate:

```lean
criticalL3 (slice u t) ≤ ENNReal.ofReal (Cemb * Y t)
```

This is `research/A05/Spec.lean:366` in its inhomogeneous consequence, but the
registry has only `A05.gradient_l6` V1.  **A05 V2**, size M–L, must register and
prove the critical embedding carrier translation.  It blocks proving.

Given that estimate, S2's `Y t ≤ theta*ν` and the universal shrinking
`C₁*Cemb*theta ≤ 1/4`, C01's exact gate

```lean
ENNReal.ofReal C₁ * criticalL3 (slice u t) ≤ ENNReal.ofReal (ν / 4)
```

is already `R43.criticalL3_gate_enorm`.  `R44.Pieces` imports and reuses it;
there is deliberately no duplicate R44 declaration.  The target vocabulary
`C₁`/`criticalL3` is registered by `C01.energy_absorption_partial` V1.

### S4 — finite `H²` time integral at zero datum (C01 V4 + endpoint glue, M)

Paper `:171`, referring to `:113-130`.  Proposed C01 field, exact draft shape:

```lean
h2TimeIntegralZeroDatum :
  ∀ ν, 0 < ν → ∀ f, MemForceR f →
  ∀ T (w : ClassicalSolutionR ν (fun _ => 0) f T) S, 0 < S → S ≤ T →
    (∀ t ∈ Ico 0 S,
      ENNReal.ofReal C₁ * criticalL3 (slice w.velocity t) ≤
        ENNReal.ofReal (ν / 4)) →
    ∫⁻ t in Ioo 0 S,
      sobolevENorm 2 (slice w.velocity t) ^ (2 : ℝ) ≤ ENNReal.ofReal (...)
```

Supply is **not registered**.  Owner **C01 V4**, M after its E5–E7 chain:
`enstrophyIntegralBound` (eq:RH1), `sobolevTwoFourier`, then this assembly.
The ordinary low-frequency input `l2Bound` is registered in
`C01.energy_absorption_partial_v3` V3.  `MemForceR` supplies finite unscaled
`L¹_tL²_x` and `L²_tL²_x` quantities; their smallness is not used.

Two wiring items remain:

* The integrand expected by A04 is `sobolevENorm 2 ... ^ (2:ℕ)`, whereas C01
  uses `^ (2:ℝ)`.  This is **closed** by the imported
  `R43.enorm_npow_two_eq_rpow_two`; no duplicate is introduced.
* At a hypothetical finite maximal lifespan `L ≤ S`, A02 gives solutions only
  on every `b < L`, while C01's field is stated for a fixed horizon.  Passing
  `b ↑ L` to get finiteness at `L` is **R44-own G4**, M (or a C01 endpoint
  corollary).  It depends on C01 V4, A02 V2, monotone convergence, and the force
  finiteness bounds.  It blocks proving.

### S5 — exclude lifespan at or before `S` (A04 V3, S wiring after S4)

Paper `:171`.  The exact continuation target is the draft field

```lean
extendsBeyond :
  ... → SolvesBelow ν (fun _ => 0) f L u p →
  squaredHTwoIntegral L u ≠ ⊤ →
  ENNReal.ofReal L < maximalLifespanR ν (fun _ => 0) f
```

It is neither proved nor registered on this branch: **A04 V3** is required.
The owner's PR #161 to `main` proves a conditional version, but it is not on
`origin/erenup/integration`.  A04 V2 explicitly stops before the criterion.
`A04.zero_mem_initialClassR`
(`Section4/A04/ZeroSolution.lean:80`) and `A04.memL1Hm_of_memForceR` are tree
lemmas supplying the zero datum and `MemL1Hm` side conditions; they are not new
R44 mathematics.

The contradiction assumes `L = maximalLifespanR ... ≤ ofReal S`, uses the
registered-but-A01-conditional maximal family `A02.maximal_partial_v2` V2,
feeds S4 at `L`, then contradicts `ofReal L < L`.  Besides A04 V3 it depends on
R44-own G4 and on discharge of A02 V2's explicit local-solution hypothesis by
the future A01 contract.  These block proving, not stating.

### S6 — exact `a = 0` API and non-density consequence (reduction S once S5 closes)

The R44 conclusion is not a general-datum result:

```lean
ENNReal.ofReal S < maximalLifespanR ν (fun _ => 0) f
```

The spelling `(fun _ => 0)` is definitionally the one in
`breakdownSetRZero`.  From `main` at `S := T`, field `nonDensityBallZero` is the
two-line contradiction

```lean
intro hfBreakdown
exact (not_le_of_gt hLife) hfBreakdown.2
```

because membership unfolds by `Iff.rfl` to
`MemForceR f ∧ maximalLifespanR ... ≤ ENNReal.ofReal T`.  This reduction is
R44-own, S, and has no analytic dependency beyond S5.  It is not separately
declared in `Pieces.lean`, because importing frozen `Contracts.V1.Data` into a
formalization implementation solely for a two-line packaging lemma would cross
the repository's contract/implementation boundary; it belongs in the eventual
R44 binding.

The smallness ball is nonempty/non-vacuous: `D01.datum_lemmas_v2` V2 supplies
`forceSobolevENorm_ne_top` at `m=0,s=-1/2,q=2`, the radius is positive by
`exists_rcritical2_constants` and the formula, and the zero force is the
concrete witness.

## 2. Gap summary

| id | owner | size | depends on | blocks |
|---|---|---:|---|---|
| G1 | D01/R44 datum layer: `J`, exact weight identity, duality | **closed in implementation** | `Section4/R44/JWeight.lean`; contract/binding registration owed | no remaining S1a proof blocker |
| G2 | R44-own: eq:Rcritical2 PDE derivation; S1b energy identity closed by lane 222 | L | S1c trilinear estimate and S1d absorption/assembly; pressure and critical-path differentiation are proved | proof (remaining S1c/S1d) |
| G3 | C01/D01: `H^{-1/2}` force slice, continuity/integrability, prefix integral = time-norm square | **partly closed, still M** | lane 218 confirms `RealVectorSobolev (-1/2)` and supplies the slicewise `B`/duality carrier. A named continuous order-`-1/2` force-datum path in the R44 consumer shape, and its prefix-integral/time-norm-square identity, remain to be packaged. | proof/S2 application |
| G4 | R44-own: maximal-endpoint gluing and `SolvesBelow` assembly | M | A02 V2, C01 V4, A04 V3, A01 local solution | proof/S4→S5 |
| G5 | A04↔C01 `ℕ`-pow/rpow pin | S | none | **closed**, reused from R43 |
| A05 V2 | critical `L³` embeddings | M–L | A05 carrier translation | proof/S1,S3 |
| C01 V4 | eq:RH1 + Fourier inequality + zero-datum `H²` assembly | M+M | existing C01 V3 | proof/S4 |
| A04 V3 | `extendsBeyond` finite-horizon criterion | M+S proof and registration (no `extendsBeyond` theorem on this branch) | A04/A02 restart/continuation work | proof/S5 |
| R44 scalar | constants, radius algebra, Grönwall + first exit | S–M | only existing tree scalar lemmas | **closed this lane** |

Bottom line: **nothing blocks stating the nine-field R44 API**.  A clean
PDE-level proof of its main estimate still waits on S1b--S1d and G3's pathwise
facts; proving and binding the API waits on G2--G4 plus A05 V2, C01 V4, A04 V3, and the transitive
A01 discharge in A02 V2.
