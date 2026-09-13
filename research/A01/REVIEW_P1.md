# A01 unit P1 — review of lane 101

Reviewer pass over `erenup/101-A01-p1-potential` (commit `05ef4af`), covering
`formalization/NSFormalization/Section4/A01/RadialPotential.lean`,
`research/A01/ATTEMPTS_P1.md` and `research/A01/axioms_p1.lean`.  Lean run in the
lane worktree at the repo pin (`leanprover/lean4:v4.34.0-rc2`).

## Verdict: **ACCEPT-WITH-NOTES**

The mathematics is right and the Lean is clean: the module compiles with **zero
warnings**, all three declarations carry only the standard three axioms, and the
two local restatements are not merely textually faithful — I proved the future
`Bindings` bridge `RadialPotential.pressurePotential = Contracts.V1.Data.pressurePotential`
by `rfl` (it compiles), so the restatement *is* the contract object.  I
cross-checked the conclusion's orientation and normalisation independently of
the lane's proof on `G = id`, and exhibited two inhabitants of
`HasSymmetricJacobian`, so the theorem is neither vacuous nor mis-normalised.
Four of the six recorded failures reproduce verbatim.

Going further than asked: I wrote the whole `pressure_potential` gauge wrapping
(`Spec.lean:227`) on top of this lane and it **compiles with standard axioms in
52 lines** (§4), and the two smoothness side conditions it needs come out of
`ClassicalSolutionR.pressure_smooth` in 14 more lines — the `t = 0` endpoint is
*not* an obstruction.  Only the Hessian-symmetry step is left.  Contract field
`m4` is therefore much closer than `A01_SPLIT.md` records.

The notes are three documentation corrections (one of which materially
overstates a blocker) and one cosmetic Lean nit.  Nothing blocks merge.

---

## 1. Commands and results

All from the lane worktree, `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, lake
from `verification/`, one lake process at a time.

| # | command | result |
|---|---|---|
| 1 | `bash scripts/lean-install.sh` | idempotent; ends `== OK` (so `lake test`, the registered contract closure, is green at this commit) |
| 2 | `lake build NSFormalization.Section4.A01.RadialPotential` | `Build completed successfully (2671 jobs).` |
| 3 | `lake env lean ../formalization/NSFormalization/Section4/A01/RadialPotential.lean` | **no output**, exit 0 — no errors *and* no warnings (no deprecations, no unused-simp-arg lints) |
| 4 | `lake env lean ../research/A01/axioms_p1.lean` | 3 declarations, each exactly `[propext, Classical.choice, Quot.sound]` |
| 5 | `grep -nE 'sorry\|admit\|axiom\|native_decide\|maxHeartbeats'` on the three files | no hit in the module; in `axioms_p1.lean` only the three `#print axioms` lines; in `ATTEMPTS_P1.md` only prose |
| 6 | `make check` | OK — `check_formalization_plan`, `check_contracts`, 13 policy tests, `30 work items: … consistent` |
| 7 | `python3 experiments/build_changed_lean.py --base-ref HEAD~1` | `Changed Lean modules: NSFormalization.Section4.A01.RadialPotential` → build success.  This is the CI step "Compile changed modules outside the registered test closure" (`.github/workflows/contracts.yml:76-81`), so the new module **is** covered by CI even though no contract imports it yet |

Reviewer scratch files (under `/tmp/a01p1rev/`, not committed): `bridge.lean`,
`normcheck.lean`, `slice.lean`, `gauge.lean`, `c1.lean`, `probes.lean`,
`eta.lean`.  Every one of them compiles except `probes.lean`, whose four
examples are *supposed* to fail (§5).

---

## 2. Statement fidelity

### (a) The two local restatements

**`pressurePotential`.**  `RadialPotential.lean:74-75` versus
`verification/Contracts/V1/Data.lean:596-597`: identical token for token, the
only difference being the whitespace `(0 : ℝ)` → `(0:ℝ)`.  Stronger check —
the bridge the `Bindings` lane will need already closes:

```lean
import Contracts.V1.Data
import NSFormalization.Section4.A01.RadialPotential
theorem pressurePotential_eq :
    NSFormalization.Section4.A01.RadialPotential.pressurePotential
      = BlowupDensity.Contracts.V1.Data.pressurePotential := rfl
```

compiles (`/tmp/a01p1rev/bridge.lean`, exit 0).  So the restatement is
*definitionally* the contract's object, not a lookalike, and the `SpatialField`
/ `SpaceTimeField` / `SpaceTimeScalar` abbreviations line up with `Data.lean:99,
104, 108` despite `Data.lean` importing `NavierStokes.R3.ProblemStatement` and
the module importing `NavierStokes.ProblemStatement` (see §3).

**`HasSymmetricJacobian`.**  `RadialPotential.lean:80-83` versus
`research/A01/Spec.lean:119-122`: byte-identical, including the
`Differentiable ℝ G` conjunct that `REVIEW.md` H2 insisted on.  `Spec.lean` is a
draft, not a registered contract, so there is no `rfl` bridge target yet; when
it is promoted, the same check should be run.  Encoding versus the manuscript:
`∂_i G_j = ∂_j G_i` is `02-preliminaries.tex:94` `∂_jG_k = ∂_kG_j`, same
statement.  Both docstring citations resolve exactly (`Spec.lean:117` is indeed
the `ClassicalSolutionR.pressure_smooth` remark; `:119` is the `def`).

### (b) The extra hypothesis `ContDiff ℝ ∞ G` — **not minimal** (Finding 1)

`EulerCompactParameterIntegral.integral_hasFDerivAt`
(`vendor/NavierStokesAndEuler/Euler/CompactParameterIntegral.lean:29-33`) does
demand `ContDiff ℝ ∞ F` **as stated**.  But its proof (`:33-51`) uses only three
things: `hF.continuous`, `hF.differentiable`, and
`Continuous (parameterDerivative F)` — i.e. continuity of `fderiv ℝ F`.  All
three are available at `ContDiff ℝ 1` through `contDiff_one_iff_fderiv`.  I
transcribed the vendor proof **verbatim** with `∞` weakened to `1` and it
compiles unchanged (`/tmp/a01p1rev/c1.lean`, `integral_hasFDerivAt_one`, 22
lines; `CompleteSpace E` turns out not to be needed either).  The rest of
`hasFDerivAt_radialPotential` likewise only ever uses `hsmooth.continuous`,
`hsmooth.differentiable` and `hsmooth.fderiv_right`, each of which has a
level-1 counterpart.

So the **minimal hypothesis is `ContDiff ℝ 1 G`** — equivalently
`Differentiable ℝ G ∧ Continuous (fderiv ℝ G)`.  This is *not* a blocker and I
do **not** recommend changing the Lean: forking a vendor lemma to save one
derivative order is not worth it, the consumer supplies `∞`
(`ClassicalSolutionR.pressure_smooth`), and — decisively — the manuscript's own
hypothesis at `02-preliminaries.tex:91` is "For smooth `H^∞` data, `G` is
smooth".  The statement is faithful.  What needs fixing is the *claim* about it
(Finding 1).

### (c) The conclusion encodes `∇(potential) = G`

`innerSL ℝ (G x) : Space →L[ℝ] ℝ` is `v ↦ ⟪G x, v⟫`; over `ℝ` the inner product
is symmetric, so there is no orientation hazard, and
`HasFDerivAt p (innerSL ℝ (G x)) x` says exactly `Dp(x)v = ⟪G x, v⟫`, i.e.
`∇p = G`.  Uniqueness of `fderiv` plus injectivity of `innerSL` means the
conclusion *pins down* `G`: no wrong field can satisfy it.

Independent cross-check of the normalisation, not routed through the lane's
proof (`/tmp/a01p1rev/normcheck.lean`, compiles):

* `potential_id : ∫₀¹ ⟪id (r • y), y⟫ dr = ‖y‖²/2` — a dropped or spurious `r`
  would give `‖y‖²` or `0`, so this pins the `∫₀¹ r dr = 1/2` bookkeeping;
* `grad_sq : HasFDerivAt (fun y => ‖y‖²/2) (innerSL ℝ x) x`, proved through
  Mathlib's `HasFDerivAt.norm_sq`;
* and `hasFDerivAt_radialPotential` instantiated at `G = id` produces
  `innerSL ℝ (id x)` — the same continuous linear map.

`pressureGradient_pressurePotential`'s right-hand side is literally `G x` in the
upstream basis-sum shape: `pressureGradient` is
`∑ᵢ (fderiv ℝ (p t ·) x eᵢ) • eᵢ` (`NavierStokes/ProblemStatement.lean:71`) and
the proof really reassembles the vector (`Fin.sum_univ_three`, then
`ext j; fin_cases j`), rather than asserting a componentwise identity.

The intermediate `inner_fderiv_symm` is also the right algebraic content:
`⟪DG(z)v, w⟫ = ∑_{i,j} vᵢ (∂ᵢGⱼ) wⱼ` is symmetric in `v, w` precisely when
`∂ᵢGⱼ = ∂ⱼGᵢ`, and the `hsym' 1 0 / 2 0 / 2 1` rewrite covers exactly the three
off-diagonal pairs.

### (d) Non-vacuity

`HasSymmetricJacobian` is inhabited — both proofs compile
(`/tmp/a01p1rev/slice.lean`):

* `hasSymmetricJacobian_zero` (the zero field, trivially);
* `hasSymmetricJacobian_id` (`G = id = ∇(‖x‖²/2)`, a genuine nonzero gradient
  field; `∂ᵢ(id)ⱼ = δᵢⱼ` is symmetric).

Combined with (c), the theorem has content and cannot be satisfied by a wrong
implementation.

---

## 3. Consistency

* **Imports are canonical and minimal.**  `NavierStokes.ProblemStatement` is
  where `Space` (`:30`), `coordinateVector` (`:39`) and `pressureGradient`
  (`:71`) actually live; `NavierStokes.R3.ProblemStatement` only re-`abbrev`s
  them (`:38-50`) and is itself an importer of the base.  `Data.lean` imports R3
  but `open`s the base namespace, and three other `Section4` modules import the
  base directly.  No divergence of `Space`, which is why the `rfl` bridge in
  §2(a) closes.  The four Mathlib imports are all used.
* **The restatements are the only copies.**  `grep -rn 'pressurePotential\|SymmetricJacobian'`
  over `formalization/NSFormalization/` (excluding `.lake`) hits this module
  only; on `origin/erenup/integration` it hits only `Contracts/V1/Data.lean:596`
  and one docstring mention in `Contracts/V1/InsertionFamily.lean:182`.
* **No clash with lane 093 on merge.**  `origin/erenup/integration` has
  `Section4/A01/{ConvectionDivergence,ProjectedEquation}.lean`; this lane adds
  `Section4/A01/RadialPotential.lean` — different filenames in the same
  directory.  093 uses namespace `NSFormalization.Section4.A01`, this lane the
  sub-namespace `NSFormalization.Section4.A01.RadialPotential`, and the five
  093 declarations (`convectionDivergence`, `convectionDivergence_eq_advection*`,
  `navierStokesResidual_eq_iff_projected`, `projected_of_classicalSolution`)
  share no name with this lane's three.  The commit touches three files, all
  new, and none of the four conflict-prone registry files — and no claim commit
  is needed, since A01 is already `in-progress` / `erenup` in
  `work_items.json` from lane 093.  Merge is textually conflict-free.
* **`inner_fderiv_symm` duplicates nothing.**  The only symmetric-Jacobian
  material in `Section4` is `D01/Longitudinal.lean:65,174` (hypothesis at `:66,175`)
  (`longitudinal_symm_of_curl_free`, `longitudinal_of_curl_free`), which takes
  the hypothesis in a different spelling (`partialDeriv i Z.field x j = …` on a
  `SmoothL2Field`) and lands in Fourier space.  Different object, different
  conclusion.  No `IsSymm`-style bilinear-form lemma exists in `Section4` or in
  the module's Mathlib import closure at this generality.  (See Finding 5 for
  the eventual consolidation.)

---

## 4. What remains for `pressure_potential` (`Spec.lean:227`) — I wrote it

The contract field is
`PressureGaugeEquivOn (Ico 0 T) (pressurePotential (fun z => pressureGradient u.pressure z.1 z.2)) u.pressure`,
i.e. `∃ c : ℝ → ℝ, ∀ t ∈ Ico 0 T, ∀ x, p(t,x) = Q(t,x) + c t` where `Q` is the
radial potential of `∇p`.  This lane gives the pointwise `∇Q = ∇p`; the wrapping
is "equal gradients on a connected `ℝ³` differ by a constant".  I wrote it
(`/tmp/a01p1rev/gauge.lean`); **it compiles and every declaration reports
`[propext, Classical.choice, Quot.sound]`**.  Three pieces, 52 lines of Lean:

| piece | lines | content |
|---|---|---|
| `pressureGradient_apply` | 5 | the basis sum reads off the `j`-th directional derivative |
| `fderiv_eq_of_pressureGradient_eq` | 15 | `pressureGradient p t = pressureGradient q t` ⇒ the slice `fderiv`s are equal (three-term basis expansion, the module's own idiom) — needed because `pressureGradient` is a vector, not a CLM |
| `pressure_potential_of_pointwise` | 32 | the gauge class itself, via `is_const_of_fderiv_eq_zero` (Mathlib `Analysis/Calculus/MeanValue.lean:565`) applied to `p(t,·) − Q(t,·)`, with `c t := p(t,0) − Q(t,0)` |

Its three hypotheses are the residual obligations, per `t ∈ Ico 0 T`:
`HasSymmetricJacobian (∇p(t,·))`, `ContDiff ℝ ∞ (∇p(t,·))`, and
`Differentiable ℝ (p(t,·))`.  Two of the three fall straight out of
`ClassicalSolutionR.pressure_smooth : ContDiffOn ℝ ∞ pressure (Ico 0 T ×ˢ univ)`
— both compile (`/tmp/a01p1rev/slice.lean`):

* `contDiff_slice` (6 lines): `ContDiff ℝ ∞ (fun y => p (t, y))` for every
  `t ∈ Ico 0 T`.  **The `t = 0` endpoint is not an obstruction** — I expected to
  need a unique-differentiability argument on the half-open slab and did not:
  `ContDiffOn.comp` with `y ↦ (t, y)` and `MapsTo univ (Ico 0 T ×ˢ univ)`, then
  `contDiffOn_univ`, closes it in two lines.
* `contDiff_gradSlice` (8 lines): hence `ContDiff ℝ ∞ (∇p(t,·))`, via
  `ContDiff.sum` + `ContDiff.fderiv_right`.

The one piece I did **not** finish is `HasSymmetricJacobian (∇p(t,·))` — i.e.
symmetry of the Hessian.  `ContDiffAt.isSymmSndFDerivAt` is the tool (already
used in-tree at `Section4/A05/SmoothJets.lean:115` and
`D01/DivergenceTime.lean:115`), but it needs the identification
`(fderiv ℝ (∇p(t,·)) x eᵢ) j = fderiv ℝ (fun y => fderiv ℝ (p(t,·)) y eⱼ) x eᵢ`
first, unpacking `pressureGradient`'s basis sum through one more `fderiv`.  I
estimate ~25 lines.

**So the whole of `m4` is roughly 90 further lines, all S-sized, with no gap.**
`A01_SPLIT.md` row `m4` sizes P1 as **M** with `pressure_potential` still open;
after this lane the honest status is "pointwise core done, wrapping written and
compiling in the reviewer's scratch, one 25-line Hessian-symmetry lemma left".

**Recommended next A01 lane: finish `m4`** — port the three declarations above
into `Section4/A01/RadialPotential.lean` (or a sibling `PressurePotential.lean`),
add the Hessian-symmetry lemma, and land
`ManuscriptLocalRegularity.pressure_potential` outright.  It is the only A01
item that is now a single short lane, it retires D01 unit **L9(b)** *and* L9(a)'s
neighbour in the same ledger, and it converts `A01_SPLIT.md`'s `m4` from an
obligation into a theorem the way lane 093 did for `m3`.  Everything else on the
A01 spine (A3, B1, C1b, C1c) is still an L-campaign needing a plan lane, and P2
is still gated on the missing Liouville statement.

---

## 5. Honesty of `ATTEMPTS_P1.md`

Citations opened and resolved: `EulerCompactParameterIntegral.integral_hasFDerivAt`
(`:29-33`), `parameterDerivative` (`:20`), `parameterDerivative_contDiff` (`:24`),
`Contracts/V1/Data.lean:596`, `research/A01/Spec.lean:117` and `:119`,
`NavierStokes/ProblemStatement.lean:71`.  All correct, including the two
line-number citations inside the module docstring.

Four of the six recorded failures reproduced, in `/tmp/a01p1rev/probes.lean`;
all four fail, and three of them with the exact symptom recorded:

| ATTEMPTS bullet | reproduced? | error actually printed |
|---|---|---|
| 3 — `.comp` output ascribed directly | **yes, verbatim** | `HasFDerivAt (?m.232 ∘ fun y => (y, t)) (?m.233 ∘SL inl ℝ Space ℝ) x` vs the ascribed type — the higher-order unification failure as described |
| 4 — `HasDerivAt.smul` on `s ↦ s • G(s•x)` | **yes, but misdiagnosed** | `HasDerivAt (id • fun s => G (s • x)) (t • DG(t•x) x + G (t•x)) t` vs `HasDerivAt (fun s => s • G (s•x)) (G (t•x) + t • DG(t•x) x) t` — see Finding 2 |
| 5 — `simpa using (hasDerivAt_id t).mul hginner` | **yes, verbatim** | `@HasDerivAt … Real.normedCommRing.toAddCommGroup … (id * fun s => ⟪G (s•x), v⟫) …` vs `… Real.instAddCommGroup Semiring.toModule … (fun s => s * ⟪G (s•x), v⟫) …` — exactly the instance-path mismatch recorded |
| 6 — `rw [hslice]` inside `integral_congr` | **yes, verbatim** | `Did not find an occurrence of the pattern G' (t, ?y)`, target still `(fun x => ⟪G' (t, x • y), y⟫) r` — the unreduced beta-redex as recorded |

Not reproduced: bullet 1 (the `ContDiff ℝ 1` route — I went the other way and
showed the claim is too pessimistic, Finding 1) and bullet 2 (the `Finset`-sum
route for `inner_fderiv_symm`, not attempted).  The "Route that worked" section
matches the committed proof step for step, including the two-stage `simp` detail
in step 5 and the explicit-ascription fix in step 6.

---

## 6. Findings

### Finding 1 — "`ContDiff ℝ ∞` is required" overstates the blocker (severity: **low**, documentation)

*Location:* `RadialPotential.lean:36-45` ("Hypothesis note") and
`ATTEMPTS_P1.md` bullet 1.

The module says the vendor lemma "requires the integrand to be `ContDiff ℝ ∞`"
and ATTEMPTS says a `ContDiff ℝ 1` route "would require re-deriving
differentiation under the integral from
`intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le` with a manual
local derivative bound on a compact ball — extra bookkeeping outside one bounded
unit".  The bound is already *in* the vendor proof and transcribes verbatim: I
compiled the identical 22-line proof at `ContDiff ℝ 1`
(`/tmp/a01p1rev/c1.lean`).  The minimal hypothesis for the theorem as a whole is
`ContDiff ℝ 1 G`.

*Fix (docs only, no Lean change):* reword to "the reused vendor lemma is
**stated** at `ContDiff ℝ ∞`; `ContDiff ℝ 1 G` would suffice mathematically —
the vendor proof only needs `Continuous (fderiv ℝ F)` — but we do not fork
vendor code to save a derivative order, the consumer supplies `∞`
(`ClassicalSolutionR.pressure_smooth`), and the manuscript's own hypothesis
(`02-preliminaries.tex:91`, 'For smooth `H^∞` data, `G` is smooth') is `∞`."
Recording the weaker hypothesis matters because a future consumer that only has
`C¹` should know the theorem is one 22-line local lemma away, not a campaign.

### Finding 2 — the `HasDerivAt.smul` failure is misattributed (severity: **low**, honesty)

*Location:* `ATTEMPTS_P1.md`, bullet "`ψ'` via `HasDerivAt.smul` …".

Recorded cause: "a `PiLp.normedAddCommGroup.toAddCommGroup` vs
`WithLp.instAddCommGroup` instance-diamond mismatch that `simpa` could not
bridge."  The failure is real, but the error Lean actually prints is a
*function-form and summand-order* mismatch — `id • fun s => G (s • x)` versus
`fun s => s • G (s • x)`, and `t • DG x + G(t•x)` versus `G(t•x) + t • DG x` —
with no `PiLp`/`WithLp` instance path in sight.  The instance-diamond text
belongs to the *next* bullet (the `Real.normedCommRing.toAddCommGroup` one),
which I reproduced verbatim.  `CLAUDE.md` rule 4 is about recording negatives
accurately; a misattributed cause sends the next reader after the wrong fix.

*Fix:* paste the actual error text into bullet 4.

### Finding 3 — needless eta-expansion in the corollary's statement (severity: **cosmetic**)

*Location:* `RadialPotential.lean:205`.

`pressureGradient (fun z => pressurePotential G' z) t x = G x` — the
`fun z => … z` wrapper is unnecessary.  I verified that the eta-reduced
statement `pressureGradient (pressurePotential G') t x = G x` typechecks and is
discharged by the committed theorem *as is* (`/tmp/a01p1rev/eta.lean`, exit 0).

*Fix:* delete the wrapper.  The cleaner spelling is what the consumer will write.

### Finding 4 — `Differentiable ℝ G` inside `hG` is dead weight here (severity: **informational**)

`hasFDerivAt_radialPotential` never uses `hG.1`: `inner_fderiv_symm` discards it
(`obtain ⟨-, hsym⟩`, `:91`) and all differentiability comes from `hsmooth`.
This is **correct as written** — the conjunct is part of `Spec.lean`'s
predicate for the reason `REVIEW.md` H2 gives (without it `IsLerayComplement`
stops being single-valued), and fidelity to the spec beats minimality.  Noted
only so a later reader does not think it is load-bearing in *this* proof.  No
change.

### Finding 5 — two spellings of "curl free" now coexist in `Section4` (severity: **low**, future consolidation)

`Section4/D01/Longitudinal.lean:66,175` states the same hypothesis as
`∀ i j x, partialDeriv i Z.field x j = partialDeriv j Z.field x i` on a
`SmoothL2Field`, while A01 now has `HasSymmetricJacobian` on a `SpatialField`.
Not a duplication — different carriers, different conclusions — but the two
should eventually be bridged by a one-line lemma so that D01's SL5 output can
feed A01's potential.  Out of scope for this lane; flag it for whoever writes
the `IsLerayComplement` / P3 lane.

### Finding 6 — `A01_SPLIT.md` row `m4` is now stale (severity: **low**, bookkeeping)

Row `m4` sizes the field as **M** / unit P1 / "differentiate under
`intervalIntegral`".  After this lane, the pointwise core is done and the
wrapping compiles in a reviewer scratch (§4).  Update the row to record the
residual (~25 lines of Hessian symmetry) rather than the whole unit, the same
way lane 093's reviewer converted `m3`.

---

## 7. Summary for the lead

Merge it.  The three documentation fixes (Findings 1, 2, 6) and the one-token
Lean nit (Finding 3) can ride on the next A01 lane rather than block this one —
none of them changes what is proved.  The next lane is short and well defined:
finish `ManuscriptLocalRegularity.pressure_potential` from §4.
