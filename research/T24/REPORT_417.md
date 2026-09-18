# REPORT_417 — T24 Ua7 `infinite_dimensional` (Opus; transcribed by lead from the agent message, report-file guard)

Done. Lane 417 is committed on `erenup/417-T24-Ua7-infinite-dimensional` (commit `d388c1a4`).

## 1. What was proved

T24a unit **Ua7**, the `infinite_dimensional` field of `AffineVariationAPI` (`research/T24/Spec.lean:1085-1087`, `paper/sections/03-torus.tex:688-691`), fully closed, no residual:

```lean
theorem infinite_dimensional (c : Space) (r τ₀ τ₁ : ℝ) (hr : 0 < r)
    (hτ : τ₀ < τ₁) :
    ∃ b : ℕ → VelocityField,
      (∀ n : ℕ, AffineAdmissible c r τ₀ τ₁ (b n)) ∧ LinearIndependent ℝ b
```

The conclusion is token-identical to the Spec field; `SpaceTimeField` is literally `VelocityField` (`verification/Contracts/V1/Data.lean:104`, an `abbrev`), and the probe records that `rfl` and states the field in both spellings. Hypotheses are only the two cylinder-nondegeneracy facts `0 < r` and `τ₀ < τ₁`. `AffineBasics.window` shows the canonical parameter package also carries `0 < τ₀` and `τ₁ < 1`; neither is used. No named input, no packet clause, no `maxHeartbeats` override.

Construction: balls `closedBall (c + (r·2⁻ⁿ/2)·e₁) (r·2⁻ⁿ/16)`, pairwise disjoint and all inside `ball c r`; on the n-th ball the witness `b n = ∇ × (θ(t)·φₙ(x)·e₁)` with one time bump `θ` supported in `Ioo τ₀ τ₁`. Independence is `linearIndependent_iff'` plus disjoint supports: `curlBump_ne_zero` yields a point `z` with `b n z ≠ 0`, that point is automatically in the carrier of `b n`, so `z.2` sits in the n-th ball and outside all others, and `Finset.sum_eq_single_of_mem` kills every other term of a vanishing combination.

## 2. What exists in Lean now

- `/data_8T/ping/blowup_density/.claude/worktrees/417-T24-Ua7-infinite-dimensional/formalization/NSFormalization/Section3/T24/AffineWitness.lean` — the promoted shared witness library the brief asked for. `AffineWitness.potential θ φ = (θ(t)·φ(x))•e₁`, `curlBump θ φ = spatialCurl (potential θ φ)`, `carrier θ φ = closedBall t₀ θ.rOut ×ˢ closedBall x₀ φ.rOut`, plus `curlBump_contDiff`, `_hasCompactSupport`, `tsupport_curlBump_subset`, `_divergence_free`, `_eq_zero_of_notMem`, `curlBump_admissible`, `curl_component_one`, `curlBump_ne_zero`. It is parameterised by arbitrary `ContDiffBump`s, so lane 398's `bWitness` is exactly its instance `t₀=1/2, x₀=0, θ=⟨1/16,1/8⟩, φ=⟨1/2,3/4⟩`. **I did not edit `research/T24/probes/affine_momentum_nonzero.lean`** (ground rule: no edits to existing modules) — sharing is available for the next lane that touches it, and the new probe uses the library directly.
- `/data_8T/ping/blowup_density/.claude/worktrees/417-T24-Ua7-infinite-dimensional/formalization/NSFormalization/Section3/T24/AffineFamily.lean` — geometry (`scale`, `centerOffset`, `ballRadius`, `center`), the two arithmetic facts `closedBall_subset_ball` and `radius_add_lt`/`notMem_closedBall_of_ne`, the bumps `timeBump`/`spaceBump`, the family `bFam`, and `infinite_dimensional`. Imports `NSFormalization.Section3.T24.AffineBasics` transitively via `AffineWitness`; nothing from `AffineBasics` is restated.
- `/data_8T/ping/blowup_density/.claude/worktrees/417-T24-Ua7-infinite-dimensional/research/T24/probes/affine_family_closes.lean` — `rfl` bridges for the Spec vocabulary in registered `Contracts.V1` types; the field discharged in both the `VelocityField` and `Contracts.V1.Data.SpaceTimeField` spelling; the packet-level form on `BlowupDensity.Bindings.packet ν hν` adding `Function.Injective (n ↦ U + b n)` via `AffineBasics.distinct` (that is the "`b ↦ U+b` is injective, so its image is infinite dimensional" half of the paper sentence); `b 0 ≠ b 1` and injectivity of the whole sequence; the explicit disjoint geometry; and two degeneracy checks proving `0 < r` and `τ₀ < τ₁` are load-bearing (at `r = 0` or `τ₁ ≤ τ₀` every admissible `b` is `0`, so no linearly independent admissible sequence exists).
- `/data_8T/ping/blowup_density/.claude/worktrees/417-T24-Ua7-infinite-dimensional/research/T24/axioms_ua7.lean` — 42 declarations, all `[propext, Classical.choice, Quot.sound]`.
- `/data_8T/ping/blowup_density/.claude/worktrees/417-T24-Ua7-infinite-dimensional/research/T24/ATTEMPTS_UA7.md` and the Ua7 `DONE (lane 417)` block in `/data_8T/ping/blowup_density/.claude/worktrees/417-T24-Ua7-infinite-dimensional/research/T24/T24_SPLIT.md`.

## 3. Gaps

No mathematical gap in Ua7 — the theorem is closed with no `sorry`/`admit`/`axiom`/`native_decide` and standard-3 axioms only. Three scope notes for the lead:

- `AffineVariationAPI` is not yet a registered contract in `verification/Contracts/V1`, so the probe restates the Spec fragments in registered vocabulary and closes them there, the same pattern as `affine_energy_closes.lean`. Registration of the T24 packet is a separate unit (lane 420).
- The library was created as a new module rather than by refactoring `research/T24/probes/affine_momentum_nonzero.lean` onto it, because that probe is an existing file. If the lead wants literal de-duplication, a follow-up one-line change rewrites `bWitness := AffineWitness.curlBump timeBump spaceBump` there.
- `AffineFamily.bFam` takes the proofs `hr`/`hτ` as arguments (they feed the `ContDiffBump` field proofs). That is harmless by proof irrelevance but means `bFam` is not a bare `ℕ → VelocityField` until the parameters are applied.

Failed approaches, all recorded in `ATTEMPTS_UA7.md` with exact text:
- `positivity` could not prove `0 < r * scale n` (twice) — `scale` is a plain `def` and `positivity` ignores the context hypothesis. Exact error: `error: NSFormalization/Section3/T24/AffineFamily.lean:102:36: failed to prove positivity/nonnegativity/nonzeroness`. Replaced with `mul_pos hr (scale_pos n)`.
- First draft put the `open`s inside `namespace AffineFamily`, so the top-level theorem lost `Space`/`VelocityField` and Lean auto-bound `Space` as a universe variable: `Application type mismatch: The argument c has type Space but is expected to have type NavierStokes.ProblemStatement.Space` and `failed to synthesize instance of type class AddCommMonoid VelocityField`. Fixed by hoisting the `open`s.
- `push_neg` is deprecated in this toolchain; rewritten as `push Not at hcon`.
- `BlowupDensity.Contracts.V1.SpaceTimeField` does not exist: `error(lean.unknownIdentifier)`. It lives in `...Contracts.V1.Data`.

Mutation check that the arithmetic is not vacuous: a throwaway copy with `ballRadius r n := r * scale n / 2` fails exactly at the two intended places — `../tmp/mut/AffineFamilyMut.lean:113:2: error: linarith failed to find a contradiction` (`closedBall_subset_ball`) and `:127:2` (`radius_add_lt_of_lt`).

## 4. Commands run and results

All from the worktree, after `. scripts/lean-env.sh`, `lake` from `verification/`, `LEAN_NUM_THREADS=6`.

- `lake build NSFormalization.Section3.T24.AffineWitness` → `✔ [3034/3034] Built ... (1.5s)` / `Build completed successfully (3034 jobs).`
- `lake build NSFormalization.Section3.T24.AffineFamily` → first run 4 errors (the `positivity` and namespace ones above); after the fixes `✔ [3035/3035] Built ... (1.3s)` / `Build completed successfully (3035 jobs).`
- `lake env lean ../formalization/NSFormalization/Section3/T24/AffineWitness.lean` → no output.
- `lake env lean ../formalization/NSFormalization/Section3/T24/AffineFamily.lean` → no output.
- `lake env lean ../research/T24/probes/affine_family_closes.lean` → only `'BlowupDensity.T24.ProbeUa7.fam' depends on axioms: [propext, Classical.choice, Quot.sound]`. (Two intermediate failures on the `SpaceTimeField` path, fixed.)
- `lake env lean ../research/T24/axioms_ua7.lean` → 42 occurrences of `[propext, Classical.choice, Quot.sound]`, nothing else.
- `bash scripts/gates.sh NSFormalization.Section3.T24.AffineWitness NSFormalization.Section3.T24.AffineFamily` → `== make test-mutations / extra_axiom: rejected as required / weakened_hypothesis: rejected as required / Mutation suite passed`, `== check_contracts "base_compatibility_checked": true`, `== gates OK`, exit 0.
- `make check` → exit 0 (`13 tests ... OK`, `45 work items: ownership, contract registration and task cards consistent.`).
- `git commit` on `erenup/417-T24-Ua7-infinite-dimensional` → `d388c1a4`, 6 files, 886 insertions. No push, no merge, no rebase.


> Lead note after review 417: the reviewer's two command-path notes — `make check` is run from the repository/worktree root (the report's `cd verification && make check` wording is corrected to that), and the base-aware contract check is `python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3`.
