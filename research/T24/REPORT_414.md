# REPORT_414 — T24 Ua4 force_smooth + force_support (Opus; transcribed by lead from the agent message, report-file guard)

Lane 414 complete — both Ua4 targets closed, no gaps. Report below (I did not write `research/T24/REPORT_414.md`: my instructions forbid writing report `.md` files, and the brief allows the full report in this message instead).

---

# Lane 414 — T24a Ua4 report

## 1. What was proved

Both Ua4 targets closed in full. No named input, no placeholder, no `sorry`/`admit`/`axiom`/`native_decide`, no `maxHeartbeats` bump. Exact statements:

```lean
theorem force_smooth {ν : ℝ} {U F : VelocityField} (c : Space) (r τ₀ τ₁ : ℝ)
    (hτ₀ : 0 < τ₀) (hτ₁ : τ₁ < 1)
    (hvelocity_smooth : ContDiffOn ℝ ∞ U preSingularDomain)
    (hforce_smooth : ContDiff ℝ ∞ F) :
    ∀ b : VelocityField, AffineAdmissible c r τ₀ τ₁ b →
      ContDiff ℝ ∞ (affineForce ν U F b)

theorem force_support {ν : ℝ} {U F : VelocityField} (c : Space) (r τ₀ τ₁ : ℝ)
    (hτ₀ : 0 < τ₀)
    (hforce_support : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport F) :
    ∀ b : VelocityField, AffineAdmissible c r τ₀ τ₁ b →
      NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport (affineForce ν U F b)
```

The conclusions are token-identical to `research/T24/Spec.lean:1025-1033` with `P.velocity`/`P.force` replaced by raw `U`/`F` (`SpaceTimeField` is an `abbrev` for `VelocityField`, `Data.lean:104`; `Contracts.V1.CompactPositiveTimeSupport` is `rfl`-identical to the vendor one, per the `Bindings/Packet.lean` correspondence block — and the probe closes across that bridge with a bare `exact`).

**Raw packet clauses consumed:** `force_smooth` uses `velocity_smooth` and `force_smooth`; `force_support` uses `force_support` only. Neither uses `0 < ν`, the pressure, `divergence_free`, or the divergence clause of `AffineAdmissible`.

**On `τ₁ < 1` (the brief asked me to state which route):** carried **explicitly**, as lane 403 does. `AffineAdmissible` cannot supply it — it constrains `b` relative to the cylinder and says nothing about where the cylinder sits; it is satisfiable with `τ₁ ≥ 1` (take `b = 0`, empty `tsupport`). A finding worth flagging to the lead: `force_support` does **not** need `τ₁ < 1` at all (it never looks at `U`), so it takes only `0 < τ₀` — a strictly weaker hypothesis set than the brief anticipated.

Route landed as sketched, with one substitution: the analytic work came wholesale from the **vendored `NavierStokes.ResidualRegularity`**, not `ResidualCalculus` (the file lane 398 mined). That file already has `contDiffOn_{temporalDerivative,spatialDerivative,spatialLaplacian}` on open sets and the locality lemmas `*_congr` (hypothesis `u =ᶠ[𝓝 z] v` only, no differentiability). Two opens cover spacetime — `Ioo 0 1 ×ˢ univ` (inside `preSingularDomain`, where `U` is smooth) and `(tsupport b)ᶜ` (where `affineForce = F`) — and `contDiff_iff_contDiffAt` + `ContDiffAt.congr_of_eventuallyEq` glue. For the support clause I did **not** use `HasCompactSupport.add`: the single inclusion `tsupport (affineForce ν U F b) ⊆ tsupport F ∪ tsupport b` gives both halves at once and needs no new definition (a named `affineCorrection` would have been drift from `Spec.lean`).

## 2. What exists in Lean now

- `/data_8T/ping/blowup_density/.claude/worktrees/414-T24-Ua4-force-smooth-support/formalization/NSFormalization/Section3/T24/AffineForce.lean` — 215 lines, imports lane 392's `AffineBasics` (nothing restated). Seven declarations: the two targets plus reusable `affineCylinder_subset_interior`, `affineCylinder_subset_positiveTimeDomain`, `affineForce_eq_of_notMem_tsupport`, `contDiffOn_affineForce_interior`, `tsupport_affineForce_subset`.
- `/data_8T/ping/blowup_density/.claude/worktrees/414-T24-Ua4-force-smooth-support/research/T24/probes/affine_force_closes.lean` — discharges both registered `AffineVariationAPI` fields on `Bindings.packet ν hν` in Contracts vocabulary (affine defs restated verbatim from `Spec.lean:961-990`), plus `zero_admissible` and the `b = 0` reduction back to the packet's own `force_smooth`/`force_support`.
- `/data_8T/ping/blowup_density/.claude/worktrees/414-T24-Ua4-force-smooth-support/research/T24/probes/affine_force_nonzero.lean` — lane 398's nonzero witness `bWitness = spatialCurl (θ·φ·e₁)` on `ball 0 1 × (1/4,3/4)` rebuilt (probes are standalone `lake env lean` files, not importable modules), with both Ua4 conclusions instantiated at it and `bWitness_ne_zero` reproduced.
- `/data_8T/ping/blowup_density/.claude/worktrees/414-T24-Ua4-force-smooth-support/research/T24/axioms_ua4.lean`, `.../research/T24/ATTEMPTS_UA4.md`, and a Ua4 DONE paragraph in `.../research/T24/T24_SPLIT.md`.

Committed as `9ce4bbc8` on `erenup/414-T24-Ua4-force-smooth-support`. Nothing pushed, merged, or rebased; no existing module touched.

## 3. Gaps

None against the brief's goal — both theorems are closed unconditionally from the raw packet clauses. Three things the lead should know:

1. `force_support` takes only `0 < τ₀`, not `0 < τ₀ ∧ τ₁ < 1`. If the Ua8 assembly lane prefers uniform signatures across the T24a units it can pass `τ₁ < 1` and let it go unused, but I did not take a hypothesis the proof does not need.
2. The nonzero-witness construction is now duplicated in two probe files (398's and mine). That is forced by probes not being library modules. If it gets a third consumer, promoting `bWitness` into a small `Section3/T24/AffineWitness.lean` module would be the fix — a decision for the lead, not something I should do inside this lane's scope.
3. `research/T24/REPORT_414.md` was not created (report-file rule); this message is the report.

## 4. Commands run and results

All from `verification/` after `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`.

| Command | Result |
|---|---|
| `lake build NSFormalization.Section3.T24.AffineMomentum` (base check) | `Build completed successfully (3007 jobs).` |
| `lake build NSFormalization.Section3.T24.AffineForce` | `Build completed successfully (3008 jobs).` — 0 errors, compiled first try |
| `lake env lean ../formalization/NSFormalization/Section3/T24/AffineForce.lean` | no output, exit 0 |
| `lake env lean ../research/T24/axioms_ua4.lean` | 7/7 declarations print `[propext, Classical.choice, Quot.sound]` |
| `lake env lean ../research/T24/probes/affine_force_closes.lean` | 6/6 declarations, same three axioms |
| `lake env lean ../research/T24/probes/affine_force_nonzero.lean` | 4/4 declarations, same three axioms |
| `make check` | exit 0 |
| `make test` | exit 0 (all registered contracts "checked; standard logical axioms only") |
| `make test-mutations` | exit 0 |

**Failed approaches, all recorded in `ATTEMPTS_UA4.md`:**

- *Using `preSingularDomain` directly for `ContDiffAt`* — dead by construction: `Ico 0 1 ×ˢ univ` is not open (the `t = 0` face), so neither `ContDiffOn.contDiffAt` nor any `ResidualRegularity.contDiffOn_*` (all take `IsOpen s`) can fire. Must pass to `Ioo 0 1 ×ˢ univ` first. This is why `0 < τ₀` is needed for *smoothness*, not only for the positive-time clause.
- *Hand-proving smoothness of `∂ₜb`/`Δb`* via `fderiv ℝ (fun s => b (s,x)) t = (fderiv ℝ b (t,x)).comp (inl ℝ ℝ Space)` + `ContDiff.fderiv_right` — correct but redundant; abandoned before writing Lean once `contDiffOn_time_fderiv` was found. Recorded because a lane that greps only `ResidualCalculus` will take it.
- *`HasCompactSupport.add` on `F` and a separately named correction* (the brief's sketch) — rejected: needs a `affineCorrection` definition `Spec.lean` does not have, and still needs its compact support proved separately.
- **Two mutation checks confirming the hypotheses are load-bearing** (scratch files in `/tmp`, not committed). Dropping `hτ₁ : τ₁ < 1` from `force_smooth`: `error: linarith failed to find a contradiction` with `hz : z ∉ Ioo 0 1 ×ˢ univ`, `hmem : z ∈ tsupport b`, `a✝ : 1 ≤ τ₁ ⊢ False`. Dropping `hτ₀ : 0 < τ₀` from `force_support`: `error: linarith failed to find a contradiction` with `hb_supp : tsupport b ⊆ affineCylinder c r τ₀ τ₁`, `a✝ : τ₀ ≤ 0 ⊢ False` — and that second one is not a proof-route artefact, the conclusion is genuinely false at e.g. `τ₀ = -1`.


> Lead note after review 414: this file was transcribed by the lead from the agent message (report-file guard), so the sentence "REPORT_414.md was not created" describes the agent's own step, not the repository state; `make check` is a repository-root target and was run from the worktree root.
