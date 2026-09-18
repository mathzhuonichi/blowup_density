# REPORT_424 — T24 Ua8 `nonisolated` (Opus; transcribed by lead from the agent message, report-file guard)

Lane 424 is complete. Full report below (I did not create `research/T24/REPORT_424.md` — my instruction set forbids writing report `.md` files, so per the brief's fallback the report is here; the durable record went into `ATTEMPTS_UA8.md` and the `T24_SPLIT.md` status line, which the project's CLAUDE.md rule 4 requires).

## 1. What was proved

The **Ua8 `nonisolated` field** of `AffineVariationAPI` (`research/T24/Spec.lean:1104-1111`, paper `03-torus.tex:692-696`): the rescaled affine family approaches the packet in every `C^m` seminorm on `tsupport b`, for both the velocity and the force.

Exact statement (`NSFormalization.Section3.T24.nonisolated`, `AffineNonisolated.lean:197`):

```lean
theorem nonisolated {ν : ℝ} {U F : VelocityField} (c : Space) (r τ₀ τ₁ : ℝ)
    (hτ₀ : 0 < τ₀) (hτ₁ : τ₁ < 1)
    (hvelocity_smooth : ContDiffOn ℝ ∞ U preSingularDomain) :
    ∀ b : VelocityField, AffineAdmissible c r τ₀ τ₁ b → b ≠ 0 → ∀ m : ℕ,
      Tendsto (fun lam : ℝ => affineCkSeminorm (tsupport b) m
          (fun z => affineVelocity U (lam • b) z - U z)) (𝓝 0) (𝓝 0) ∧
      Tendsto (fun lam : ℝ => affineCkSeminorm (tsupport b) m
          (fun z => affineForce ν U F (lam • b) z - F z)) (𝓝 0) (𝓝 0)
```

Token-identical to the Spec field with `P.velocity`/`P.force` → `U`/`F`; `affineCkSeminorm` (lane 392, `AffineBasics.lean:50`) is the Spec's `ckSeminormE` on the nose, and `VelocityField` is the Spec's `SpaceTimeField` — both recorded as `rfl` bridges in the probe.

**Hypotheses consumed: only `velocity_smooth`, `0 < τ₀`, `τ₁ < 1`.** No named input, no placeholder. The packet's `force_smooth`/`force_support` are *not* needed (the ambient `F` cancels in the difference), nor `0 < ν`, nor the pressure. `b ≠ 0` is carried because the Spec carries it; the proof does not use it.

**Route (differs from the brief's literal suggestion, deliberately):** the paper's `λ L_U b + λ²(b·∇)b` was regrouped as `λ·(F̃_b − F) + (λ²−λ)·(b·∇)b`. Reason: `L_U b = ∂ₜb − νΔb + (U·∇)b + (b·∇)U` is **not globally `ContDiff`** — `U` is smooth only on `preSingularDomain` — so Mathlib's global `fun_iteratedFDeriv_add_apply` / `iteratedFDeriv_const_smul_apply'` would not apply and a pointwise `ContDiffAt`-on-`tsupport b` variant of the seminorm lemmas would have been needed. After regrouping, both coefficient fields are globally smooth: `F̃_b − F = affineForce ν U (fun _ => 0) b` is lane 414's `force_smooth` applied at the **zero** force (this is exactly why `force_smooth` on `F` drops out), and `(b·∇)b = advection b` is the vendored `contDiffOn_advection` on `univ`. The resulting bound `C_m|λ| + C_m'|λ²−λ|` differs from the paper's `C_m|λ| + C_m'λ²` only by absorbing a `|λ|`; the Spec asserts the `Tendsto`, not the constants.

## 2. What exists in Lean now

`/data_8T/ping/blowup_density/.claude/worktrees/424-T24-Ua8-nonisolated/formalization/NSFormalization/Section3/T24/AffineNonisolated.lean` (namespace `NSFormalization.Section3.T24`, imports `AffineBasics` + `AffineForce` + vendored `NavierStokes.ResidualCalculus`; no definition restated):

- §1 seminorm algebra, none of which was in the tree: `enn_mul_biSup` (`:75`), `affineCkSeminorm_const_smul` (`:82`, exact homogeneity), `affineCkSeminorm_add_le` (`:94`), `affineCkSeminorm_lt_top` (`:112`) — the last **is** the brief's `ckSeminorm_lt_top_of_contDiff_compact`, built from `ContDiff.continuous_iteratedFDeriv` + `IsCompact.exists_bound_of_continuousOn`.
- §2 `contDiff_crossAdvection_self` (`:126`), `affineForce_smul_sub` (`:137`, the scaling identity, closed by `module` after five operator rewrites), `affineVelocity_smul_sub` (`:181`).
- §3 `nonisolated` (`:197`).

`/data_8T/ping/blowup_density/.claude/worktrees/424-T24-Ua8-nonisolated/research/T24/probes/affine_nonisolated_closes.lean`:
- lane 398's nonzero witness `bWitness = ∇×(θ·φ·e₁)` on `ball 0 1 × (1/4,3/4)` rebuilt (lane 417's shared `Section3/T24/AffineWitness.lean` is confirmed absent from this base: `find` returns nothing);
- six `rfl` bridges (`SpaceTimeField_eq`, `ckSeminormE_eq`, `affineCylinder_eq`, `AffineAdmissible_eq`, `crossAdvection_eq`, `affineVelocity_eq`, `affineForce_eq`);
- `nonisolated_on_canonical` — the registered field discharged on `Bindings.packet ν hν` in Contracts vocabulary, fed only the packet's `velocity_smooth`;
- `nonzero_admissible_nonisolated` — both limits at the nonzero witness;
- `nonisolated_nontrivial` — at `λ = 1`, `m = 0` the velocity seminorm of the nonzero witness is **nonzero**, so the two `Tendsto` statements are limits of a not-identically-zero function (the check the `ℝ≥0∞` `⨆` choice exists for).

`research/T24/axioms_ua8.lean`, `research/T24/ATTEMPTS_UA8.md`, and the Ua8 **DONE (lane 424)** paragraph in `research/T24/T24_SPLIT.md`. All 8 module declarations and all 8 probe declarations print exactly `[propext, Classical.choice, Quot.sound]`. Committed as `89b1f894` on `erenup/424-T24-Ua8-nonisolated`; nothing pushed, merged, or rebased; no existing module touched.

## 3. Gaps

**None for Ua8** — the field is closed, with no residual statement and no error text. Everything attempted compiles. Two honest notes for the lead:

- The bound proved is `≤ ‖λ‖ₑ·‖F̃_b−F‖_{C^m} + ‖λ²−λ‖ₑ·‖(b·∇)b‖_{C^m}`, not literally the paper's `C_m|λ| + C_m'λ²`. Same content for the `Tendsto`; if a later unit ever needs the paper's exact two-constant form, it needs the pointwise-`ContDiffAt` version of `affineCkSeminorm_add_le` described above.
- `affineCkSeminorm_{const_smul,add_le,lt_top}` are general facts about the registered seminorm and are now reusable by Ua9/T24b; they were placed in this module rather than in the frozen `AffineBasics.lean` (no edits to existing modules).

**Negative mutation (added after the codex review, `REVIEW_424-T24-Ua8-nonisolated.md`):** three substantive mutations were run against scratch `/tmp` copies with the unchanged proof script and all three break — `𝓝 0 → 𝓝 1` on the velocity limit, dropping the `λ` from `affineVelocity U (lam • b) z − U z`, and the sign flip `λ²−λ → λ²+λ` in `affineForce_smul_sub`.  Mutation texts and the exact Lean error output are in `research/T24/ATTEMPTS_UA8.md` §3b; the second one is additionally proved **false** (not merely unprovable) in `/tmp/mut424_B_false.lean`.

Failed approaches, all recorded in `ATTEMPTS_UA8.md` §3, are Lean-spelling traps rather than mathematical dead ends. The one that actually cost time and is worth propagating: **`Contracts.V1.Packet` does not import `Contracts.V1.Data`**, so writing the Spec's `SpaceTimeField` in a probe silently becomes an `autoImplicit` type variable and produces eight misleading `has type SpaceTimeField but is expected to have type VelocityField` errors. Also: `h.mul_const` on an `ℝ≥0∞`-valued `Tendsto` resolves to the *generic* `Filter.Tendsto.mul_const` and fails with `failed to synthesize SeparatelyContinuousMul ℝ≥0∞` — `ENNReal.Tendsto.mul_const` must be written out. And `hf.of_le (by exact_mod_cast le_top)` works for a variable index `(k : ℕ)` but not for the numeral in `ContDiff ℝ 2 _`, where lane 398's `(WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))` is required.

## 4. Commands run and results

All from the worktree, after `. scripts/lean-env.sh`, `lake` from `verification/`:

- `LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T24.AffineNonisolated` → `Build completed successfully (3009 jobs).` (0 errors)
- `lake env lean ../formalization/NSFormalization/Section3/T24/AffineNonisolated.lean` → no output (0 errors)
- `lake env lean ../research/T24/probes/affine_nonisolated_closes.lean` → 8 `#print axioms` lines, every one `[propext, Classical.choice, Quot.sound]`
- `lake env lean ../research/T24/axioms_ua8.lean` → 8 lines, every one `[propext, Classical.choice, Quot.sound]`
- `make check` → `Ran 13 tests ... OK`, `45 work items: ownership, contract registration and task cards consistent.`, **EXIT 0**
- `grep` for `sorry|admit|native_decide|axiom` over the three new files → no hits (only the `#print axioms` lines)
- `LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T24.AffineForce` (base sanity, before starting) → `Build completed successfully (3008 jobs).`
