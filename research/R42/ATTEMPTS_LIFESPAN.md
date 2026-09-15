# R42 lifespan — attempts, dead ends, decisions (lane 072, split-and-start)

Companion to `LIFESPAN_SPLIT.md` (the sub-lemma split) and `ATTEMPTS.md` (the
assembly lane 027 record).  Scope: the two lifespan clauses of
`Contracts.V1.InsertionLifespanAPI`, split off and their **S** pieces proved in
`formalization/NSFormalization/Section4/R42/Lifespan.lean`.

## 1. Where the S pieces can live

`Lifespan.lean` sits in the `NSFormalization` package, an **upstream** Lake
dependency of `verification`, so it **cannot** import `Contracts.V1.*` (same
constraint as `Assembly.lean`, `ATTEMPTS.md §1`).  Therefore the S lemmas are
stated in `Mathlib` + `NavierStokes.ProblemStatement` vocabulary
(`Space = EuclideanSpace ℝ (Fin 3)`, `VelocityField = ℝ × Space → Space`), and
the eventual `verification/Bindings/*` will consume them against the versioned
notions.  The bridge is definitional in every case:
`MaximalPartial.speedENorm = eLpNorm · ⊤ volume`,
`MaximalPartial.limsupLeft T = Filter.limsup · (𝓝[<] T)`,
`D01.IsSobolevDatum = Contracts.V1.Data.IsSobolevDatum`.

The only import needed is `NSFormalization.Section4.D01.SmoothDatum` (for the
datum unit); it also transitively opens `NSFormalization.Paper3`
(for `RealVectorSobolev`) and `NavierStokes.ProblemStatement`.

## 2. Which "limsup transfer" to prove — Option A vs Option B

The task named the S piece "if `limsup ‖U‖_∞ = ⊤` and `‖w‖ ≤ C` then
`limsup ‖U + w‖_∞ = ⊤`" (Option B: transfer the *packet* essSup blow-up across a
bounded background).  I proved this (`limsup_eLpNormTop_add_eq_top`) **and** its
abstract core (`limsup_eq_top_of_le_add_const`).  But I record that Option B is
**not** the shortest route to feed `A02.lifespan_le_of_unbounded`: the assembly
already proves `blowup : SpeedUnboundedAt T u_ε` for the **full** `u_ε`
(`InsertionFamilyAPI.blowup`), so the direct route (Option A) — pointwise
blow-up of `u_ε` + slice continuity ⟹ essSup `limsupLeft = ⊤` — avoids needing a
uniform bound on `v + w_ε` near `T` (the reference velocity `v` is a general
`H^∞` solution, not obviously uniformly bounded on the closed slab up to `T`;
that bound is itself an M lemma).  Both routes share the *same* residual M step
(2a in the split): a pointwise value ⟹ essSup lower bound via slice continuity
and `IsOpenPosMeasure volume`.  Recorded in `LIFESPAN_SPLIT.md §2`.  I proved
Option B because it was the named S piece and is genuinely reusable; the binding
should prefer Option A.

## 3. The `u_ε` compact-support question — resolved: only the *difference* is compact

The task asked whether `u_ε(t,·)` is compactly supported at each time so that
`ClassicalSolutionR.sobolev` is the "D01 compact-support case".  It is **not**:
`u_ε = v + w_ε + U_ε`, and the reference velocity `v` is a general `H^∞` field
with no compact support.  What **is** compactly supported is the **difference**
`u_ε(t,·) - v(t,·) = (w_ε + U_ε)(t,·)`, whose `tsupport ⊆ ball x₀ r`
(`InsertionFamilyAPI.velocityDifference_support`).  So the `sobolev` field for
`u_ε` is **not** a single compact-support datum; it is
`datum(v)` [from `reference.sobolev`, non-compact] **plus** `datum(w_ε + U_ε)`
[the D01 compact-support case].  The compact-support S lemma
(`hasCompactSupport_of_tsupport_subset_ball`) and the datum lemma
(`exists_isSobolevDatum_of_contDiff_hasCompactSupport`) therefore apply to the
**correction**, and the additive combination with the reference datum path is
the missing D01 unit (1e).  This corrects the task's framing and is the key
structural finding of the split.

## 4. Lean frictions worth recording

1. **`add_le_add_right` orientation.**  `(hle a).trans (add_le_add_right ha.le C)`
   elaborated to `C + g a ≤ C + b` (wrong side) and failed the `trans`.  Fixed by
   `(hle a).trans (by gcongr)` — `gcongr` picks the correct
   `g a + C ≤ b + C` and closes the `g a ≤ b` side goal from `ha : g a < b`
   automatically (so a trailing `exact ha.le` errors "no goals").
2. **`RealVectorSobolev` unknown.**  It lives in `NSFormalization.Paper3`; the D01
   restatement `IsSobolevDatum (s) (z) (A : RealVectorSobolev s)` needs
   `open NSFormalization.Paper3` in addition to `open NSFormalization.Section4.D01`.
3. **`ContDiff ℝ ∞` vs `ω` in `continuous_iteratedFDeriv`.**
   `ContDiff.continuous_iteratedFDeriv le_top hz` fails: `le_top` forces the
   smoothness index to `ω` (analytic, the true `⊤` of `WithTop ℕ∞`), but
   `hz : ContDiff ℝ ∞ z` has index `∞ = ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ ω`.  The needed
   `↑n ≤ ∞` is `by exact_mod_cast le_top` (cast of `(n : ℕ∞) ≤ ⊤`).
4. **essSup ≤ constant.**  `eLpNormEssSup_le_of_ae_nnnorm_bound` wants an `NNReal`
   bound.  Use `(C := C.toNNReal)`; `ENNReal.ofReal C = ↑C.toNNReal` holds
   **definitionally**, so the conclusion `≤ ofReal C` needs no rewrite (an
   `ENNReal.ofReal_eq_coe_nnreal` rewrite there left a stuck `NormedAddCommGroup`
   metavariable — avoid it).  The a.e. bound `‖w x‖₊ ≤ C.toNNReal` is
   `← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal C hC`.
5. **`eLpNorm_add_le` at `p = ⊤`** needs `1 ≤ (⊤ : ℝ≥0∞)` (`le_top`) and
   `AEStronglyMeasurable` of both summands; the reverse triangle
   `‖u‖ ≤ ‖u+w‖ + ‖w‖` is `u = (u+w) + (-w)` then `eLpNorm_neg`.

## 5. Not attempted, and why

* **The remaining M pieces** (split 1e-i datum-path *time-continuity*; 1f
  `pressure_gradient`; 2a pointwise⟹essSup; the R42-V2 `RegularThrough (T+δ)`/`hg`
  contract shapes for #6/#3).  Out of scope for a split-and-start; stated precisely
  in `LIFESPAN_SPLIT.md`.  The task said stop at the L pieces.
* **`ScalingAPI.scaledBlowup` in essSup form.**  Left to the binding: it needs the
  same 2a step and is contract-side.

### Review fixes (post-review, `research/R42/REVIEW_LIFESPAN.md`)

The first draft of §5 (and of `LIFESPAN_SPLIT.md`) inherited two **stale** claims
from `research/R42/ATTEMPTS.md §5` (lane 027), which lane 028
(`D01/ForceClass.lean`) had already superseded — I cited `ATTEMPTS.md §5` without
re-checking it.  Corrected:

1. **`IsSobolevPath` additivity is NOT missing.**  `D01.isSobolevDatum_add`
   (`ForceClass.lean:261`, registered `DatumLemmas.lean:296`) and
   `D01.isSobolevPath_add` (`:320`, registered `:309`) exist and are registered
   contract fields.  So split 1e is **not** L: additivity + `ContinuousOn.add`
   are done, and the only residual is **1e-i time-continuity** of the correction
   datum path, an **M** via `D01.contDiff_angularPath` (`ForceClass.lean:133`) after
   a time cutoff at `S < T`, then `isSobolevDatum_unique` to transfer back.
2. **`F_R + C_c^∞ ⊆ F_R` is proved and even R42-specialised.**
   `D01.memForceR_of_compact_difference` (`ForceClass.lean:401`, registered
   `DatumLemmas.lean:381`) takes exactly `MemForceR g` + `MemForceCompact (g_ε - g)`.
   Split #3 is therefore **S** — now **proved** here as `memForceR_insertedForce`
   (⇐ that lemma), whose `hd` slot is `InsertionFamilyAPI.forceDifference_compact`.
   Only residual: the `hg : MemForceR g` hypothesis field (R42-V2).
3. **Strict reference clause (#6) has a one-step S route.**  Under the paper's own
   hypothesis "regular through `T+δ`" (`RegularThrough ν a g (T+δ)`,
   `02-preliminaries.tex:34-36`, `04-whole-space.tex:32`),
   `A02.regularThrough_iff` at `T' = T+δ` gives the field directly — **proved** here
   as `lt_maximalLifespanR_of_regularThrough`.  The earlier "take `family.margin :=
   δ_A`" option is not available (`margin` is a projection of a universally
   quantified `ScalingAPI`); the residual is only that `InsertionFamilyAPI.reference`
   was weakened to the half-open `[0,T+δ)`, so a correct-strength R42-V2 must carry
   `RegularThrough (T+δ)` (or read `reference` on `Icc 0 (T+δ)`).

Lean added for 2 and 3 (no other Lean change requested): `memForceR_insertedForce`,
`lt_maximalLifespanR_of_regularThrough` in `Lifespan.lean`; imports widened to
`D01.ForceClass` and `A02.Order`; both standard-3-axioms.  Frictions: none new — the
two lemmas are single applications of registered units.  Name clash avoided by
opening `NSFormalization.Section4.A02` only `in` the reference lemma (both `A02` and
`D01` define `MemForceR`; the force lemma uses the file-level `open D01`).

## 6. Gates

From WT root, `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, lake from
`verification`.

| command | result |
|---|---|
| `bash scripts/lean-install.sh` | exit 0 |
| `lake build NSFormalization.Section4.R42.Lifespan` | `Built … Lifespan (2.7s)`, `Build completed successfully` |
| `lake env lean …/Lifespan.lean` | empty output (no warning/error; linter-clean) |
| `lake env lean research/R42/axioms_lifespan.lean` | all **8** decls `[propext, Classical.choice, Quot.sound]` (6 original + `memForceR_insertedForce`, `lt_maximalLifespanR_of_regularThrough`) |
| `make check` | exit 0 (plan check, `check_contracts`, policy tests, work items) |

No `sorry`, `axiom`, `native_decide`, `admit`, or placeholder field.
