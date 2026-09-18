# REPORT_393 — T22 U-A5 `orderZero` (Opus; transcribed by lead from the agent message, report-file guard)

Everything is green on the committed branch. Here is my final report.

---

# Lane 393 — T22 · U-A5 — `orderZero` (COMPLETE)

**Commit:** `1f5078bd330325adce9178aea13e91aee25a3d01` on branch `erenup/393-T22-UA5-orderzero` (not pushed/merged).

## 1. What was proved (exact statements)

New module `/data_8T/ping/blowup_density/.claude/worktrees/393-T22-UA5-orderzero/formalization/NSFormalization/Section3/T22/OrderZero.lean` proves the `orderZero` field of the canonical `BoundedDomainNormAPI` **verbatim** (`Section3/T22/Domain.lean:59-62` = `research/T22/Spec.lean:125-128`):

```
theorem orderZero (Ω : Set Space) (hΩ : IsOpen Ω) (z : SpatialField)
    (hz : ContDiffOn ℝ ∞ z Ω) :
    domainSobolevENorm Ω 0 (restrictField Ω z) = eLpNorm z 2 (volume.restrict Ω)
```

Both sides may be `⊤`; no compact-support or `L²` hypothesis. `orderZero`'s type equals the structure field type (probe checks it with `exact BoundedDomainNormAPI.orderZero` / `exact orderZero`).

Supporting theorems proved in the same module (no named inputs, no placeholders, no goal repackaging):
- `orderZeroDatum_surjective (A : RealVectorSobolev 0) : ∃ (w : Space → Space) (hw : MemLp w 2 volume), orderZeroDatum hw = A` — order-0 realization surjectivity (**not** previously in the tree, confirmed by two independent searches).
- `restrictField_eq_ae (hΩ : IsOpen Ω) (hw : MemLp w 2 volume) (hz : ContDiffOn ℝ ∞ z Ω) (heq : restrictField Ω w = restrictField Ω z) : w =ᵐ[volume.restrict Ω] z` — du Bois-Reymond.
- `conjugation_fourierInv_of_mem {h} (hh : h ∈ realSubspace 0) : conjugation (𝓕⁻ h) = 𝓕⁻ h` (+ a.e.-real form `fourierInv_ofReal_re_ae`) — the missing bridge for surjectivity.
- `restrictDatum_eq_restrictField_of_datum {Ω s z A} (hA : IsSobolevDatum s z A) : restrictDatum Ω s A = restrictField Ω z` — general datum-restriction bridge.
- `sobolevENorm_zero_eq_eLpNorm (hw : MemLp w 2 volume) : sobolevENorm 0 w = eLpNorm w 2 volume`.
- `fieldOf` / `memLp_fieldOf` — assemble a `Space → Space` field from three complex `L²` classes by real parts.

Every declaration (including `orderZero`) prints exactly `[propext, Classical.choice, Quot.sound]`.

**Route.** `≤`: the zero extension `E₀z = Ω.indicator z` is `L²` when the RHS is finite (`memLp_indicator_iff_restrict`); `domainSobolevENorm_le_sobolevENorm` (lane 383) + `sobolevENorm_zero_eq_eLpNorm` + `norm_orderZeroDatum_eq` (lane 387) + `eLpNorm_indicator_eq_eLpNorm_restrict`; the `⊤` case is `le_top`. `≥`: every `A` is `orderZeroDatum hw` of some `L²` field `w` (surjectivity); if `A` restricts to `restrictField Ω z` then `restrictField Ω w = restrictField Ω z`, so `w =ᵐ z` on `Ω`, and `eLpNorm z 2 (restrict Ω) = eLpNorm w 2 (restrict Ω) ≤ eLpNorm w 2 volume = ‖A‖ₑ`. The `⊤ = ⊤` edge is automatic: `‖A‖ₑ < ⊤` always, so the constraint family is empty exactly off `L²(Ω)`.

## 2. Files (all absolute)

- `/data_8T/ping/blowup_density/.claude/worktrees/393-T22-UA5-orderzero/formalization/NSFormalization/Section3/T22/OrderZero.lean` — the module.
- `/data_8T/ping/blowup_density/.claude/worktrees/393-T22-UA5-orderzero/research/T22/probes/orderzero_closes.lean` — probe: field-type match by `exact`, plus a nonzero `ContDiffBump` field on `Ω = ball 0 1` with the identity, both sides `< ⊤`, field nonzero.
- `/data_8T/ping/blowup_density/.claude/worktrees/393-T22-UA5-orderzero/research/T22/axioms_ua5.lean` — axiom audit of 8 declarations.
- `/data_8T/ping/blowup_density/.claude/worktrees/393-T22-UA5-orderzero/research/T22/ATTEMPTS_UA5.md` — positive/negative examples, heartbeat findings.
- `/data_8T/ping/blowup_density/.claude/worktrees/393-T22-UA5-orderzero/research/T22/T22_SPLIT.md` — U-A5 marked DONE.

No existing module was edited; only new files plus the split-doc status line.

## 3. Gaps / exact error text

**None for U-A5.** `orderZero` is proved verbatim, standard axioms, no `sorry`/`axiom`/`native_decide`. The realised `≥` route differs from the split doc's guess (it suggested `LocalizationBoundary.domainL2Sq_*`, which is `0<s<1` only and unusable at order 0); I used the quotient-norm identity both directions with the two new in-module facts. Out of this lane's scope: `cutoffMultiplier` (U-A3), `zeroExtensionComparison` (U-Z1), assembly/registration (U-REG).

Load-bearing pitfall for the reviewer: `cyclesToAngularRealVector 0 (e.symm A)` is *definitionally* `A`, so a trailing `rfl` inside `rw`/`conv` closes the goal **nondeterministically** (sometimes `(deterministic) timeout at isDefEq, maximum number of heartbeats (200000)` — the lane-387 heavy unification). The deterministic close is `simp only [hkey, ContinuousLinearEquiv.apply_symm_apply]` inside the commented `set_option maxHeartbeats 400000` on `orderZeroDatum_surjective` (the only raised-heartbeat declaration; all others pass at 200000).

## 4. Commands run and results

From the worktree, each shell `. scripts/lean-env.sh`, `lake` from `verification/`, `LEAN_NUM_THREADS=6`:
- `lake build NSFormalization.Section3.T22.OrderZero` → `✔ Built NSFormalization.Section3.T22.OrderZero`; `Build completed successfully (9931 jobs).`
- `lake env lean ../research/T22/axioms_ua5.lean` → all 8 declarations (incl. `orderZero`, `orderZeroDatum_surjective`, `restrictField_eq_ae`) `depends on axioms: [propext, Classical.choice, Quot.sound]`.
- `lake env lean ../research/T22/probes/orderzero_closes.lean` → no errors; `T22ProbeA5.probe_closes depends on axioms: [propext, Classical.choice, Quot.sound]`.
- `make check` → contract policy 13 tests `OK`; architecture checks pass; `45 work items: ownership, contract registration and task cards consistent.`

---

The REPORT_393.md write was guard-blocked (subagent report-file rule); the full four-part report is the message above. The report content is also captured in `ATTEMPTS_UA5.md` and the T22_SPLIT.md U-A5 status block on the branch.
