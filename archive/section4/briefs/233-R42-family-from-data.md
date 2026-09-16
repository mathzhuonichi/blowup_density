# Lane 233-R42-family-from-data — R41D gap G1: from raw data `(ν, T, a ∈ X_R, g ∈ F_R)` with `ofReal T < maximalLifespanR ν a g`, construct the registered R42 insertion record `InsertionLifespanV2API ν P` with `family.a = a`, `family.g = g`, `family.T = T`

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/233-R42-family-from-data` (git branch `erenup/233-R42-family-from-data`, based on `origin/erenup/integration`). Read `CLAUDE.md`,
`collaboration/HANDOFF.md` §0 and §2 P10, the top 40 lines of `logs/LESSONS.md`, then the target: `research/R41D/COMPARISON.md` §3 gap **G1** (`:64`, exact Lean shape:
`∀ ν, 0 < ν → ∀ T, 0 < T → ∀ a ∈ initialClassR, ∀ g, MemForceR g → ENNReal.ofReal T < maximalLifespanR ν a g → ∃ (P : PacketAPI ν) (L : Contracts.V2.InsertionLifespan.InsertionLifespanV2API ν P), L.family.a = a ∧ L.family.g = g ∧ L.family.T = T`
— note this quantifies over the **contract** structures in `verification/Contracts`; `formalization/` cannot import `Contracts`, so this lane lives in `verification/Bindings/` or
`research/R41D/` as a binding-layer theorem — decide: the cleanest is a new file `verification/Bindings/InsertionFromData.lean` (Bindings may import Contracts and formalization) plus its
axiom audit; do not touch existing Bindings/Tests), `research/R41D/Spec.lean` (`RDensityAPI`, `IsR41DForceClass`, the density fields and how the second arm uses the record),
`research/R41D/RECONCILIATION.md`, then the supply chain, bottom-up: `verification/Contracts/V1/Packet.lean` (`PacketAPI ν` — the blow-up packet; find its **witness** in `Bindings/`
(grep `PacketAPI` in `verification/Bindings/*.lean`; I01/U-lanes) — it must exist for every `ν > 0`), the correction layer (`Contracts/V1/Correction.lean`, `Contracts/V2/Correction.lean`,
`Bindings/Correction*.lean`: how a `CorrectionAPI` is built from a reference classical solution `(v, π, g)` on a slab `[0, T+δ)` and a packet — what inputs its constructor takes: `RegularThrough`?
a `ClassicalSolutionR ν a g (T+δ)`? a compact spatial ball?), the scaling layer (`Contracts/V1/Scaling.lean`, `Bindings/Scaling*.lean`: `ScalingAPI ν P` from a correction), the family
(`Contracts/V1/InsertionFamily.lean:125-330` `InsertionFamilyAPI ν P` with fields `scaling`, `a`, `reference : ClassicalSolutionR ν a scaling.correction.g`, `reference_velocity`, …;
`Bindings/InsertionFamily.lean` — its constructor from `S : ScalingAPI` and the reference), and the lifespan records (`Contracts/V1/InsertionFamily.lean:421-440` `InsertionLifespanAPI`,
`Contracts/V2/InsertionLifespan.lean:117-160` `InsertionLifespanV2API` with `solution`, `maximal`, `blowup_limsup`; `Bindings/InsertionLifespan.lean` (`lifespan_eq` needs `hg : MemForceR g`),
`Bindings/InsertionLifespanV2.lean`). Also `Bindings/MaximalPartial.lean:142` `maximalPartial_regularThrough_iff` (strict lifespan ⇔ `RegularThrough`) and A02's `Section4/A02` selection lemmas.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`. `verification/Tests` is `warningAsError`; Bindings are not, but keep them warning-free.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules/Bindings/Tests; new files only.
  Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`; non-vacuity: instantiate at some concrete admissible data if the tree has a witness (`a = 0`, `g = 0`, `T = 1`
  with `maximalLifespanR ν 0 0 = ⊤` — grep A04/R43 for that fact), else explain.
- **Satisfiability rule / peeling:** if a constructor in the chain is genuinely missing (e.g. `CorrectionAPI` from a slab-regular reference), isolate exactly that as ONE named hypothesis with
  its precise statement and prove G1 from it; record which supplier lane (I02/I03/R42) owes it.

## Goal
`theorem insertionLifespanV2_of_data : <G1 statement verbatim>` in `verification/Bindings/InsertionFromData.lean` (namespace `BlowupDensity.Bindings`), assembled as: strict lifespan ⇒
`RegularThrough ν a g T` ⇒ a `ClassicalSolutionR ν a g (T+δ)` ⇒ correction record ⇒ scaling record ⇒ family record (with `family.a = a`, `family.g = g`, `family.T = T` by construction —
check the field names for `T`/`g` on the family: `scaling.correction.g`, `scaling.correction.T`?) ⇒ `InsertionLifespanV2API` via the existing V2 binding. Plus the projections R41D's second arm
uses: `L.lifespan ε hε : maximalLifespanR ν a (L.family.force ε) = ofReal T` and `L.family.forceConvergence`.

## Deliverables
1. `verification/Bindings/InsertionFromData.lean`; audit `research/R41D/axioms_insertion_from_data.lean` (`lake env lean` from `verification/`).
2. Records `research/R41D/ATTEMPTS_G1.md`, update `research/R41D/COMPARISON.md` G1 row (closed / what named input remains and who owes it).

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build BlowupDensity.Bindings.InsertionFromData` (check the module name convention in `verification/lakefile*`), `lake env lean` on the file (0 output),
the audit, `make check`, `make test` (Bindings compile in the contract closure — confirm nothing registered breaks).

## Report
Commit on your branch; end with four parts. Also write it to `research/R41D/REPORT_233.md`.
