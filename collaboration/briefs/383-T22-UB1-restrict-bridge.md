# Lane 383-T22-UB1-restrict-bridge — T22 U-B1: the T22 canonical vocabulary module + the restriction bridge `restrictDatum_eq_restrictField` and the left conjunct `domainSobolevENorm_le_sobolevENorm`

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/383-T22-UB1-restrict-bridge` (git branch `erenup/383-T22-UB1-restrict-bridge`, based on `origin/erenup/integration-section3`).
Read `CLAUDE.md`, **`research/T22/T22_SPLIT.md` §0 and unit U-B1 (and U-A5/U-Z1 for how it is consumed)**, **`research/T22/Spec.lean`** (the reconciled statement: `DomainTest`,
`restrictDatum :62`, `domainSobolevENorm :72`, `restrictField :81`, `zeroExtension :89`, `IsCutoffDatum :99`, `structure BoundedDomainNormAPI :114` — token-for-token source),
`research/T22/RECONCILIATION.md`, `research/T22/COMPARISON.md`, the registered whole-space data layer `Section4/D01/*.lean` (`IsSobolevDatum`, `angularRealization`, `RealVectorSobolev`,
`sobolevENorm` — grep the exact names the Spec's copied block uses and the canonical modules they come from), the canonical-module lanes as templates (`Section3/T16/LocalPotential.lean`
+ `research/T16/probes/api_on_canonical.lean`; `Section3/T15/Bridges.lean`), and the top 40 lines of `logs/LESSONS.md` (**name every instance explicitly**).

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- **No placeholders, no aliases, no named inputs, no goal repackaging.** An honest partial with the exact residual statement and error text beats a stub.
- Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`.

## Goal
1. The T22 canonical vocabulary module `formalization/NSFormalization/Section3/T22/Domain.lean` (namespace `NSFormalization.Section3.T22`): the Spec's definitions (`DomainTest`,
   `restrictDatum`, `domainSobolevENorm`, `restrictField`, `zeroExtension`, `IsCutoffDatum`) restated verbatim over the canonical Section 4 D01 vocabulary (import, never copy D01), and
   `structure BoundedDomainNormAPI : Prop` restated token-for-token; probe `research/T22/probes/api_on_canonical.lean` restating the Spec's definitions and proving each equal to the
   module's by `rfl` (fieldwise conversion for the structure if needed; no inhabitant).
2. `formalization/NSFormalization/Section3/T22/RestrictBridge.lean`: `theorem restrictDatum_eq_restrictField {Ω s z A} (hA : IsSobolevDatum s (zeroExtension Ω z) A) : restrictDatum Ω s A = restrictField Ω z`
   (route: for a `DomainTest ψ` with `tsupport ψ ⊆ Ω`, `angularRealization s (A i) ψ = ∫ x, ψ x * (zeroExtension Ω z) x i` by `IsSobolevDatum`; split the integral on `Ω`/`Ωᶜ`,
   `zeroExtension Ω z = z` on `Ω` and `ψ = 0` off `tsupport ψ ⊆ Ω`, giving `∫ x in Ω, ψ x * z x i = restrictField Ω z i ψ` — match the exact spellings of the Spec's definitions),
   and the corollary `domainSobolevENorm_le_sobolevENorm : domainSobolevENorm Ω s (restrictField Ω z) ≤ sobolevENorm s (zeroExtension Ω z)` (the left conjunct of
   `zeroExtensionComparison`, verbatim in the field's spelling — read `Spec.lean:114-…` and match), via the two `⨅` families (`iInf` monotonicity: every datum of the zero extension
   restricts to a datum of the restricted field).

## Deliverables
1. `Section3/T22/Domain.lean`, `Section3/T22/RestrictBridge.lean`; 2. probes `research/T22/probes/api_on_canonical.lean` and `research/T22/probes/restrict_bridge_closes.lean` (the
left conjunct instantiated on a concrete smooth compactly supported `z` with `Ω = ball 0 1`); 3. `research/T22/ATTEMPTS_UB1.md`, `research/T22/axioms_ub1.lean`, status in
`research/T22/T22_SPLIT.md` U-B1, report `research/T22/REPORT_383.md`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T22.RestrictBridge` (0 errors), `lake env lean` on both modules, both probes and the axioms file; `make check`.

## Report
Commit on your branch; end with four parts. Also write it to `research/T22/REPORT_383.md`.
