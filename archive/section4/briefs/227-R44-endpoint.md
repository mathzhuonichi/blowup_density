# Lane 227-R44-endpoint — R44 rows S2→S6 assembled: from the S1 differential inequality (eq:Rcritical2, taken as a named input) to Proposition 4.4's conclusion `T_max(0,f) > S` for `‖f‖_{L²_tH^{-1/2}} < r_{ν,S}`

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/227-R44-endpoint` (git branch `erenup/227-R44-endpoint`, based on `origin/erenup/integration`, which contains lane 166's `Section4/R44/Pieces.lean`
(the R44 scalar layer: constants, radius algebra, Grönwall + first exit — "closed"; S2 "closed conditionally" on the S1 input; read every declaration), lane 218's `R44/JWeight.lean`
(`Y`, `Z`, `B`, `JWeightDatum`), lane 222's `R44/EnergyIdentity.lean` (`jWeightDatumPath`, `energy_identity` along classical solutions), lane 221's `R43/ForcePath.lean` and lane 223's
`R43/Endpoint.lean` + lane 225's `R43/Universal.lean` (**the template**: the same S3→S4→S5 assembly for Prop. 4.3 — slice bootstrap → `L³` gate → C01 V4 absorbed eq:RH1 → explicit `H²` budget →
G5 endpoint gluing (`MaximalEndpoint.lean`) → A02 `exists_maximal'` → A04 `lifespanInfiniteOfLocallyFinite_of_memForceR'`/`extendsBeyond_of_memForceR'` (217)), A05 V2
(`velocityCriticalL3`), C01 V4 (`verification/Contracts/V4/EnergyAbsorption.lean`, `Bindings/EnergyAbsorptionV4.lean`)). Read `research/R44/R44_SPLIT.md` in full (`:53-64` the clean
S1 target — copy it token for token as the named input `RCritical2Differential w`; `:82-120` S2; `:121-143` S3; `:144-175` S4 with G5; `:176-200` S5; `:201-230` S6 and the exact `a = 0`
API clause `RCritical2API` consumes; `:231-246` the gap ledger), `research/R44/Spec.lean:169-230` (the `RCritical2API` structure — the target fields, token for token), `research/R44/COMPARISON.md`,
`REPORT_166.md`, `REVIEW_166-R44-split.md`, `REPORT_218.md`, `REPORT_222.md`, `research/R43/REPORT_223.md`, the paper `04-whole-space.tex:136-175` (Prop. 4.4 and its proof: Grönwall
`Y(t)² ≤ C₃ν⁻¹e^{C₂νS}‖f‖²_{L²H^{-1/2}}`, radius `r_{ν,S}` keeping `Y ≤ θν` by first exit, then eq:RH1 gives `∫₀ˢ‖u‖²_{H²} < ∞`, hence `T_max > S`), `CLAUDE.md`, `collaboration/HANDOFF.md` §0 and §2 P6,
and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
  Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`; non-vacuity `example` (`f = 0`; and `A04.zeroSol` satisfies the named input with `E' = 0`).
- **Satisfiability rule / peeling:** the ONLY permitted named input is the S1 target `RCritical2Differential` (the split's `:56-64` statement, assembled as one `E' : ℝ → ℝ` with
  `IntervalIntegrable E' volume 0 S` per `Pieces.lean:162-163`), which lane 222 + lane 220 (S1c) + the pending S1d will discharge. Everything else must close from the tree.
- **Statement fidelity:** the final theorem is `RCritical2API`'s conclusion field for `a = 0` (copy from `Spec.lean`), with the radius `r_{ν,S}` explicit.

## Goal
1. `structure RCritical2Differential (w : ClassicalSolutionR ν (fun _ => 0) f T) (hf : MemForceR f) : Prop` — exactly the S1 target (`theta`, `C₂`, `C₃` universal constants as `def`s with
   positivity; `E'` integrable).
2. S2 instance: feed it to `Pieces.lean`'s conditional Grönwall/first-exit results to get `∀ t ∈ Icc 0 S, Y t ≤ theta·ν` for `‖f‖_{L²_tH^{-1/2}} < r_{ν,S}` (explicit `r`), for `S < T`.
3. S3: the `L³` gate from `Y ≤ theta·ν` (`velocityCriticalL3` + `dotHomogeneousENorm ≤ sobolevENorm`; the `ν`-free arithmetic like R43's `criticalL3_gate_enorm`).
4. S4: the finite `H²` budget on `(0,S)` from C01 V4 with zero datum (223's route; note the force enters through `∫₀ˢ‖f‖²₂` — for `MemForceR` finite), G5 endpoint gluing.
5. S5/S6: A02 maximal solution + A04 continuation ⇒ `ENNReal.ofReal S < maximalLifespanR ν (fun _ => 0) f` (or `= ⊤`-style if the spec says so — copy the spec), i.e. the `RCritical2API`
   field `…` conditional only on `∀ w, RCritical2Differential w hf` (state the conditional theorem `rcritical2_endpoint_of_differential` and the unconditional-shape corollary skeleton
   `rcritical2_endpoint` that S1d will instantiate — do not fake the latter).

## Deliverables
1. New module `formalization/NSFormalization/Section4/R44/Endpoint.lean` (namespace `NSFormalization.Section4.R44`).
2. Records `research/R44/ATTEMPTS_ENDPOINT.md`, update `R44_SPLIT.md` rows S2–S6/G4/G5 and `COMPARISON.md`, conformance `research/R44/axioms_endpoint.lean` (incl. a `Contracts.V1.Data`-vocabulary
   conformance theorem as 223 did).

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.R44.Endpoint` (silent), `lake env lean` on the module (0 output), the axioms file, `make check`.

## Report
Commit on your branch; end with four parts. Also write it to `research/R44/REPORT_227.md`.
