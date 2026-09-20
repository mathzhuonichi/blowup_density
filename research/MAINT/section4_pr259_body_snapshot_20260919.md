## erenup lane, waves 6–81: Section 4 (whole space, Theorems 4.1–4.7) formalized and registered

**Scope of this batch** (`erenup/integration` → `main`): everything since PR #15 — lanes 011–262 (plus the Section 3 kickoff lanes 263/264, specification drafts only) of `PLAN.md` §8, 205 local Lean modules under `formalization/NSFormalization/Section4/`, and 37 registered contracts (was 6). Every registered contract is `Contracts/V*` + `Bindings` + `Tests` with `TestSupport.checkAxioms` (transitive axioms exactly `[propext, Classical.choice, Quot.sound]`); `make check`, `make test`, `make test-mutations` and `check_contracts.py --base-ref main` pass locally on every merge (CI `cancel-in-progress`: gates run locally per lane, see `logs/AGENT_RUNS.csv`).

### Theorems (contract ids)
- **Theorem 4.1 (thm:Rmain, Y = F_R)** — `R41.main_thresholds` V1: fixed-initial density, zero-datum iff, threshold values, regular-reference rider (lanes 224/229/232/233/235/249).
- **Theorem 4.2 (thm:Rinsert)** — `R42.insertion_family`, `R42.insertion_lifespan` (+V2), `R42.correction`; the record-from-raw-data constructor (233).
- **Proposition 4.3 (prop:Rcritical1)** — `R43.critical_regularity` V1: both clauses with one explicit constant (175–226).
- **Proposition 4.4 (prop:Rcritical2)** — `R44.critical_finite_horizon` V1 (166, 218–231).
- **Corollary 4.5 (cor:Rclasses)** — `R45.force_classes` V1 (234, 252–262).
- **Proposition 4.6 (prop:Renergy)** — `R46.completed_density` V1 (256, 259, 261; I03 homogeneous scaling 250/255).
- **Theorem 4.7 (thm:Rgrid)** — `R47.grid_observations` V1 (247, 251, 253, 258, 260).
- Local theory / continuation: `A01.regularity_partial` V1, `A01.local_theory_v2`, `A02.uniqueness`, `A02.maximal_partial` (+V2), `A04.energy_high_partial` (+V2), `A04.continuation_v2`, plus the D01/A03/A05/B01/B02/C01/I01–I03 supplier contracts.

### Statement fidelity
Every contract statement was written from the paper by two mutually blind drafts and reconciled by the lead (`research/<ID>/RECONCILIATION.md`, `COMPARISON.md`); `research/section4/STATEMENTS.md` has the overview. **Two documented narrowings for the owner's decision** (`research/A01/V2_DECISION.md`): A01 `horizon_lower_bound` and A04 `Restart` are registered in V2 with the fixed-force/H⁷ wording the tree proves (uniform over restart times); the paper's H¹, force-uniform sentence is kept verbatim as an explicitly **open** named definition (`ManuscriptHorizonLowerBoundH1`) and is not claimed. All downstream theorems use only the V2 form. Open vocabulary question: `mixedLebesgueENorm 1 2` (R47 spec) vs `forceSobolevENorm 1 0` (R46 spec) for the same `L¹_tL²_x` term (not definitionally equal; `research/R47/COMPARISON.md`).

### Process
Codex (gpt-5.6-sol / gpt-6-astra) workers in tmux, one lane = one PR to `erenup/integration`, codex review with probes and mutation checks, lead merge + gates; records in `PLAN.md` §8, `logs/AGENT_RUNS.csv`, `logs/LESSONS.md`, `NEXT_SESSION.md`; per-lane reports `research/<ID>/REPORT_<lane>.md`.

🤖 Generated with [Claude Code](https://claude.com/claude-code)

