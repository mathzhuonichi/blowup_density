# Lane 179-A01-gronwall-endpoint — A01 residual row (iii-b): the Grönwall bound at the closed endpoint `t = T` (HANDOFF P9b)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working
directory `/data_8T/ping/blowup_density/.claude/worktrees/179-A01-gronwall-endpoint` (git branch
`erenup/179-A01-gronwall-endpoint`, based on `origin/erenup/integration`). Read `CLAUDE.md`,
`collaboration/HANDOFF.md` §0 and §2 P9 (P9b), `research/A01/REVIEW_APRIORI_ROWS.md` §"Residual-row audit"
(rows (iii-a′) cap at `T₀ = T` — done in lane 149 as `AprioriRows.kbnd_of_sup_bound_Icc_endpoint`; (iii-b′)
cylinder endpoint — free, probe `rev149_cylinder_endpoint.lean`; **(iii-b) Grönwall output at `t = T`** — the
eq:criterion endpoint, L), `research/A01/A3_SPLIT.md`, and the top 40 lines of `logs/LESSONS.md` first.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`,
  commented. No edits to existing modules; new files only.
- Before claiming a lemma is "not in the tree", `grep -rn` all of `Section4/{D01,A03,A04,A01,C01}`, `Source/`,
  `Paper1/`. Before citing a paper line, `sed -n` it.
- Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`; include a non-vacuity `example`
  on `A04.zeroSol`.

## The problem
`Section4/A01/GronwallInstance.lean` `highOrder_bddAbove_of_kbnd` (`:72`) gives, from the cap
`hkbnd : ∀ t ∈ Ico 0 T₁, ∫₀ᵗ sobolevNormAt 2 w.velocity s² ≤ Kbnd`, the explicit bound
`sobolevNormAt m w.velocity t ≤ (sobolevNormAt m w.velocity 0 + ‖f‖_{L¹H^m})·exp(Cgron m ν·Kbnd)` on `Ico 0 T₀`
(lane 149 widened it to `Icc 0 T₀` for `T₀ < T₁ ≤ T`, `AprioriRows.highOrder_bddAbove_of_kbnd_Icc`). The cap
itself now exists on the closed `Icc 0 T` (`kbnd_of_sup_bound_Icc_endpoint`). What is missing is the Grönwall
**output** at the endpoint `t = T`: the solution class `ClassicalSolutionR ν a f T` lives on `Ico 0 T` (no
value at `T`), so "the bound at `t = T`" must be read as: **`sobolevNormAt m w.velocity` is bounded on all of
`Ico 0 T` by the endpoint constant** (`sup_{t < T} ≤ (…)·exp(Cgron·256R²T)`), i.e. the bound does not degrade as
`t ↑ T`. That is exactly what eq:criterion (`02-preliminaries.tex:108-114`) and A04's continuation consume: a
uniform `H^m` bound on `[0,T)` implies extension beyond `T` (`research/A04/Spec.lean` `extendsBeyond`,
`restartBeyond` — the owner's PR #161 to `main` proves the conditional versions; on `origin/erenup/integration`
they may be absent — grep). Paper: `04-whole-space.tex:113-121` (eq:RH1 + criterion), `02-preliminaries.tex:108-114`.

## Deliverables
1. New module `formalization/NSFormalization/Section4/A01/GronwallEndpoint.lean` (namespace
   `NSFormalization.Section4.A01`):
   - `highOrder_bddAbove_of_kbnd_Ico_full`: the explicit bound on **all** of `Ico 0 T` with `Kbnd := 256·R²·T`
     (feed `kbnd_of_sup_bound_Icc_endpoint` into `highOrder_bddAbove_of_kbnd` at horizon `T₁ = T`, or into the
     `T₁`-parameterized `_Icc` version with `T₀ ↑ T` — state which; the constant must be the endpoint constant,
     not degrading in `T₀`);
   - `highOrder_bddAbove_all_orders_Ico_full`: `∀ m ≥ 3, BddAbove (range (fun t : Ico 0 T => sobolevNormAt m w.velocity t))`;
   - the hand-off shape for A04's criterion: the uniform bound in the exact form `A04`'s `extendsBeyond` /
     `restartBeyond` input needs (`∀ t ∈ Ico 0 S, sobolevENorm 1 (u (t,·)) ≤ K` with `K ≠ ⊤` — see
     `research/A04/Spec.lean` `restartBeyond`'s hypothesis and `research/A04/COMPARISON.md:216-217`), derived
     from the `m = 1` (or `m = 3` lowered) bound.
2. Record `research/A01/ATTEMPTS_GRONWALL_ENDPOINT.md` (incl. what the *true* endpoint obligation of row (iii-b)
   still is after this lane — e.g. whether A02's `restart` then closes `HasAprioriBound`'s circle
   `Kbnd = Kbnd(R)`); update `A3_SPLIT.md` row (iii-b); conformance `research/A01/axioms_gronwall_endpoint.lean`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A01.GronwallEndpoint` (silent),
`lake env lean` on the module (0 output), the axioms file, `make check` from the worktree root.

## Report
Commit on your branch; end with four parts (theorems with exact statements / files / gaps with error text /
commands). Also write it to `research/A01/REPORT_179.md`.
