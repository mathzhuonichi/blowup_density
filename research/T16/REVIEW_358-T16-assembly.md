REJECT

## what the lane claims

The worker claims a general theorem localPotential : localPotentialStatement assembling seven correction fields (Assembly.lean:414-461), with canonical and Spec probes. research/T16/REPORT_358.md is absent.

## what is in Lean

localPotentialStatement is the quantified proposition ending in ∃ D : CutoffData, LocalPotentialAPI ... D (LocalPotential.lean:166-174). localPotential proves it and fills correction_formula through correction_cancels (Assembly.lean:455-461), using physical correction hypotheses (Assembly.lean:421-431). The module builds. However, the brief explicitly requires localPotentialData and localPotentialAPI; neither declaration exists anywhere in Section3/T16 (grep found no matches). The theorem directly constructs an anonymous structure (Assembly.lean:433-461).

## gaps

1. REJECT: missing required localPotentialData and localPotentialAPI declarations.
2. Required worker report research/T16/REPORT_358.md is missing.
3. Reviewer mutation research/T16/probes/rev352_widen_ball.lean:9-17 widens the key bound from ≤ 1 to ≤ 2; Lean breaks at line 17: “argument hρr has type r + ρ ≤ 2 but is expected to have type r + ρ ≤ 1”.
4. No Section4 localPotential lemma was found by rg -n "localPotential" formalization/NSFormalization/Section4.

## commands and results

- lake build NSFormalization.Section3.T16.Assembly: success, “Build completed successfully (9360 jobs)” (three deprecation warnings at Assembly.lean:327,332,362).
- lake env lean on Assembly.lean: success, same warnings.
- lake env lean on assembly_closes.lean and axioms_assembly.lean: success. Every printed declaration has exactly [propext, Classical.choice, Quot.sound].
- Hygiene search found no sorry/admit/axiom/native_decide/maxHeartbeats in Assembly.lean.
- lake env lean on rev352_widen_ball.lean: expected failure quoted above.
- make check from verification: failed to start: make: *** No rule to make target 'check'. Stop.
- scripts/gates.sh NSFormalization.Section3.T16.Assembly: completed build/test/mutation sequence; “Mutation suite passed.”
- python3 check_contracts.py --base-ref origin/erenup/integration-section3 from worktree root: failed because the script is at experiments/check_contracts.py, not root.


---

## fix note (worker r1, lane 358)

Addressed the REJECT items:

1. **Missing `localPotentialData` / `localPotentialAPI`** — added both to
   `Section3/T16/Assembly.lean`, factored out of the original `localPotential`
   with every existing declaration name and statement unchanged:
   - `def localPotentialData (v x₀ T θ η O θR ε₀) : CutoffData` — the `CutoffData`
     witness `⟨θ, η, O, θR, ε₀, timePotential v x₀, fun ε => latticeLift (physicalCorrection v x₀ T θ η ε)⟩`.
   - `theorem localPotentialAPI (v U K x₀ r T δ θ η O θR ε₀) (…hyps…) :
     LocalPotentialAPI v U K x₀ r T δ (localPotentialData v x₀ T θ η O θR ε₀)` —
     the fieldwise API proof (the former anonymous-structure body).
   - `theorem localPotential : localPotentialStatement` now returns
     `⟨localPotentialData …, localPotentialAPI …⟩`.
   Both added to `research/T16/axioms_assembly.lean` and to
   `research/T16/probes/assembly_closes.lean` (a `CutoffData` type-check and a
   tactic-mode `⟨localPotentialData …, localPotentialAPI …⟩` composition of
   `localPotentialStatement`), each `[propext, Classical.choice, Quot.sound]`.

2. **Report** — `research/T16/REPORT_358.md` (transcribed by the lead) updated
   with the new declaration names and the r1 gate outputs.

3. **Gates re-run from the correct locations** (the paths in the review were the
   root/`experiments` variants):
   - `make check` (worktree root) → 13 contract-policy tests OK, work queue
     consistent (45 items).
   - `python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3`
     (worktree root) → exit 0, `registered_contracts: 40`,
     `base_compatibility_checked: true`.
   - `lake build NSFormalization.Section3.T16.Assembly` → `Build completed
     successfully (9360 jobs)`; `lake env lean` on module/probe/axioms → 0 errors,
     only the three tolerated `if_pos`/`if_neg` deprecation warnings.

Note on review item 4 ("no Section4 localPotential lemma"): none is expected —
the T16 assembly lives in `Section3/T16`, and the reused chart lemmas are
`Section4.I02.*` / `Paper1.*` / `Source.PhysicalRemoval.*` (not named
`localPotential`).
