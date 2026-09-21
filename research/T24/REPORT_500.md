# Lane 500 — P5.3/P5.4 on Ω

## 1. Statements

Closed all four requested fields in
`NSFormalization.Section3.T24.OmegaRegions`:

- `region_agreement`: on each prescribed ball the finite sum equals its component.
- `region_blowup`: separate `SpeedUnboundedAtOn T (ball c_j r_j)` witnesses.
- `energy_bound`: `(energyEssSupOmega Ω T assembledVelocity)^2 ≤ ofReal (M² Σ ε_j)`.
- `dissipation_bound`: `(energyGradientOmega Ω T assembledVelocity)^2 = ofReal (D² Σ ε_j)`.

The proofs formalize revised `03-torus.tex:528–531`, with separate sequences as
specified at line 535. No periodization is used. The full Euclidean gradient is
the registered I02 gradient. Closed slice support lies strictly inside each ball;
restriction to Ω preserves both velocity and gradient norms. Disjoint supports
then give exact slice additivity. I03 supplies the original packet constants.

P5.3 commit: `7eeefa87`. P5.4 commit: `e9f1c0f7`.

## 2. Files and assembly interface

- `formalization/NSFormalization/Section3/T24/MultipleOmegaRegions.lean`:
  four target theorems and thirteen supporting lemmas; local `assembledVelocity`
  has exactly the `finiteVelocitySum` body.
- `formalization/blueprint/entrypoints.json`: new proof module registered.
- `research/T24/probes/p5b_closes.lean`: four field-shaped proofs ending in
  `exact`, after substituting the threaded assembled-velocity formula. Uses
  actual `ClassicalSolutionOmega` components, both component pins, and raw packet
  hypotheses; never assumes the target API is inhabited.
- `research/T24/axioms_p5b.lean`: all seventeen module theorem dependencies.
- `research/T24/ATTEMPTS_P5B.md`: proof routes, elaboration errors/fixes, edits.
- `research/T24/T24_SPLIT.md`: P5.3/P5.4 closure status.
- `formalization/blueprint/AXIOM_AUDIT.json`: refreshed source fingerprint/count
  after a successful full audit; all target results and coverage are unchanged.

Lane 501 instantiates `w := fun j => (component j).velocity`. Pass
`component_pin j |>.1`, `component_support`, and `regions_disjoint` directly.
P5.3 additionally takes positive ε, `eps_time`, and raw packet blow-up.
P5.4 takes the existing I03 `PacketData` assembled from the raw clauses,
`placement`, `eps_admissible`, and `region_interior`; dissipation also takes
`placement_time` and `placement_chart`. The stronger `2 ε_j² < T` required by
I03 is derived from `DomainPlacementData.eps_time`, never added as a residual.
The probe gives the exact argument order. Pressure and force supports are not
needed by these velocity/energy proofs.

## 3. Gaps and errors

No remaining P5.3/P5.4 mathematical gap, admission, custom axiom, or named input.
P5.1/P5.2 constructors, P5.5 assembly, registration, and article-level closure
remain with their assigned lanes. Neither competing component nor assembled
module was created. The article coverage remains Partial pending that assembly.

The first static gate stopped with:
`AssertionError: Source changed: rerun the article axiom audit`.
The required audit was rerun and the fingerprint refreshed. Lean development
errors (section variable omission and an unreduced applied-integrand lambda)
are documented with their fixes in ATTEMPTS; the final Lean runs are clean.

## 4. Commands and results

All Lean commands used `. scripts/lean-env.sh`, ran from `verification/`, and
set `LEAN_NUM_THREADS=6`.

- `lake build NSFormalization.Section3.T24.MultipleOmega NSFormalization.Section3.T15.Energy`:
  success; existing dependency warnings only.
- `lake build NSFormalization.Section3.T24.MultipleOmegaRegions`: success,
  10132 jobs; new module clean.
- `lake env lean ../formalization/NSFormalization/Section3/T24/MultipleOmegaRegions.lean`:
  exit 0, zero output.
- `lake env lean ../research/T24/probes/p5b_closes.lean`: exit 0, zero output.
- `lake env lean ../research/T24/axioms_p5b.lean`: exit 0; all seventeen theorem
  axiom sets exactly `[propext, Classical.choice, Quot.sound]`.
- Probe axiom audit (same probe plus four `#print axioms` commands in `/tmp`):
  exit 0; all four have exactly the same three axioms.
- `python3 experiments/audit_article_axioms.py --build --output-dir /tmp/p5b-article-audit --workers 2`:
  success, 56 declarations / 27 article entries / 0 forbidden-axiom results.
- `python3 experiments/check_formalization_plan.py`: success; graph unchanged.
- `make check`: exit 0; blueprint/package checks pass, all 29 registered
  contracts pass architecture checks, and all 11 contract-policy tests pass.
