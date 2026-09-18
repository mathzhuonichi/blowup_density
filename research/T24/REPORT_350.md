# Lane 350 (SPEC, T24) — report

Task: produce the reconciled statement-only specification of T24 "Further
constructions" (`prop:affine`, `prop:multiple`, `prop:conservative`,
`paper/sections/03-torus.tex:667-740`) from the lead's reconciliation of the two
blind drafts (306/307).  Statement-only: no proofs.

## 1. What was stated

`research/T24/Spec.lean` — three structures, one per proposition, in three
namespaces, on top of the copied T10/T13/T14/T15 vocabulary and the registered
`Contracts.V1` contracts.

- `BlowupDensity.T24.Affine.AffineVariationAPI {ν} (P : PacketAPI ν) (c r τ₀ τ₁) : Prop`
  — **13 fields** — infinite-dimensional affine variations of the **whole-space**
  Theorem 1.1 packet inside a cylinder, terminal time `1`.  Concrete clauses:
  `radius_pos`, `window` (`0<τ₀<τ₁<1`), `force_smooth`, `force_support`
  (`CompactPositiveTimeSupport`), `divergence_free`, `momentum`
  (`navierStokesResidual ν (U+b) P = F̃`), `zero_initial`, `late_agreement`,
  `speed_unbounded` (`SpeedUnboundedAtOne`), `energy_finite` (`energyENorm 1 < ⊤`),
  `infinite_dimensional` (`LinearIndependent ℝ`), `distinct`, `nonisolated`
  (`ckSeminormE`, an `ℝ≥0∞` `⨆`, `Tendsto … (𝓝 0)`).  Helper defs
  `affineCylinder`, `AffineAdmissible`, `crossAdvection`, `affineVelocity`,
  `affinePressure`, `affineForce` (the six-term `eq:affine`), `ckSeminormE`.

- `BlowupDensity.T24.Multiple.MultipleRegionsAPI {ν} (P : PacketImportAPI ν) (T) {N} (regionCenter) (regionRadius) : Type`
  — **30 fields** — `N` prescribed disjoint interior balls on the torus, each
  blowing up at the common terminal `T`, energy `≤ M²Σε_j` and dissipation
  `= D²Σε_j` (`M,D = P.energyBound/dissipationBound`, no new constants).  Geometry
  (`ν,T,N`, balls) is parametric; `placement_chart` pins T15's chart ball to
  `B_j`; component/force supports are measured inside `fundamentalCube`.  Helper
  defs `finiteVelocitySum/PressureSum/ForceSum`, `SpeedUnboundedAtOn`.

- `BlowupDensity.T24.Conservative.ConservativeForcingAPI : Prop` — **2 fields** —
  `potential_pairing` (`∫_{T³} inner ℝ (-∇φ) u = 0` on `[0,T)`) and
  `zero_from_rest` (`∀ t ∈ Ico 0 T, ∀ x, S.velocity (t,x) = 0`).  Helper defs
  `PeriodicPotentialT`, `conservativeForceT`.

Three closing existence statements: `affineVariationStatement`,
`multipleRegionsStatement` (both quantify the prescribed geometry first),
`conservativeForcingStatement`.  Every field carries a docstring citing the paper
line, the exact quantifier order, and a non-vacuity note.  No field is `True`, a
tautology, or an argument-ignoring definition.

Every reconciliation ruling is followed: whole-space affine on `PacketAPI`;
geometry as parameters; the two false B clauses fixed (`zero_from_rest` on
`Ico 0 T`; supports on `fundamentalCube`); `ckSeminormE` as an `ℝ≥0∞` `⨆`; the
non-paper `−∇φ ∈ forceClassT` hypothesis dropped; dissipation `:719` an equality,
energy `:718` a `≤`; bounded-domain/no-slip clauses omitted with docstring notes.

## 2. What exists in Lean now

- `research/T24/Spec.lean` (1418 lines): the T24 spec.  It **elaborates** under
  `Contracts.V1.{TorusData,Packet,HomogeneousNorm,Scaling}` (transitively `Data`)
  with 0 errors and 0 warnings.  Lines 36-943 are the vocabulary block, byte-for-byte
  identical to `research/T15/Spec.lean:17-924` (verified by `diff`); it carries the
  copied T10 solution class, T13 localization, T14 packet-import and T15 scaling
  vocabulary in namespaces `T10.Draft`/`T13.Spec`/`T14.Draft`/`T15.Draft`, plus the
  seven `example … := rfl` drift checks (`CompletedDense`/`CompletedDenseHomogeneous`
  vs `CompletedDenseVia`, and the scaling defs vs `Contracts.V1.scaledPacket`/
  `scaledPressure`/`scaledForce`/`alpha`), all of which pass.
- Provenance (verbatim from the draft branches): `DraftA.lean`, `DraftB.lean`,
  `COMPARISON_A.md`, `COMPARISON_B.md`, `REPORT_306.md`, `REPORT_307.md`.
- `research/T24/COMPARISON.md`: merged clause→field table with A/B provenance and
  rulings, "Proof dependencies" (copied from the reconciliation §4), and
  "Open questions for the owner".
- `research/T24/ATTEMPTS.md`: copy header, ambient-space ruling, the two
  corrected falsities, the seminorm choice.  `logs/LESSONS.md`: one prepended
  line for the two statement-fidelity traps.

Nothing is registered as a contract by this lane; these are the reconciled
statements for a later registration/binding lane.

## 3. Gap

- **Statement-only.**  No inhabitant of any structure is constructed; the ten
  proof obligations (`COMPARISON.md` "Proof dependencies") are open.  T24c is
  closest — `Paper1/ConservativeForce.lean:91 zero_of_negative_gradient_on_Ico`
  matches `zero_from_rest`'s hypotheses and corrected conclusion, needing two
  `rfl` bridges.
- **Bounded-domain / no-slip branches** of `prop:multiple` and `prop:conservative`
  are omitted (no bounded-domain carrier / no-slip class exists in the tree),
  recorded as docstring notes — owner question 2 in `COMPARISON.md`.
- **Whole-space vs torus/scaled affine**: `prop:affine` is stated on whole space
  per the reconciliation; whether a torus/scaled counterpart is wanted is owner
  question 1 (it would be a new statement).

## 4. Commands and results

- `cd verification && LEAN_NUM_THREADS=6 lake build Contracts.V1.TorusData Contracts.V1.Packet Contracts.V1.Scaling Contracts.V1.HomogeneousNorm Contracts.V1.Data`
  → `Build completed successfully (8822 jobs)`, exit 0 (deps were unbuilt in this worktree).
- `cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/T24/Spec.lean`
  → exit 0, no output (0 errors, 0 warnings).  Re-run after docstring edits: exit 0, no output.
- `grep -nE ': *True|:= *0$|→ *True' research/T24/Spec.lean` → no matches (grep exit 1).
- `grep -nE '\bsorry\b|\badmit\b|\baxiom\b|native_decide' research/T24/Spec.lean` → none.
- `diff <(sed -n '17,924p' research/T15/Spec.lean) <(sed -n '36,943p' research/T24/Spec.lean)`
  → identical (vocabulary block verbatim).
- Field counts (by field-line grep): AffineVariationAPI 13, MultipleRegionsAPI 30,
  ConservativeForcingAPI 2.

### Failed approaches / dead ends

None material.  The only design fork was where to source the copied vocabulary:
draft B's own copy (`DraftB.lean:1-953`) carries four extra decls
(`initialClassT`, `maximalLifespanT`, `breakdownSetInT/T`) not on the
reconciliation's copy list and renames the T15 namespace; the authoritative
`research/T15/Spec.lean:17-924` has exactly the reconciliation's copy list and no
extras, so it was used as the verbatim block (only `import Contracts.V1.Packet`
and the header docstring were added).  No Lean error arose during construction.
