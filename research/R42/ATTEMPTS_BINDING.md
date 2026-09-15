# R42 lane 092 — Bindings-level assembly of the two lifespan clauses

Deliverable: `verification/Bindings/InsertionLifespan.lean`, namespace
`BlowupDensity.Bindings.InsertionLifespan`.  Inhabits the still-**unregistered**
`Contracts.V1.InsertionFamily.InsertionLifespanAPI`
(`Contracts/V1/InsertionFamily.lean:421-436`).  No contract registration in this
lane (next lane).  Build/silent/axioms/`make check`/`make test` all green (command
table at the end).

## The V2 contract's exact hypothesis list (the point of this lane)

**FINAL (after lane-092 review):** `insertionLifespan` — hence a correct-strength
R42-V2 — takes **exactly two** extra hypotheses beyond `F : InsertionFamilyAPI ν P`,
and no more:

| hyp | type | why `InsertionFamilyAPI` cannot supply it | enters |
|---|---|---|---|
| `hg`   | `Data.MemForceR F.g` | reference force `∈ F_R` (`04-whole-space.tex:32`); `Data.ClassicalSolutionR` has no force-class field, and `g_ε − g ∈ C_c^∞` alone cannot give it (`DatumLemmas.lean:378-381` note) | `lifespan_upper` |
| `hreg` | `Data.RegularThrough ν F.a F.g (F.T + F.margin)` | the reference is *the* solution, regular through `T+δ` (`04-whole-space.tex:32`); `InsertionFamilyAPI.reference` is only a solution on the half-open `[0,T+δ)`, giving `≤` not the strict `<` | `referenceLifespan` |

**Not** hypotheses (derived from the ambient contracts):
- `0 < ν`  = `P.viscosity_pos` (`Packet.lean:199`); `P` is a parameter of every
  structure here.
- `F.a ∈ Data.initialClassR` (`X_R`) = `initialClassR_a F`, 12 lines from
  `F.reference` at `t = 0` (`D01.contDiff_slice` on `velocity_smooth`;
  `reference.sobolev`; `reference.divergence`), all in the import closure.
- `0 < F.T`  = `F.scaling.correction.time_pos` (`Correction.lean:202`);
- `0 < F.margin` = `F.scaling.correction.margin_pos` (`Correction.lean:207`);
- the essSup blow-up `limsupLeft T (speedENorm ∘ slices) = ⊤` — derived from
  `F.blowup` + `F.velocity_smooth`, not assumed.

### NEGATIVE EXAMPLES — two hypotheses the first draft carried but should not have

The initial (pre-review) draft listed **four** hypotheses.  Two were wrong and
were removed (lane-092 review findings 1, 2, verified in
`/tmp/r42rev092/Scratch.lean`):

- ~~`hν : 0 < ν` — "structural; not a field".~~  **FALSE.**  `0 < ν` is the field
  `viscosity_pos` of `PacketAPI ν` (`Packet.lean:199`), and `P : PacketAPI ν` is a
  parameter of `InsertionFamilyAPI`/`InsertionLifespanAPI`, hence in scope
  everywhere.  Corrected: `hν` replaced by `P.viscosity_pos` at all use sites.
- ~~`ha : F.a ∈ Data.initialClassR` — "derivable in principle … but a separate
  M-item, not this bounded lane".~~  **FALSE — it is an S-item.**  It is 12 lines
  from `F.reference` at `t = 0`, and the only lemma it needs
  (`D01.contDiff_slice`) is already in this module's import closure via
  `Bindings.DatumLemmas`.  Corrected: added as the public lemma `initialClassR_a`
  and dropped from the three signatures.  `LIFESPAN_SPLIT.md` 4a's "S/M" should
  read S.

Lesson: before recording "not a field", check the *parameter* structures
(`PacketAPI` here), not only `InsertionFamilyAPI`'s own fields; and before
recording "M-item", try the `reference`-at-`t=0` route with the in-closure slice
lemma.

## Route (what was reused, clause by clause)

- **#1 `sol_on_shorter`** — reused the lane-087 reviewer's verified 22-line
  instantiation *verbatim* (`research/R42/REVIEW_SOL_SHORTER.md`, and the
  reviewer's still-present scratch `/tmp/r42rev/Consume.lean`, exit 0).  Feeds
  `NSFormalization.Section4.R42.classicalSolutionR_of_inserted`
  (`SolutionOnShorter.lean:74`) with:
  - reference via `uniqueness_toA02 F.reference` (the `Data → A02` conversion;
    the `A02 → Data` back-conversion `maximalPartial_ofA02` returns the witness);
  - `t₁ := F.scaling.correction.T − 2ε² > 0` from
    `F.scaling.eps_time ε hεS` + `min_le_left` + `linarith`;
  - `hδ := F.scaling.correction.margin_pos`;
  - `history`/`velocityDifference_support`/`pressureDifference_support` rewritten
    from `F.reference.velocity`/`.pressure` to `F.scaling.correction.v`/`.π` by
    `F.reference_velocity` / `F.reference_pressure`.
- **#3 `memForceR_force`** — `datumLemmas.memForceR_of_compact_difference F.g
  (F.force ε) hg (F.forceDifference_compact ε hε)`.  `F.g` unfolds to
  `F.scaling.correction.g`, so the compact-difference field's type matches by
  defeq.
- **#5 `lifespan_lower`** — `maximalPartial.lifespan_ge_of_forall_shorter ν F.a
  (F.force ε) F.T F.scaling.correction.time_pos (fun b hb0 hbT =>
  ⟨(sol_on_shorter …).choose⟩)`.
- **#4 `lifespan_upper`** — `maximalPartial.lifespan_le_of_unbounded` fed `hν`,
  `ha`, `hgε := memForceR_force …`, `time_pos`, `sol_on_shorter`, and `hblow`.
  `hblow` produced by `NSFormalization.Section4.R42.limsupLeft_speedENorm_eq_top
  (F.blowup ε hε) (continuous_slice_of_velocity_smooth (F.velocity_smooth ε hε))`.
- **`lifespan_eq`** — `le_antisymm (lifespan_upper …) (lifespan_lower …)`.
- **#6 `referenceLifespan`** — `(maximalPartial.regularThrough_iff ν F.a F.g
  (F.T + F.margin) (add_pos time_pos margin_pos)).mp hreg`.

## Bridges / mismatches, and how each was crossed (no failures, all by design)

1. **`Data.ClassicalSolutionR` vs `A02.ClassicalSolutionR`** — two separately
   declared structures, no `rfl` bridge possible.  Crossed by the *existing*
   field-by-field conversions in `Bindings/MaximalPartial.lean`:
   `uniqueness_toA02` (`Data → A02`, from `Bindings/Uniqueness.lean`) and
   `maximalPartial_ofA02` (`A02 → Data`).  Both directions already exist — no new
   conversion had to be written here.
2. **`(uniqueness_toA02 F.reference).velocity` vs `F.reference.velocity`** — defeq
   (structure-literal projection), so the `show F.velocity ε (t,x) =
   F.reference.velocity (t,x)` step in each of the three support/history lambdas
   type-checks, after which `rw [F.reference_velocity]` fires (the pattern is now
   syntactically present).  A bare `rw [F.reference_velocity]` on the un-`show`n
   goal would NOT fire — the goal there mentions `(uniqueness_toA02 …).velocity`,
   not `F.reference.velocity` — which is why the `show` is load-bearing.  (Copied
   from the verified reviewer template; noted here so a later simplifier does not
   delete the `show`.)
3. **`MaximalPartial.limsupLeft`/`speedENorm` (contract) vs
   `A02.limsupLeft`/`speedENorm` (what `limsupLeft_speedENorm_eq_top` produces)** —
   `rfl`-bridged in `Bindings/MaximalPartial.lean:57,61`, so the produced `A02`
   term is accepted by defeq where the `have hblow : MaximalPartial.… = ⊤`
   annotation and, in turn, `lifespan_le_of_unbounded`'s hypothesis expect the
   contract shape.  No `rw`/coercion needed.
4. **`Contracts.V1.SpeedUnboundedAt` (from `F.blowup`) vs
   `PacketScaling.SpeedUnboundedAt` (arg of `limsupLeft_speedENorm_eq_top`)** —
   `rfl`-bridged in `Bindings/Scaling.lean:50`, so `F.blowup ε hε` passes by defeq.
5. **`Data.RegularThrough` vs `A02.RegularThrough`** — a bridge
   (`maximalPartial_regularThrough_iff`) exists in `Bindings/MaximalPartial.lean`,
   and lane 072's `lt_maximalLifespanR_of_regularThrough` is stated in `A02` terms.
   **Chosen route:** the registered contract field
   `maximalPartial.regularThrough_iff`, which is already in `Data` vocabulary
   (`MaximalPartial.lean` opens `Data`).  This keeps `referenceLifespan` entirely
   in `Data`-land and needs **no** `RegularThrough`/`maximalLifespanR` bridge and
   **no** `A02` import — strictly less machinery than going through the R42 lemma.
   `lt_maximalLifespanR_of_regularThrough` was therefore not used (it would have
   required composing the two Bindings bridges to re-express its `A02` conclusion).

## Failed approaches / iterations

1. First draft: one unused-variable linter warning
   (`Variable name ε is not explicitly referenced` at the `lifespan := fun ε hε => …`
   field binder), fixed by renaming the binder to `_ε` (the `ε` is used only
   implicitly, inferred from `hε`).
2. **Lane-092 review round (ACCEPT-WITH-NOTES):** the two negative examples above —
   `hν` and `ha` were carried as hypotheses when both are derivable from the ambient
   contracts.  Removed from `lifespan_upper`/`lifespan_eq`/`insertionLifespan`;
   `hν → P.viscosity_pos`, `ha → initialClassR_a F` (new public lemma, reviewer's
   12-line derivation).  Also: deleted the dead
   `import NSFormalization.Section4.R42.Lifespan` (nothing from lane 072 is used —
   `memForceR_force` and `referenceLifespan` go through the registered `Data`-vocabulary
   fields), and added the regression guard
   `insertionLifespan_family : (insertionLifespan F hg hreg).family = F := rfl`.

## Commands run

Initial round (worktree, after `. scripts/lean-env.sh`, `export LEAN_NUM_THREADS=6`;
lake from `verification/`): build 9969 jobs, silent, 7 decls standard-3-axioms,
`make check`/`make test` green.

Post-review round (same setup):

| command | result |
|---|---|
| `cd verification && lake build Bindings.InsertionLifespan` | `Build completed successfully (9968 jobs).` (one fewer — dropped `Lifespan.lean`); only pre-existing upstream `Source/`,`Paper3/` linter warnings — none from `InsertionLifespan.lean` |
| `lake env lean Bindings/InsertionLifespan.lean` (from `verification/`) | **silent**, exit 0 |
| `lake env lean ../research/R42/axioms_binding.lean` | 9 declarations (`sol_on_shorter`, `memForceR_force`, `initialClassR_a`, `lifespan_lower`, `lifespan_upper`, `lifespan_eq`, `referenceLifespan`, `insertionLifespan`, `insertionLifespan_family`), each `[propext, Classical.choice, Quot.sound]` |
| `make check` | architecture checks pass; `test_contract_policy.py` 13/13 OK; `check_work_queue.py` "30 work items … consistent." |
| `make test` | SUCCESS; all registered contracts replayed, each "checked; standard logical axioms only" |
