# Lane 476 report — T23 U1 domain placement

## 1. Statements

`NSFormalization.Section3.T23.Placement` now contains the canonical raw-field
`DomainPlacementData u p f K` with all 16 fields from
`research/T23/Spec.lean:374-450` and no torus/fundamental-cube condition.

The construction uses

```text
Kstar = K ∪ Prod.snd '' tsupport f
R      = a positive norm bound for Kstar
margin = chartRadius - dist x₀ chartCenter
ε₀     = min (min (1/2) (T/4)) (margin / (2 * (R+1)))
```

and proves compactness, carrier and force-projection containment,
`0 < ε₀ ≤ 1`, `2ε² < T`, and
`x₀ + ε • Kstar ⊆ ball chartCenter chartRadius` on `Ioc 0 ε₀`.
`domainPlacementData` accepts any compact carrier, compactly supported force,
positive horizon, prescribed positive-radius ball with closed-ball containment
in `Ω`, and any `x₀` in that ball.  Its `T`, `chartCenter`, `chartRadius`, and
`x₀` projections are definitionally the prescribed inputs.  The theorem
`interiorBall_in_domain` has the API geometry form

```text
closure (Metric.ball place.chartCenter place.chartRadius) ⊆ Ω
```

for the canonical `place`.

## 2. Files

- `formalization/NSFormalization/Section3/T23/Placement.lean`: record,
  compact-enlargement/radius/margin/threshold lemmas, constructor, definitional
  projection theorems, and `interiorBall_in_domain`.
- `research/T23/probes/placement_closes.lean`: translated center `(5,5,5)`,
  radius-`1` prescribed ball inside the radius-`2` domain ball, proof that the
  origin is outside the domain, a nonempty compact raw carrier, and an `exact`
  consumer for each of the 16 fields plus the API geometry theorem.
- `research/T23/axioms_u1.lean`: all 20 production declarations print exactly
  `[propext, Classical.choice, Quot.sound]`.
- `research/T23/ATTEMPTS_U1.md`: verbatim errors and resolutions for all failed
  proof/check attempts.
- `research/T23/T23_SPLIT.md`: U1 marked complete.

## 3. Gaps and failed approaches

There is no open U1 proof gap.  Five resolved development failures are recorded
verbatim in `ATTEMPTS_U1.md`:

1. an unnecessary `dist_comm` caused `hx₀` to be expected at the reversed
   ball center;
2. `linarith failed to find a contradiction` when strict multiplication by
   `ε > 0` had not been supplied explicitly;
3. `failed to synthesize ... MulRightStrictMono ℝ` from the wrong
   multiplication lemma for this pin;
4. the probe initially lacked the new `.olean`;
5. the probe then used the wrong `isCompact_closedBall` namespace and omitted
   the safe T13 coordinate-helper import.

The repository-wide `make check` still reports the known sorry token in the
copied umbrella closure at `Paper1/BoundaryCorollary.lean:90`; the new module
does not import that module or either transitive unsafe helper.  The targeted
source scan found no `sorry`, `admit`, `axiom` declaration, or `native_decide`
in the delivered Lean files.

## 4. Commands and results

Run from `verification/` after `. ../scripts/lean-env.sh` unless noted:

- `LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T23.Placement` —
  success, 0 errors (only pre-existing replayed dependency warnings).
- `lake env lean ../formalization/NSFormalization/Section3/T23/Placement.lean`
  — success, 0 output.
- `lake env lean ../research/T23/probes/placement_closes.lean` — success,
  0 output.
- `lake env lean ../research/T23/axioms_u1.lean` — success; every printed line
  is exactly `[propext, Classical.choice, Quot.sound]`.
- targeted forbidden-token and unsafe-import `rg` scans — no output.
- from the repository root, `make check` — success (exit 0); 13 contract-policy
  tests passed and the 45-item work queue was consistent.

## Lead amendment after review (2026-09-19 16:34Z)
- Reviewer note 2 (disclosure): `make check` prints `source_hashes_match: false` (exit 0) — a pre-existing snapshot diagnostic recorded in every Section 3 build report since `logs/SECTION3_BUILD_20260918f.md`; the repository-wide forbidden-token count reported by the reviewer is documentation text only (see `logs/SECTION3_BUILD_20260919g.md` §3).
- Reviewer note 1 (three auxiliary geometry lemmas: closed-ball compactness, a smaller closed ball around `x₀`, frontier separation under `IsOpen Ω`) is folded into lane 480 (T23 U-CAN) — `collaboration/briefs/480-T23-UCAN-canonical-records.md`.
