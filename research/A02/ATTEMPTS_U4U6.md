# A02 units U4 + U6 — attempts, decisions, dead ends

Lane 032, worktree `.claude/worktrees/032-A02-restrict-order`, 2026-09-13, base `4ba9f2b`.
Units per `research/A02/COMPARISON.md` §3: **U4** (`restrict` + congruence +
`pressure_normalization`) and **U6** (the six order-theoretic fields).
Both are rated **S** and touch nothing analytic; both came out `sorry`-free.

Deliverables:

* `formalization/NSFormalization/Section4/A02/Restrict.lean` (404 lines) — U4;
* `formalization/NSFormalization/Section4/A02/Order.lean` (163 lines) — U6;
* `research/A02/AxiomsU4U6.lean` — draft check file: `#print axioms` for all 25
  declarations plus a **conformance block** that discharges each spec field's
  *verbatim* type by the corresponding theorem.

---

## 1. The blocking decision: there is no local `ClassicalSolutionR`

`ClassicalSolutionR`, `maximalLifespanR`, `RegularThrough`,
`PressureGaugeEquivOn`, `initialClassR`, `MemForceR` exist **only** in
`verification/Contracts/V1/Data.lean`.  Checked exhaustively:

```
grep -rn "ClassicalSolutionR" --include="*.lean" formalization/ vendor/
```

hits only two docstring mentions in `Section4/D01/SmoothDatum.lean` (`:42`, `:384`).
There is no `Bindings/Data*.lean`; `verification/Bindings/` has eight modules,
none about D01's solution class.  So the objects had to be restated in this
lane, in `Restrict.lean` §0, exactly the way
`Section4/D01/SmoothDatum.lean:237,306` restates `Data.IsSobolevDatum` and
`Data.sobolevENorm` ("definitionally equal; a binding module can discharge one
by the other with `exact`").

**Positive:** every field type of the restated `ClassicalSolutionR` is
definitionally the contract's, so a future `Bindings/Data.lean` can carry a
solution across the two copies field by field
(`{velocity := w.velocity, pressure := w.pressure, horizon_pos := w.horizon_pos, …}`)
and then discharge every contract statement by `exact`.

**Negative / warning for the lead:** a `rfl` bridge `Contract.X = Local.X` is
*not* available for `ClassicalSolutionR`, because two separately declared
structures are different inductive types, never definitionally equal.  The
bridge has to be the two conversion functions above.  For the six `def`s
(`maximalLifespanR`, `RegularThrough`, `PressureGaugeEquivOn`, `initialClassR`,
`MemForceR`, `IsSobolevPath`) a `rfl` bridge *is* available only once the two
`ClassicalSolutionR`s are identified, which they are not — so those, too, need
transport rather than `rfl`.  **This is the one real cost of the "formalization
cannot import verification" rule at D01's solution class, and it is worth the
lead deciding whether `ClassicalSolutionR` should move into a canonical local
module (a new `Section4/D01/Solution.lean`) added to
`check_contracts.py`'s `CONTRACT_CANONICAL_MODULES`, so that `Data.lean` V2
imports it instead of re-declaring it.**  With that, all bridges become `rfl`.

**Collision warning:** lane 033 (A02 unit U1a) needs the same restatement.  If
both lanes restate it, the merge has two copies.  Suggested resolution at merge
time: keep this file's §0 and have U1a import `Section4.A02.Restrict`.

## 2. Why `IsSobolevDatum` is restated here rather than imported from D01

First draft imported `NSFormalization.Section4.D01.SmoothDatum` to reuse its
verbatim `IsSobolevDatum`.  Measured the import closure (script over the
`import` lines of the local sources):

* `Section4.D01.SmoothDatum` closure: **67** local modules;
* `Contracts/V1/Data.lean` closure: **35** local modules;
* extra: **33**, including `Source.PhysicalIntegerSobolev`,
  `Source.FourierTameProduct`, `Source.YoungConvolution`, `Source.BesselH2Fourier`,
  `Paper3.CompleteTameProduct`, `Paper3.SobolevPhysicalProduct`,
  `Paper3.AngularRealVectorBochner`, four `Paper1.*`.

None of that is used by U4 or U6 — `IsSobolevDatum` is never unfolded here, it
only appears as the type of the `sobolev` field.  Dragging 33 analytic modules
into the two cheapest units of A02 is the wrong dependency, so `Restrict.lean`
carries its own three-line copy and its import list is exactly
`Contracts/V1/Data.lean`'s (minus `Paper3.GridGeometry` and
`Source.FourierConvention`, which none of the restated objects needs).
The three copies (`Data`, `D01`, `A02`) are definitionally equal, so any one
discharges any other by `exact`.  Recorded as a deliberate duplication.

## 3. U4a `restrict` — no surprises

Transcribed from `Source/SmoothLifespan.lean:83` `Flow.restrict`.  `Flow`'s
`energy`/`velocity_bound`/`derivative_bound` have no analogue; the two extra
D01 fields restrict by `Ico`-monotonicity:

* `sobolev`: the datum path `G` is reused unchanged; `ContinuousOn G (Ico 0 T)`
  narrows by `ContinuousOn.mono (Ico_subset_Ico le_rfl hST)`.
* `pressure_gradient`: pointwise in `t`, so only the membership shrinks.

Negative detail: `Set.Ico_subset_Ico_right` **does not exist** for `Set` (only
for `Finset`, `Order/Interval/Finset/Basic.lean:176`).  Use
`Ico_subset_Ico le_rfl hST` (`Order/Interval/Set/Basic.lean:281`).

## 4. U4b congruence — the only unit with real content

Statement chosen after reading what `IsMaximalSolution` (`Spec.lean:210-214`)
actually needs: not "two solutions agreeing on the slab are equal" (which is
false — the structures carry no extensionality), but a **constructor**: from
`w : ClassicalSolutionR ν a f T` and fields `u, p` agreeing with `w`'s on
`Ico 0 T ×ˢ univ`, build a solution whose fields are *literally* `u` and `p`.
That is exactly the shape `∃ w, w.velocity = u ∧ w.pressure = p` of
`Spec.lean:214`.  `ClassicalSolutionR.congr` (`Restrict.lean:281`) is that
constructor; `exists_eq_fields_of_eqOn` / `exists_eq_fields_of_agree` are the
two spellings U7 will want.

Field-by-field, why the germ on the slab is enough — this is the argument that
had to be checked before writing anything:

| field | why slab agreement suffices |
|---|---|
| `velocity_smooth`, `pressure_smooth` | `ContDiffOn.congr` |
| `initial` | `(0,x)` is in the slab, `0 < T` |
| `divergence` | for `t ∈ Ico 0 T` the *whole* spatial slice agrees, so `fderiv ℝ (fun y => u (t,y)) x` is literally the same function's derivative |
| `momentum` | three of the four terms are spatial; the fourth, `temporalDerivative`, is a **two-sided** `fderiv` in `t`, and is only imposed on `Ioo 0 T`, which is *open* and contained in `Ico 0 T` — so `Ioo_mem_nhds` + `Filter.EventuallyEq.fderiv_eq` |
| `sobolev` | the datum clause is per-time and spatial |
| `pressure_gradient` | per-time and spatial |

So the helpers are split by what they need: `spatialDerivative_eq_of_eqOn`,
`pressureGradient_eq_of_eqOn` take `t ∈ Ico 0 T`, while
`temporalDerivative_eq_of_eqOn` and `navierStokesResidual_eq_of_eqOn` take
`t ∈ Ioo 0 T`.  **If D01 had imposed `momentum` on `Ico 0 T` instead of
`Ioo 0 T`, this lemma would be false as stated** (no neighbourhood at `t = 0`),
which is the same reason `Data.lean:632-636` gives for the `Ioo` convention.

Negative: `simp only [temporalDerivative, hev.fderiv_eq]` fails/ is fragile
because `Filter.EventuallyEq.fderiv_eq` leaves the field `𝕜` as a metavariable;
bind it first with an explicit
`have hfd : fderiv ℝ … = fderiv ℝ … := hev.fderiv_eq`.

## 5. U4c `pressure_normalization`

Three obligations, each its own lemma so a reviewer can check them separately:

* `pressureGradient_sub_basepoint` (`Restrict.lean:336`): `fderiv_sub_const`
  (`Mathlib/Analysis/Calculus/FDeriv/Add.lean:790`) is **unconditional** — no
  differentiability hypothesis — so the gradient identity holds pointwise with
  no side condition, and `momentum` and `pressure_gradient` transfer by
  rewriting.
* `contDiffOn_basepoint` (`:352`): `(t,x) ↦ (t,x₀)` is
  `contDiff_fst.prodMk contDiff_const`, and it maps the slab into itself, so
  `ContDiffOn.comp`; the statement is kept generic in the set `S` plus a
  `MapsTo` hypothesis, which is how it is reused for `Ico 0 T ×ˢ univ`.
* `normalizePressure_gauge_invariant` (`:393`): `q = p + c(t)` implies the two
  normalizations agree — three lines, and it is the fact that makes U7's
  pressure coherent across horizons without extending any gauge.

## 6. U6 — six fields, all order-theoretic

Transcription of `Source/SmoothLifespan.lean:44,48,58,101` with
`Flow → ClassicalSolutionR`.  `lifespan_le_iff`, `lifespan_le_iff_no_extension`
and `lifespan_ge_of_forall_shorter` are the source proofs verbatim (the source's
`bad_or_regular_reference` and its `push Not` step are **not** needed and were
not transcribed — `lifespan_le_iff_no_extension`'s proof uses `by_contra` only).

Two genuinely new ones, both resting on U4:

* `regularThrough_iff` (`Order.lean:135`).  Forward: `ofReal T < ofReal (T+δ)`
  then `horizon_le_lifespan`.  Backward is the half `bad_or_regular_reference`
  never had: enter the supremum from below.  Factored out as
  `exists_horizon_gt_of_lt_lifespan` (`:124`), which is
  `simp only [maximalLifespanR, lt_iSup_iff]` on the **double** `iSup` — one
  `simp only` handles both levels and also flattens `∃ _ : P, Q` to `P ∧ Q` —
  then `ENNReal.ofReal_lt_ofReal_iff_of_nonneg` and a `restrict` to `T+(S−T)/2`.
* `referenceLifespan` (`:152`).  One halving of the given margin serves all
  three conjuncts at once: `δ := δ₀/2` gives the solution on `[0,T+δ)` by
  `restrict`, the strictly longer realized horizon `S := T+δ₀` by the original
  witness, and the strict lifespan inequality by `ofReal (T+δ) < ofReal (T+δ₀)`.
  No second margin is needed, contrary to the "halves once more" phrasing of
  `research/A02/COMPARISON.md` §1.2 — that phrasing counts the halving of the
  `RegularThrough` margin, which is the same halving.

`horizon_le_lifespan` is split in two: the order fact
`horizon_le_lifespan` (`:48`, one line, `le_iSup_of_le` twice) and the spec
field `horizon_le_lifespan_of_localSolution` (`:56`), which takes
⟪A01:LocalTheoryAPI.solution⟫ (`Spec.lean:318-321`) as an explicit hypothesis
argument.  **A01 is not assumed anywhere**; instantiating that argument at A01's
`LocalTheoryAPI.solution` reproduces the field verbatim, and the conformance
block of `research/A02/AxiomsU4U6.lean` checks exactly that.

## 7. Build: run lake from `WT/verification`, never from `WT/formalization`

**Negative, cost a 682 MB re-clone.**  `CLAUDE.md` says
`cd WT/formalization && lake build NSFormalization.Foo.Bar`.  That treats
`formalization/` as its *own* Lake workspace, and `scripts/lean-install.sh`
only symlinks `verification/.lake/packages` to the main checkout — so the first
`lake` invocation there starts re-cloning Mathlib and ten other packages into
`formalization/.lake/packages` and then fails with `unknown module prefix
'Mathlib'` (nothing is built in the fresh clone).  Removed the directory; note
that `.lake` is gitignored, so nothing leaked into the commit.

**What works:** the same command from the *verification* workspace, which has
`formalization` as a path dependency and resolves dependency modules by source
path even though `formalization/lakefile.toml`'s `NSFormalization` library
declares no `globs`:

```sh
cd WT/verification && . ../scripts/lean-env.sh
LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A02.Order   # builds Restrict too
LEAN_NUM_THREADS=6 lake env lean ../research/A02/AxiomsU4U6.lean   # axioms + conformance
LEAN_NUM_THREADS=6 lake env lean ../research/A02/Spec.lean         # spec still elaborates
```

Incremental cost after a warm tree: **Restrict 3.5 s, Order 3.1 s**.  Both
modules build with **zero** warnings of their own (the warnings in the log all
come from pre-existing `Source/RealSobolev.lean` and `Paper3/*`).

One footnote: `lake env lean <file>` rejects a file outside the workspace root
only when `-o` is passed; the plain `../research/<ID>/X.lean` form of
`CLAUDE.md` is fine.

## 8. Not done here, and why

* **U1a/U1b/U2/U3/U5/U7/U8/U9/U10** are out of this lane's scope.  U7 is the
  direct consumer of everything above and is unblocked on the U4 side: it now
  has `restrict`, the congruence constructor and the canonical gauge, and needs
  only `velocity_unique` (U2) and `pressure_gauge` (U3) — i.e. U1a + U1b — plus
  ⟪A01:solution⟫.
* `patch` (U5) was **not** attempted: `COMPARISON.md` §1.2 makes it a
  consequence of `velocity_unique`/`pressure_gauge` (WLOG the longer horizon),
  so it is U2/U3-bound, not U4-bound.
* No attempt was made to relate the local class to `Source/SmoothLifespan.Flow`
  (implication **I5**): it needs `UniformFiniteEnergy` and the two sup bounds,
  i.e. U1a + U1b, and nothing in U4/U6 wants it.
