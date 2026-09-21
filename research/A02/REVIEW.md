# A02 review — lane 016, task A02 ("Uniqueness and maximal solution identification")

Reviewer pass on `research/A02/Spec.lean` + `research/A02/COMPARISON.md`, worktree
`.claude/worktrees/016-A02-spec`, HEAD `6ed65fb`.  Neither reviewed file was modified.

## Verdict: **ACCEPT-WITH-NOTES**

The Lean typechecks clean and is hygienic; every `file:line` I re-opened resolves; fidelity
is high and the reuse table is accurate (the `residual`/`navierStokesResidual` `rfl` claim is
verified below, not asserted).  Two substantive gaps (H1, H2) and a sizing overstatement (M3)
keep it off a clean ACCEPT.  No field is *stronger* than the manuscript; one is narrower (H2)
and one is redundantly decorated (`insertion_lifespan_eq`, harmless).

## Ranked issues

**H1 — `exists_maximal` has an unstated pressure-gauge obligation.**
`IsMaximalSolution` (Spec.lean:186-190) demands **one** `p` such that for *every* `S <
T_max` some `w` has `w.pressure = p`.  Uniqueness gives velocities outright but pressures
only up to `PressureGaugeEquivOn` (`Data.lean:589-590`, `∃ c : ℝ → ℝ, q = p + c t`), so
"define `p` from any solution with horizon `> t`" is **not well defined**.  `COMPARISON.md`
§1.3 U7 offers only "directed union … with coherence from `velocity_unique`" — that covers
`u`, not `p`.  A construction is needed: exhaust by `S_n ↑ T_max` and subtract the gauge
`c(t) = q(t,x₀) − p_n(t,x₀)` at each step, smooth because both pressures are
(`Data.lean:634`), so `pressure_smooth` survives and `momentum` is gauge-blind.  Easy, but
it is a step missing from U4/U7 and from the docstring.

**H2 — "Hypotheses are exactly the manuscript's … Nothing else is assumed" is not right.**
Spec.lean:203-212.  `prop:local` quantifies over "each force smooth into every `H^m` on
compact time intervals" (`02-preliminaries.tex:107-108`); `MemForceR` (`Data.lean:544-550`)
additionally demands `MemLp G 1` and `MemLp G 2` over `forceTimeMeasure` at every order.  So
`UniquenessAPI` is stated on a strictly **narrower** force class than the proposition — the
deviation A01 records explicitly at `research/A01/Spec.lean:301-309`.  Benign for Section 4
(`F_c ⊆ F_rd ⊆ F_R`), but the claim as written is false; use A01's wording.

**M3 — the split understates U1; "6 S / 4 M / 0 L" is not credible.**
U1 must produce a uniform bound on `‖spatialDerivative u t x‖` (`hG`), but `sobolev`
(`Data.lean:643-645`) gives datum paths for `u`, not `∇u`.  So U1 also needs (i) an
order-shift `‖∇v‖_{H²} ≤ ‖v‖_{H³}` on D01's angular datum carrier and (ii) identification of
the *physical* `spatialDerivative` with that datum's derivative — neither is in U1's
dependency column.  Further, A03's delivery of `‖v‖_∞ ≤ C‖v‖_{H²}` **on the D01 carrier** is
A01 unit **A1** (`research/A01/COMPARISON.md:197`), which depends on **C1b**, rated **L**
there.  U1 is realistically **L**, or should split (U1a energy / U1b sup bounds); the
critical path inherits an L either way.

**M4 — the acyclicity chain is mis-ordered and "no A01 dependency" is inexact.**
`COMPARISON.md` §3 writes `U1 → U2 → A2b → A1/A3 → U7/U8`.  A1 is a *dependency* of A2, which
is a dependency of A2b (`A01/COMPARISON.md:197-199`), so A1 **precedes** A2b; and "U1–U3
depend only on D01 and A03 — not on A01" is inexact, since A1 ← C1b is an A01 unit.  The
conclusion survives: `C1a → C1b → A1 → U1 → U2 → A2b → A3 → X1 → U7/U8` is acyclic.

**M5 — `horizon_le_lifespan` (U6) also consumes ⟪A01:solution⟫**; §3 names only U7/U8.

**L6 — `referenceLifespan` gives the half-open horizon R42 does not literally ask for.**
It yields `Nonempty (ClassicalSolutionR ν a g (T+δ))` = `[0,T+δ)`; R42's `reference`
(`STATEMENTS.md:332`) and O2's recommendation (`:391-392`) are on the closed `Icc 0 (T+δ)`.
Recoverable — strict `ofReal (T+δ) < maximalLifespanR` plus the `iSup` shape yields some
`S > T+δ` carrying a solution — but no field names that step.  Consistent with D01's own
convention note (`Data.lean:660-663`), so documentation only.

**L7 — citation drift (all minor).**  `02-preliminaries.tex:105-107` for the quantifier
sentence: the text is at `:107-109`.  `R3MildContinuation.lean:30-33`: line 30 is blank and
the sentence ends at `:34`, so `:31-34`.  `COMPARISON.md` §1.1 cites
`OrdinaryViscousUniqueness.lean:53-64` as "(`gradient_mem … gradientSpace`)" — those are
`have` steps; the declarations live at `vendor/…/Euler/OrdinaryPressureCancellation.lean:84`
and `Euler/MeanSolenoidalSpace.lean:50` (the claim about them is correct).  The carrier
column calls `VelocityField` "D01's"; it is upstream, aliased by `Data.lean:104`.

**L8 — naming.**  `speedENorm` realizes `⟪D01:normLinfty⟫` under another name;
`breakdownSetIn` vs `STATEMENTS.md:1204`'s `breakdownSetR` — the Spec is right (`Data.lean:672`).

## Fidelity spot-results (no defects beyond the above)

`velocity_unique`/`pressure_gauge`: hypotheses `0 < ν`, `a ∈ initialClassR`, `MemForceR f`
(H2 aside); `Ico 0 (min T₁ T₂)` is exactly the intersection of the two intervals of
definition, nonempty by `horizon_pos` (`Data.lean:630`); `Ico` rather than `Ioo` is right
because `momentum` is imposed on `Ioo` only (`Data.lean:640`).  `IsMaximalSolution` arity
`ν a f u p` matches `STATEMENTS.md:1198`, `:174`, `:346`.  The literal-field-equality notion
is the right one for R42 (which talks about `u_ε` outside `[0,S)`) and **does** need a
`ClassicalSolutionR` congruence lemma; the lemma is true — `ContDiffOn` on `Ico 0 S ×ˢ univ`
reads only the germ within the set, and `momentum` at `t ∈ Ioo 0 S` sees a full spacetime
neighbourhood inside the slab — and the draft books it in U4 (risk 4).  `lifespan_le_iff`
matches `breakdownSetIn` membership exactly and genuinely needs `0 ≤ T`.  `referenceLifespan`
matches `STATEMENTS.md:333` modulo L6.  `restart` reproduces A01's quantifier order verbatim.
`insertion_lifespan_eq`'s blow-up is verbatim R42's `blowup` (`STATEMENTS.md:348-351`) modulo
currying; `2ε² < T` is the retained half of `:419`.  The three restated A01 fields are
byte-equivalent to `research/A01/Spec.lean:283,297,338` (renamed `solution → localSolution`,
`horizon_lower_bound → horizonLowerBound`).  Props 4.3/4.4 (`04-whole-space.tex:132,171`) use
the *continuation criterion*, correctly left to A04; Thm 4.7 (`:303,320`) needs `T_max = T`
and the constant pressure gauge, both supplied.

## Reuse table (all citations re-opened)

| cited | verdict |
|---|---|
| `Source/BoundedViscosityUniqueness.lean:23` `classical_uniqueness_on_Icc` | **accurate.** Whole space; only `0 < ν` (no smallness); carrier upstream `VelocityField` = `Data.lean` `SpaceTimeField`; `UniformFiniteEnergy (Icc 0 T)` for **both**, `hB0/hB` and `hG0/hG` for **one**; `hNS` as equal residuals on `Ioo 0 T`.  All as described |
| `Source/Insertion.lean:21` `residual` ≡ `navierStokesResidual` | **verified by `rfl`** in a `/tmp` scratch (deleted).  `ClassicalSolutionR.momentum` uses `NavierStokesR3.ProblemStatement.navierStokesResidual ν …` (`Data.lean:641`), so `hNS` closes by `rfl`.  Caveat worth carrying: `Insertion.lean:26` `residual_one` is against the *two-argument* `NavierStokes.ProblemStatement.navierStokesResidual`, a different declaration |
| `Source/OrdinaryViscousUniqueness.lean:26` | **accurate**, incl. `0 ≤ T`, `0 ≤ ν` (non-strict), `Icc 0 T → SmoothL2Field Space` carrier, separate `D₁ D₂`, shared force `F`.  The `:53-64` sub-citation is a `have`, see L7 |
| `Source/SmoothLifespan.lean:23,41,44,48,58,70,83,101,124` | **all correct declarations.**  `lifespan` (`:41`) is the same `⨆ S, ⨆ _ : Nonempty …, ofReal S` term as `maximalLifespanR` (`Data.lean:657`) modulo `abbrev` unfolding and parens — the draft's "syntactically" is fair.  `Flow` (`:23`) has 11 fields incl. `energy`/`velocity_bound`/`derivative_bound` and lacks `sobolev`/`pressure_gradient`, exactly as claimed |
| `Source/InsertionBreakdown.lean:16,58,68` (+ `:51` as a use site) | **accurate, no overclaim.**  `:68` `insertion_lifespan_eq` concludes about the **`Flow`** `lifespan`, and §1.3/I5 says so explicitly rather than pretending it transports |
| `Source/LocalizedBlowup.lean:36` `no_continuous_continuation` | **accurate**, incl. the compact-`K` `LocalSpeedUnboundedAt` hypothesis that risk note 2 turns on |
| `FormalPatched/EndpointSafeTwoSpaceUniqueness.lean:231` | **accurate.**  Unrestricted, mild, **unforced** (no `+∫e^{(t−s)A}f`).  Sharper than the draft says: `R3HsVelocity 3` is `abbrev R3HsVelocity (_s : ℝ) := R3L2Velocity`, i.e. the order argument is *discarded* — complex `L²`, order carried only by the decoder |
| `FormalPatched/R3MildContinuation.lean:30-33,67,93,143` | **content accurate**, `:30-33` should be `:31-34` (L7).  `:143` is `r3EndpointSafeProjected_blowup_dichotomy`, a disjunction over certified horizons, not a maximal-trajectory statement — which supports the draft's "not on A02's critical path" |

## DAG ruling

**The draft is right on the mathematics and overstated on the polemics.**

1. **`A03 → A02` is required, and required independently of R42.**
   `appendix-a-local-theory.tex:120` displays the Grönwall coefficient `‖∇u₂‖_∞`; `:122-123`
   justifies its finiteness *only* by "since `u₂ ∈ C_tH³`", i.e. by `‖v‖_∞ ≤ C‖v‖_{H²}` at
   `:12` (eq:Rproduct, second clause) applied to `∇u₂`.  Nothing in `ClassicalSolutionR`
   (`Data.lean:624-648`) supplies a sup bound — unlike `Flow`, which has
   `velocity_bound`/`derivative_bound` as *fields* — and the in-tree route takes `hB`/`hG` as
   hypotheses (`BoundedViscosityUniqueness.lean:23`).  Every route to `velocity_unique` on
   the D01 carrier passes through A03, whatever shape the blow-up hypothesis takes.
   **Add `A03 → A02`.**
2. **No cycle.**  A03's ancestor closure is `{D01, U04, A05, U03}` (`DEPENDENCY_GRAPH.md:
   46-48`, `:160`, `:197`, `:216`); A02 is in none of it.  Confirmed.
3. **The ledger is not wrong, and the draft should not say it is.**  `STATEMENTS.md:405-411`
   and `section4/REVIEW.md:181-184` never claim A02 does *not* need A03; they say the
   alternative route to **R42's** step "additionally requires `A03 → A02` … so the direct
   edge is cleaner" — a minimality preference about one edge, not a rejection.
   Spec.lean:66-73 ("the correct conclusion is the opposite one") mischaracterises it.
4. **`A03 → R42` becomes optional once (1) lands.**  With `A03 → A02` and `A02 → R42`
   (`DEPENDENCY_GRAPH.md:58`) A03 is a transitive ancestor of R42, and A02's
   `insertion_lifespan_eq` takes the blow-up in R42's own `L^∞` shape
   (`STATEMENTS.md:348-351`), so R42 needs no `H²→L^∞` step of its own.  Recommendation: add
   `A03 → A02` (necessary); **keep** `A03 → R42` too, since `04-whole-space.tex:53` names
   eq:Rproduct inside R42's own proof text and the redundant edge costs nothing.
5. **Ownership nit.**  `tasks.json` gives A03 `manuscript_labels: ["lem:calculus"]` (both
   clauses), but A03's contract text now says "The embedding clauses of shared Lemma A.1 are
   supplied by **A05**" (`DEPENDENCY_GRAPH.md:220`).  The tightest edge is arguably
   `A05 → A02`; naming A03 stays correct since `A03 ← A05` and A03 exports Lemma A.1.
6. **A01 ⇄ A02 latent task-level cycle** (the draft's own §3, and correct): A01 unit A2b
   consumes A02's uniqueness (`A01/COMPARISON.md:199`) while the DAG has `A01 → A02`.
   Resolvable only at unit granularity; see M4 for the corrected ordering.

## Check log

* `cd verification && lake env lean ../research/A02/Spec.lean` → **exit 0**, no output,
  2.82s wall (`. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, no `-j`).
* Hygiene: `grep -nE '\b(sorry|axiom|admit|native_decide|unsafe)\b'` → 2 hits, both in the
  module prose (lines 11-12) saying the file contains none.  Declarations: 5 `def`
  (`limsupLeft:123`, `speedENorm:136`, `timeShift:145`, `presingularTimes:156`,
  `IsMaximalSolution:186`) and 2 `structure` (`UniquenessAPI:229`, `MaximalSolutionAPI:278`);
  **no** `theorem`/`lemma`/`example`/`instance`/`opaque`, no abstract `Prop` variable.  D01
  defines none of the five (`Data.lean` has no `limsup`, `timeShift`, `normLinfty`,
  `IsMaximalSolution`).
* `rfl` scratch (created and deleted under `/tmp/a02rev`): `example … : residual ν u p t x =
  NavierStokesR3.ProblemStatement.navierStokesResidual ν u p t x := rfl` → **exit 0**; a
  control `example : (2:Nat) = 3 := rfl` in the same setup fails, so the file really
  elaborated, and `#check ClassicalSolutionR.momentum` prints the R3 residual on `Ioo 0 T`.
* Paper read: `02-preliminaries.tex:28-48,105-120`; `appendix-a-local-theory.tex:1-19,
  100-160`; `04-whole-space.tex:25-60,132,171,177,295-321`.  Ledger read:
  `STATEMENTS.md:172-176,199-204,306-352,386-424,1110-1130,1315-1355` (version 2, per `:1`
  and `CHANGELOG.md`); `section4/REVIEW.md:30-70,181-184`; `A01/COMPARISON.md:160-211`;
  `A01/Spec.lean:275-380`; `DEPENDENCY_GRAPH.md:14-97,158-230,275-279`; `tasks.json`
  (A02/A03/A04/A05/U03/U04/R42).
* No git write commands; nothing outside `research/A02/REVIEW.md` created or modified.
