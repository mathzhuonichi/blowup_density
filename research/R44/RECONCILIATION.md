# R44 — reconciliation decisions (Proposition 4.4, `prop:Rcritical2`)

Plain language: what was decided, why, what a wrong implementation could get
away with, and what upstream still owes us.

Deliverable: `research/R44/Spec.lean`,
`BlowupDensity.R44.Draft.RCritical2API` — **nine fields, no local `def`**.
Field-by-field and gap tables: `research/R44/COMPARISON.md`.

Inputs: `DraftA.lean` (9 fields, `radius` named and pinned) and `DraftB.lean`
(4 fields, radius inlined), written blind. They agree on every *mathematical*
choice — this is the strongest signal in the pair, and it is worth naming what
they agreed on before the differences: the **inhomogeneous** `H^{-1/2}` force
norm, the datum fixed at exactly zero, `ℝ≥0∞` everywhere with no `.toReal`, the
strict lifespan inequality rather than `RegularThrough`, the two universal
constants as fields, and **no restatement of any A02/A04/A05/C01 clause as a
field**. The R43 decision (`research/R43/RECONCILIATION.md` §1) therefore
carries over untouched, and neither draft had to be talked out of a proof
interface.

---

## 1. `radius` as a named field, or inlined?

This is the one packaging decision, and it is **not** a decision about strength:
the two shapes are inter-derivable, which was checked rather than argued.
`toInlined` rewrites A's `main` by `radiusFormula` into B's; `ofInlined` takes
`radius := fun ν S => c * ν ^ (3/2 : ℝ) * Real.exp (-(C*ν*S))`, discharges
`radiusFormula` by `rfl` and `radiusPos` by
`mul_pos (mul_pos hc (Real.rpow_pos_of_pos hν _)) (Real.exp_pos _)`. Both
compile (`/tmp/r44scratch/probe3.lean`, EXIT=0). So `radius` adds **no**
implementation freedom and `radiusPos` adds **no** obligation that `hc` did not
already settle.

**A's shape is adopted.** Three reasons, in order of weight.

**(a) It is the ledger's own skeleton, with the ledger's own reason.**
`research/section4/STATEMENTS.md:611-624` proposes exactly these seven
non-conclusion fields, and `:626-627` gives the reason in one line: "Keeping
`radius` as a field (rather than inlining the formula) lets
`RMainAPI.nonDensityZero` consume `radius ν T` without re-deriving `c, C`."
R43 settled that `STATEMENTS.md` is the skeleton and naming authority
(`research/R43/RECONCILIATION.md` §3, first row), and nothing here contradicts
it.

**(b) One threshold, not two copies of a formula.** The contract has *two*
conclusion fields, and B's inlining writes the radius out in both. Nothing in
the file forces the two copies to agree. A transcription slip in one of them —
`Real.exp (-(C*ν*T))` vs `Real.exp (-C*ν*T)` (different terms, both typecheck),
or `ν ^ (3/2 : ℕ)` which silently means `ν ^ 1` — would leave a structure whose
`main` and whose R41 field carry *different* radii, with no error anywhere.
With `radius` + `radiusFormula` the two fields are the same threshold by
construction, and the formula is stated once, in the one place a reader checks
it against `04-whole-space.tex:143`.

**(c) It is the shape that is harder to satisfy wrongly, in the only place that
question has a nontrivial answer here.** `radiusFormula` quantifies over *all*
real `ν, S`, so it pins `radius` completely; the only freedom left in the whole
structure is the pair `(c, C)`, which is the manuscript's own freedom. B's
inlining has the same property, but only because the formula is repeated — the
pinning is implicit in the repetition rather than stated.

*What is not a reason.* "Fewer fields is better" is the R43 principle, but it
was about restating **sibling clauses** and **proof intermediates** as fields —
both of which create a second, divergent copy of someone else's statement. A
redundant *definitional* field pinned by an equation is a different object: it
duplicates nothing, and it is what the consumer names.

`radiusPos` keeps the ledger's hypotheses `0 < ν → 0 < S` even though `0 < S` is
unused in its proof. That is deliberate: the field records the paper's claim on
the paper's regime (`:137`, "For each `ν, S > 0` there is `r_{ν,S} > 0`"), and a
consumer that has `0 < S` anyway loses nothing.

---

## 2. Expose `C`, or hide it?

**Exposed, as a field, alongside `c`.** The brief asks whether `C` is worth a
field when only the product `c ν^{3/2} e^{−CνS}` is used. It is, for one
reason that is not aesthetic: a hidden `C` would have to live under an
existential inside `radiusFormula` (`∃ C, 0 < C ∧ ∀ ν S, radius ν S = …`), and
then `C` would be chosen *after* nothing in particular — the structure would no
longer record that a **single** `C`, fixed before every `ν` and `S`, governs
every radius. `04-whole-space.tex:143` says "universal positive constants
`c, C`" and `STATEMENTS.md:594` lists `θ, C₀, C₂, C₃, c, C` as all `ν`- and
`S`-free; R41's non-density ball must scale uniformly in the `ν, T` it is
instantiated at. So both constants stay as fields, and the proof's internal
constants `θ, C₀, C₂, C₃` stay out — they belong to the gate `Y ≤ θν` and the
Grönwall bookkeeping, and `STATEMENTS.md:645-648` records that the paper's
outline does not even pin `C₂, C₃`.

---

## 3. The two spellings — settled by running Lean

Neither is a matter of taste; both were checked.

**The exponent: `ν ^ (3 / 2 : ℝ)`.** A wrote `ν ^ ((3:ℝ)/2)`, B wrote
`ν ^ (3/2 : ℝ)`; `example (ν : ℝ) : ν ^ (3/2 : ℝ) = ν ^ ((3:ℝ)/2) := rfl`
succeeds, so they are interchangeable and the ledger's spelling (`:617`) is
taken. The ascription is what makes `^` mean `Real.rpow`
(`ν ^ (3/2 : ℝ) = Real.rpow ν (3/2)` by `rfl`); dropping it in favour of a
natural exponent would silently give `ν ^ 1`, which is why the `radiusFormula`
docstring says so.

**The critical order: `-1 / 2`, not `-(1 / 2)`.** This one is real:

    example : (-1/2 : ℝ) = -(1/2) := rfl
    -- error: type mismatch ... -1 / 2 = -(1 / 2)

`-1/2` parses as `(-1)/2` (prefix `-` binds tighter than `/`), and in `ℝ` the
two terms are not definitionally equal. That matters more than an ordinary
notation choice because the order **indexes a type**: `forceSobolevENorm q s f`
is an infimum over `ℝ → RealVectorSobolev s`, so the two spellings give two
non-defeq types and mixing them costs a transport, not a `rw`. The tie is broken
by the frozen contract: `Contracts/V1/Thresholds.lean:15,16,17` spells the
`q = 2` threshold `-1 / 2` three times (`l2`, `negativeIndex`), and the ledger
skeleton writes `(-1/2)` at `:622`. So `-1 / 2` it is, and
`forceSobolevENormL2 (-1 / 2) f = forceSobolevENorm 2 (-1 / 2) f` holds by
`rfl`.

Two honest riders. First, lane 042's `forceSobolevENorm_ne_top` takes the order
as an implicit with side condition `s ≤ (m : ℝ)` discharged by `norm_num`, so it
applies at *either* spelling — it puts no constraint on the choice. Second,
`Data.criticalOrder 2` is `2 / 2 - 3 / 2` and `ThresholdAPI.exponent 2 0` is
`-1 / 2 - 0`, so R41 will need `norm_num` to reach any literal spelling whatever
R44 writes. The spelling therefore buys lemma reuse across lanes, not a `rfl`
in R41; it is recorded as gap **G7** so the next lane does not re-litigate it.

---

## 4. The R41 consequence field

Kept, named `nonDensityBallZero` (A's name; it names the object R41 wants and
parallels `RMainAPI.nonDensityZero`), with `ν` and `T` universally quantified
even though `RMainAPI` fixes them as fields (`STATEMENTS.md:144`) — a
universally quantified field instantiates, a fixed one would have to be
transported.

Shape: `MemForceR f → ‖f‖ < ofReal (radius ν T) → f ∉ breakdownSetRZero ν T`.
B's `Iff.rfl` claim was verified:

    f ∈ breakdownSetRZero ν T ↔
      MemForceR f ∧ maximalLifespanR ν (fun _ => 0) f ≤ ENNReal.ofReal T

holds by `Iff.rfl` (`Data.lean:686 → breakdownSetR :678 → breakdownSetIn :672`,
`forceClassR :553`). So the field is the literal negation of the breakdown
condition, and the zero datum is spelled the way `breakdownSetRZero` itself
spells it.

The alternative — stating it in `RMainAPI.nonDensityZero`'s own direction,
`∀ f ∈ B^ℝ_{ν,0,T}, ofReal (radius ν T) ≤ ‖f‖` — was considered and rejected.
The `∉` form is the ledger's prose ("contains no element of `B^ℝ_{ν,0,T}`",
`STATEMENTS.md:133-136`) and the paper's ("an open ball about zero disjoint from
`B^ℝ_{ν,0,T}`", `:179`), and the conversion costs the consumer three lines with
**no** extra hypothesis, because `f ∈ B^ℝ_{ν,0,T}` already supplies
`MemForceR f`:

    intro f hf; by_contra hlt; exact h f hf.1 (not_le.mp hlt) hf

(checked, `/tmp/r44scratch/probe3.lean`). Keeping the field at all — rather than
letting R41 instantiate `main` at `S := T` — follows `STATEMENTS.md:522`'s
instruction for R43's twin: the consumer performs no reduction. Here the
reduction saved is smaller than R43's (two lines: `S := T` and the contradiction
with the `≤ ofReal T` inside the set), because `a = 0` and the inhomogeneous
norm are already in `main`; the field is kept for symmetry with R43 and because
`R41` consumes it verbatim.

---

## 5. "Could a wrong implementation satisfy this?" — per field

| field | can it be satisfied by something that is not Prop 4.4? |
|---|---|
| `c : ℝ`, `C : ℝ` | Data; nothing to satisfy. Their force is *where they sit*: as fields they are bound before `ν, S, f`, which is the whole content of "universal". |
| `hc : 0 < c` | **No, and it is the anti-vacuity guard.** With `c ≤ 0` the radius is `≤ 0`, `ENNReal.ofReal (radius ν S) = 0`, nothing in `ℝ≥0∞` is `< 0`, and both conclusion fields become vacuously true. |
| `hC : 0 < C` | Not a guard — any real `C` leaves the radius positive, and `C < 0` would give a *growing* radius, i.e. a strictly stronger (and false) claim. It is a faithfulness marker: it records `:143` and the `:173` / `STATEMENTS.md:641-644` claim that the ball shrinks as `νS` grows. Recorded here because "this field cannot be gamed" is the honest answer, not "this field is load-bearing against vacuity". |
| `radius : ℝ → ℝ → ℝ` | Data, but **fully pinned** by `radiusFormula` at every real `ν, S`, so no wrong radius is choosable. Without `radiusFormula` this field alone would let an implementer pick `radius := fun _ _ => 0` and satisfy both conclusions vacuously — that is exactly why the formula field exists and why it is quantified unrestrictedly. |
| `radiusFormula` | It is an equation between two closed expressions in `c, C, ν, S`; the only way to "satisfy it wrongly" is to spell the right-hand side wrongly, and the two spellings that would do it silently (`(3/2 : ℕ)`, and a homogeneous vs inhomogeneous mix-up elsewhere) are called out in the docstring. |
| `radiusPos` | Derivable from `hc` + `radiusFormula`; adds nothing an implementer could fake. |
| `main` | **Conclusion side: no.** `maximalLifespanR ν (fun _ => 0) f` (`Data.lean:657`) is the supremum over horizons that carry an actual `ClassicalSolutionR`, so it cannot be inflated by a field that is not a solution, and `ENNReal.ofReal S <` is unreachable by any solution that breaks down at or before `S`. The datum `fun _ => 0` is a *specific* field, not a variable, so the clause cannot be dodged by choosing a convenient datum. **Hypothesis side: two routes, both closed.** (i) *Vacuity* — if `forceSobolevENormL2 (-1/2) f` were `⊤` for every `f ∈ 𝓕_ℝ`, the hypothesis would be unsatisfiable and the field vacuously true. Closed: `0 ∈ 𝓕_ℝ` has norm `0`, and lane 042's `forceSobolevENorm_ne_top` (`HalfOrder.lean:156`, `m := 0`, `s := -1/2`, `q := 2`) makes *every* `f ∈ 𝓕_ℝ` finite, so the ball is a genuine neighbourhood and not a singleton. (ii) *Wrong norm* — `forceHomogeneousENorm 2 (-1/2)` would make the field state a proposition the paper says is **false** (`:173`) and would route through lane 042's still-open homogeneous finiteness, so it would also be vacuous meanwhile. Closed by using `forceSobolevENormL2`, which is `Data.lean:225`'s honest measurable-path infimum — not a lower integral that could under-report (the `REVIEW_B` issue `Data.lean` already decided). |
| `nonDensityBallZero` | Same analysis. Additionally `breakdownSetRZero ν T` is the frozen V1 set (`Data.lean:686`), so the `∉` cannot be satisfied by redefining the breakdown condition, and `Iff.rfl` (§4) shows the field is exactly its negation. |

**What the contract deliberately does not rule out.** It says nothing about
forces outside `𝓕_ℝ`. That is the paper's own restriction and it is load-bearing
rather than cosmetic (`04-whole-space.tex:171`, `STATEMENTS.md:633-638`): the
continuation half uses that `‖f‖_{L¹_tL²_x}` and `‖f‖_{L²_tL²_x}` are **finite**,
"even though they are not required to be small". A formalisation that read the
proposition as "an open ball in `L²_tH^{-1/2}` consists of regular inputs" would
be wrong, and it is why Theorem 4.1's converse gives a *relative* open ball.

Honest summary: after the norm choice and lane 042's finiteness, there is **no**
remaining route by which this contract is satisfied by something that is not
Proposition 4.4 — the difference from R43, whose reconciliation had to leave
vacuity open as gap G3.

---

## 6. What upstream must add, ranked by what it blocks

Exact Lean shapes: `COMPARISON.md` §4. Nothing here blocks *stating* R44 —
`Spec.lean` typechecks against `Contracts/V1/Data.lean` alone.

**Already done — verified, not assumed** (and two of these were reported as gaps
by one draft or the other, so they are listed first):

0a. **D01 finiteness at `s = -1/2`, `q = 2` — proved.** Lane 042,
    `formalization/NSFormalization/Section4/D01/HalfOrder.lean:156`
    `forceSobolevENorm_ne_top`, general in `s ≤ (m : ℕ)` and `q ∈ {1,2}`;
    R44's case is `m := 0`. This is the non-vacuity of the smallness ball.
    (Draft A had it as an open D01 obligation; draft B had it right.)
0b. **A04's bounded-horizon continuation — exists.** `research/A04/Spec.lean:613`
    `extendsBeyond`, whose docstring at `:592-594` says it *is* Prop 4.4's field.
    (Draft B reported this as A04's one shape mismatch; it is not.)
0c. **C01's `a = 0` assembly — exists.** `research/C01/Spec.lean:599`
    `h2TimeIntegralZeroDatum`. (Draft B reported this as missing; it is not.)
0d. **A05 is complete for R44's embeddings**, including the
    homogeneous→inhomogeneous comparison the *inhomogeneous* `Y, Z` need
    (`A05/Spec.lean:268,280`). Both drafts agree.

**Blocks R44's own a-priori estimate** — the substance the proof lane owes
itself; nothing else can supply it:

1. **G1 — D01: the operator `J = (I−Δ)^{1/2}` and the exact weight identity**
   `‖u‖²_{H^{3/2}} = ‖u‖²_{H^{1/2}} + ‖∇u‖²_{H^{1/2}}` (exact, not up to
   constants, `STATEMENTS.md:588-590`) plus the duality
   `|⟨f,Ju⟩| ≤ ‖f‖_{H^{-1/2}}‖u‖_{H^{3/2}}` (`:591`). No lane owns `J`; A05 has
   only the inequality `dotThreeHalvesLeGradientSobolev` (`A05/Spec.lean:280`)
   and `‖Jv‖₃ ≤ Cbessel‖v‖_{H^{3/2}}` (`:406`). Small in size (Fourier-weight
   algebra), first in order — G2 cannot start without it.
2. **G2 — R44's own lane: eq:Rcritical2, Grönwall, first-exit time.** Needs a
   *differentiable inhomogeneous critical path* (`Y` carrying `HasDerivAt`), the
   order-`1/2` analogue of `A04/Spec.lean:247` `HasSmoothSobolevPath`, which no
   lane exports. This is R44's twin of R43's gap G7 and the largest single unit
   of the eventual proof lane.

**Blocks R44's continuation half:**

3. **G3 — C01: the `H^{-1/2}` force slice.** `B(t) = ‖f(t)‖_{H^{-1/2}}` as an
   interval-integrable real function with `∫₀ᵗ B² = ‖f‖²_{L²(0,t;H^{-1/2})}`.
   `C01/Spec.lean:326` `forceTimeRegularity` does the order-0 slice only, so the
   Grönwall right-hand side cannot yet be identified with the hypothesis norm.
4. **G4 — R44's lane: the gluing.** Build `SolvesBelow` (`A04/Spec.lean:223`)
   from A02's maximal family, discharge C01's `C₁‖u‖₃ ≤ ν/4` gate from
   `‖u‖₃ ≤ C(1/2)θν` by shrinking `θ`, supply `MemL1Hm` (`A04/Spec.lean:268`,
   free from `MemForceR`). Friction, not new mathematics.
5. **G5 — A04 ↔ C01 power spelling.** `^ (2 : ℕ)` (`A04/Spec.lean:202`) vs
   `^ (2 : ℝ)` (`C01/Spec.lean:576,599`); one `ℝ≥0∞` identity. Identical to
   R43's G6 and **still open** — two consumers now need it, so it should be
   pinned at A04 (which exports the `def`) rather than bridged twice.

**Packaging; blocks nothing mathematically:**

6. **G6 — D01: register lane-042 `forceSobolevENorm_ne_top`** into
   `DatumLemmas` V2 plus a `Bindings` import of `HalfOrder`, so item 0a is a
   contract fact inside the build closure rather than a theorem beside it.
7. **G7 — pin the `-1 / 2` spelling tree-wide** (§3), matching
   `Contracts/V1/Thresholds.lean:15-17`.
8. **G8 — A02, A04, A05, C01 must land as registered contracts**; they are
   research-stage specs, and R44 cannot bind until they do.

---

## 7. Commands run

    cd <WT> && bash scripts/lean-install.sh                      # == OK
    . scripts/lean-env.sh ; export LEAN_NUM_THREADS=6
    cd <WT>/verification
    lake env lean ../research/R44/DraftA.lean                    # EXIT=0
    lake env lean ../research/R44/DraftB.lean                    # EXIT=0
    lake env lean ../research/R44/Spec.lean                      # EXIT=0
    lake env lean /tmp/r44scratch/probe.lean                     # EXIT=1 (intended)
    lake env lean /tmp/r44scratch/probe2.lean                    # EXIT=0
    lake env lean /tmp/r44scratch/probe3.lean                    # EXIT=0

`DraftA.lean`, `DraftB.lean`, `COMPARISON_A.md`, `COMPARISON_B.md` are
unmodified. `Spec.lean` has no `sorry` / `admit` / `axiom` / `native_decide`
(the words occur only in the module docstring), one `structure`, no `def`, no
proof term, no placeholder `Prop` field, and no warnings.
