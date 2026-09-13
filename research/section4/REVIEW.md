# Review of `research/section4/STATEMENTS.md` (lane 006, Section 4 statement ledger)

**VERDICT: ACCEPT-WITH-NOTES.**
The ledger is a faithful transcription of Section 4. Every paper citation I checked
resolves (one off-by-one), every DAG citation matches `DEPENDENCY_GRAPH.md` and
`tasks.json`, and the two structural defects it reports (items 2, 3) are real and do
change the task graph. Notes: (a) the three homogeneous usages are not three *objects*,
(b) concrete defects in both pseudo-Lean skeletons, (c) imprecise "missing edge" phrasing.
Line numbers below are `04-whole-space.tex` unless another file is named.

---

## Item 1 — three homogeneous realizations, Ḣ^{3/2} only as a quantity: **PARTLY**

The *inventory* is correct and correctly located:
* Appendix-B Λ^a completion, `appendix-b-embeddings.tex:44` (`0<a<3/2`), `:51–53`,
  `:56–70` (realization `v̂=|ξ|^{-a}G`, `G∈L²`); used by Prop 4.3 at `04:91`.
* Bare Fourier integral for `−3/2<s<0` on smooth compact profiles: `04:70–72`, plus
  `(1+|ξ|²)^s ≤ |ξ|^{2s}` at `04:71`.
* `eq:homogeneous-realization`, `02-preliminaries.tex:57–70`, used by Prop 4.6 at
  `04:219`, `04:241–249`, `04:264–271`.
* Ḣ^{3/2} never completed: App. B's range `0<a<3/2` is **exclusive** (`:44`, `:64`) and
  `:101–102` says "no embedding of Ḣ^{3/2} into L^∞ is asserted"; in Section 4 it appears
  only as `z=‖Λ^{3/2}u‖₂` (`04:91`). But `‖v‖_{Ḣ^{3/2}}` does occur as *notation* in
  `appendix-b:31,107` and `appendix-a:24`, so D01 must still define that norm; L465–467
  elides this.

**Refuted sub-claim: a single D01 abstraction is not impossible.** All three are the same
formula. Define once, for `−3/2 < s < 3/2`,
`Ḣ^s = {h ∈ S' : ĥ measurable, |ξ|^s ĥ ∈ L²}`, `‖h‖ = ‖|ξ|^s ĥ‖₂`.
`s=1/2,1` is realization 1 (App. B `:56–70` *is* this set; `:67–69` proves the annular
class is dense in it, i.e. the completion equals it); `s=−1` is realization 3 verbatim
(`02-prelim:59–61`); realization 2 is the *lemma* "smooth compactly supported ⟹ finite
`Ḣ^s` norm for `s<0`" (`04:70`). Temperedness holds uniformly on `|s|<3/2` by the estimate
the paper gives twice (`appendix-b:58–65`, `02-prelim:66–69`). Recommend one D01 definition
plus three lemmas.

## Item 2 — Lemma A.1 / A03 used by R42's lifespan step, edge missing: **CONFIRMED**

Decisive sentence, `04:53`: "An extension through `T` would be bounded in `C_tH²` on a
neighborhood of `T`, hence bounded in `L^∞_x` by \eqref{eq:Rproduct}, contradicting the
blowup of `U_ε`." `eq:Rproduct` is `appendix-a-local-theory.tex:9–13` (Lemma A.1
`lem:calculus`), whose second clause is `‖v‖_∞ ≤ C‖v‖_{H²}`. `tasks.json` assigns `lem:calculus`
to **A03** (`manuscript_labels: ["lem:calculus"]`), whose title is "tame products and
**bounded representatives**"; A05 carries only the homogeneous clauses (its label is
`lem:critical-embeddings`), so the `L^∞` bound is A03's. DAG: `R42 ← I03, A02`
(`DEPENDENCY_GRAPH.md:57–58`); R42's ancestors are I03←I02←I01,D01 and
A02←A01←D01,U02,U04,U01,U05. **A03 is not among them**; its only out-edges are `A03→A04`
and `A03→T01` (`:49`, `:82`), and A04 is not an R42 ancestor either. The torus twin
(`03-torus.tex:339`) does *not* use `eq:Rproduct`, so this is Section-4-specific.

## Item 3 — R45 ← R41 insufficient; R46 cites Cor 4.5, DAG says R41D: **CONFIRMED**

Cor 4.5's proof, `04:198`: "the force correction in **Theorem~\ref{thm:Rinsert}** is
spacetime compact. Addition of that correction preserves each stated force class."
Theorem 4.1's statement (`04:7–14`) says nothing about the support of `f−g`; that is
Theorem 4.2 conclusion 5 (`04:38`). So R41's *contract* cannot discharge R45. (Nuance:
`R42 → R41D → R41 → R45` already makes R42 a transitive ancestor, so this is an interface
gap, not a reachability gap — see errors.)

Prop 4.6's proof, `04:262`: "**Corollary~\ref{cor:Rclasses}** supplies a singular smooth
compact force within the other half." DAG has `R41D → R46` (`:74`) and `R45 ← R41`
(`:71`), with no `R45 → R46`. Confirmed disagreement. Note the *homogeneous* half
(`04:271`) does **not** cite Cor 4.5 — it re-runs the two-case argument with the `s=−1`
scaling — so `I03 → R46` (`:77`) is separately load-bearing and correct.

## Item 4 — one threaded ε-family across 4.2 / 4.6(B) / 4.7: **CONFIRMED**
`04:42` "All of these conclusions hold for the same family of inserted solutions.";
`04:221` "For every reference in Theorem~\ref{thm:Rinsert}, one may **simultaneously**
arrange"; `04:271` "prove the simultaneous convergence for the same family."; `04:303`
"while `T^ν_{max,R}(a,g_ε)=T` **and** the energy and force convergences in
Proposition~\ref{prop:Renergy} hold." The single-ε₀ reading is supported by `04:32`
("for all sufficiently small ε>0") together with `04:320` ("the convergence estimates are
unaffected by this fixed upper bound on ε"), which is exactly a minimum-of-constraints
statement. Ledger §9.2/§9.3 (L1114–1125) are accurate.

## Item 5 — 4.2 exports neither div-freeness nor the compact pressure: **CONFIRMED**

Theorem 4.2's statement (`04:31–43`) mentions the velocity difference only through
"supported inside `B` at every `t<T`" (`04:38`), and never mentions `p_ε` or `π` at all.
Its **proof** does fix the pressure: `04:51` "The pressure difference may be chosen to be
the compact scalar `P_ε`". Divergence-freeness is *not* stated even in 4.2's proof; it is
imported with Lemma 3.4 (`03-torus.tex:188` "smooth, divergence-free field") and
Prop. 3.3 (`03-torus.tex:141`) via `04:23–27`, and is displayed only in the torus twin,
**Theorem 3.6(iii)** (`03-torus.tex:295`: "`u_ε−v` divergence free and supported, for
every `t<T`, …"). Theorem 4.7's proof uses both: `04:306` ("using the compact pressure
representative … `δp=p_ε−π=P_ε`") and `04:308` ("`δu` is smooth, **divergence free** and
compactly supported in its interior"). So both must be added to R42's exported contract.

## Item 6 — quantifiers: **CONFIRMED** (all three)
* Converse only at `a=0`: `04:10` "(i) For every fixed `a∈X_R` … dense if `s<s_q`";
  `04:11` "(ii) For zero initial velocity … if and only if `s<s_q`."
* Prop 4.4 uses finiteness, not smallness, of the `L²` force norms: `04:171` "Because
  `f∈F_R`, its `L^1_tL^2_x` and `L^2_tL^2_x` norms are finite, even though they are not
  required to be small." Combined with `04:8` ("In the relative … topology on `F_R`") and
  `04:179` ("These nonempty **relative** open balls prove non-density"), the relative-ball
  reading is right; an abstract `L²_tH^{-1/2}`-ball statement would be unproved.
* Theorem 4.7 only on `0 ≤ t < T`: displayed at `04:300–302`. The audit's C3
  (`SOL_MAX_AUDIT_SYNTHESIS_20260912.md:104–123`) gives the `F^♯=F+χ(σ)ψ(x)e`
  counterexample to any all-time reading; `04:76` confirms post-`T` force support.

## Item 7 — skeleton spot-check: **PARTLY** (both skeletons have concrete defects)

`RMainAPI` (L128–159): faithful on (i)/(ii)/non-density, including the correct endpoint
`exponent q 0 ≤ s` (L146; the proof's embeddings need `s ≥ 1/2` and `s ≥ −1/2`, `04:179`).
Defects — L156 ties the "same earlier history" window to the *force* radius (`t ≤ T-ρ`)
whereas the paper's window is `T − 2ε²` (`04:36`), two independent parameters; L150–158
omits `limsup_{t↑T}‖u‖_∞ = ∞` (`04:35`, and `02-prelim:47–48` "unbounded speed at their
terminal time"), so "singularity exactly at `T`" is under-stated as `Tmax = T`; L155 uses
a 4-argument `IsMaximalSolution` while L308 uses 5; L145–148 leaves the non-density centre
existential while `RClassesAPI` (L661) correctly centres it at `0`, which is what `04:179`
proves.

`RInsertAPI` (L285–327): conclusions 1–8 of `04:31–43` are all present and correctly
quantified over one `ε₀`-family. Defects — L321–324 uses `Cconst` before declaring it
(field-order error); L325 hardcodes `2/q - 3/2` in violation of the ledger's own rule at
L38–39, and the structure has no `thresholds` field to route through; L313 and L319 write
`∀ t, t < T` where the paper's velocity lives on `[0,T)` (`04:36`, `04:38`); L310–311
replaces the displayed `limsup … = ∞` (`04:35`) with `¬ BoundedNear` (equivalent, but a
restatement); L315/L319 add two conclusions absent from `04:31–43` — legitimate, but the
justification at L329–330 ("proved inside its proof") holds only for `pressureCompact`
(`04:51`), not for `velDivFree` (see item 5); the hypothesis `T^ν_{max,R}(a,g) > T+δ`
flagged in the risk note at L340 never appears in the skeleton.

## Item 8 — the five open questions: **CONFIRMED** (all five are real)
* **Grid offset / half-open cells.** Real. `04:288` says only "complete uniform Cartesian
  grid of `R³` with positive mesh widths" — nothing about offset or cell closure (the
  plural does support per-axis widths). The proof uses only a closed measure-zero locally
  finite union of planes (`04:306`), infinitely many cells (`04:295`) and the divergence
  theorem on a box (`04:311`), all insensitive to half-open vs closed. The ledger's
  recommendation is the strongest reading the proof supports.
* **`F_rd ⊆ F_R` unproved.** Real and load-bearing: `Tmax`, Thm 4.2 and Props 4.3/4.4 all
  require `F_R` membership (`02-prelim:17–21`, `04:32`, `04:83`, `04:139`), yet the paper
  only asserts class preservation (`04:198`) and never checks `C^∞([0,∞);H^∞)` or finite
  `L^1_t`/`L^2_t` `H^m` norms. Routine and true; must be a D01 obligation. `F_c ⊆ F_rd`
  likewise needs the zero extension to `t=0`, valid since the time support is compact in
  the *open* half-line (`04:185`).
* **"Regular through `T+δ`" nesting.** Real; `04:32` vs the definition at
  `02-prelim:34–36`. Already adjudicated harmless as O2 in the audit
  (`SOL_MAX_AUDIT_SYNTHESIS_20260912.md:209–216`). The ledger's recommendation matches.
* **`Sing_c = F_c` in Prop 4.6.** Real ("smooth compact forces" at `04:219` is undefined
  there) and settled by the paper: the approximants at `04:260` are "jointly smooth with
  compact support strictly inside `R³×(0,∞)`", exactly `F_c` (`04:185`); `04:262`/`04:271`
  say "compact smooth reference force".
* **Rider sentence as a field.** Real. `04:13` states it; `04:179` says "The energy and
  earlier-history assertions are part of the insertion theorem", i.e. it is a re-export
  of R42, which the ledger says at L122–123 while nonetheless making it a field at L150.
  Defensible as a re-export, but see the L156 defect above.

---

## Errors found in the ledger (STATEMENTS.md line numbers)

1. **L1027–1035, L462–467** — "three distinct objects" over-claims. One definition covers
   all three (item 1). Recommend rewriting §8.4 as one object + three lemmas.
2. **L321–324** — `energyRate` references `Cconst` one field before its declaration.
3. **L325** — hardcoded `2/q - 3/2` contradicts the ledger's own mandate at L38–39; add a
   `thresholds : ThresholdAPI` field to `RInsertAPI`.
4. **L156** — history window `t ≤ T - ρ` misquantified; paper gives `t ≤ T − 2ε²`
   (`04:36`), independent of the approximation radius.
5. **L150–158** — rider omits the `limsup_{t↑T}‖u‖_∞ = ∞` clause (`04:35`).
6. **L155 vs L308** — `IsMaximalSolution` used with 4 and 5 arguments.
7. **L313, L319** — `∀ t, t < T` should be `0 ≤ t → t < T`.
8. **L329–330** — "proved inside its proof" is accurate for `pressureCompact` (`04:51`)
   but not for `velDivFree`; cite Lemma 3.4 (`03-torus.tex:188`) via `04:23–27` and
   Thm 3.6(iii) (`03-torus.tex:295`) instead.
9. **L364–365** — cites `01-introduction.tex:151` for "imposes no endpoint value at `T`";
   the sentence is at `01-introduction.tex:149–150`.
10. **L796–805** — `simultaneous`/`differenceOnly` are stated as `∀ ins : RInsertAPI`,
    which is stronger than `04:221` ("one may simultaneously arrange") and is not implied
    by `RInsertAPI`'s own fields for the `L²_tḢ^{-1}` clause; `differenceOnly` also drops
    the `ins.ν = ν` guards.
11. **L145–148 vs L656–661** — non-density is existential in `RMainAPI` but centred at `0`
    in `RClassesAPI`; `04:179` centres at `0` in both cases. Make them match.
12. **L667–670, L1172** — "Missing DAG edge `R42 → R45`" is imprecise: `R42` already
    reaches `R45` transitively via `R41D → R41 → R45`. The defect is that `R41`'s
    *contract* does not carry the compact force difference. Reword as an interface gap.

## Recommended DAG changes

1. **Add `A03 → R42`** (item 2). No cycle: `A03 ← D01, U04, A05` and none of those
   descends from `R42`. The ledger's alternative — have `A02` export an `L^∞`-blowup
   continuation criterion — additionally requires `A03 → A02` (today `A02 ← A01` only, and
   `A01` does not depend on `A03`), so the direct edge is cleaner. Name
   `‖z‖_∞ ≤ C‖z‖_{H²}` as an input in `R42`'s contract text.
2. **Make `R41D` class-parametric** over `Y ∈ {F_R, F_c, F_rd}` (its contract in
   `tasks.json` currently fixes no class), and **route `R41D → R45`** alongside the
   existing `R41 → R45`. This is the interface fix for item 3's first half; `R45` still
   needs `R41` for the two critical balls (`04:198`).
3. **Keep `R41D → R46` and do not add `R45 → R46`**, provided change 2 lands: `R46` then
   consumes the same `F_c` instance of `R41D` that `R45` does, matching `04:262` without
   dragging `R43`/`R44` into `R46`'s closure. If change 2 is rejected, add `R45 → R46`
   instead (no cycle, but a wider closure).
4. **No new edge for item 5**: `R42 → R47` already exists. Instead amend `R42`'s contract
   to export `u_ε − v` divergence free and `p_ε − π = P_ε` compactly supported (the
   compact gauge), and amend `R47`'s to permit the extra spatially constant `κ(t)`
   (`04:303`, `04:320`).
5. **No change** to `I03 → R46`: the `s = −1` homogeneous estimate at `04:264–270` is
   genuinely I03's, independent of the Cor 4.5 route.
