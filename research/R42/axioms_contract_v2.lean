import Bindings.InsertionLifespanV2

/-! Axiom + hypothesis-signature audit for lane 114 (`R42.insertion_lifespan_v2`).

Every public declaration of `Bindings/InsertionLifespanV2.lean` must print exactly
`[propext, Classical.choice, Quot.sound]`.  The two `#check`s confirm the bound V2
API needs only the two version-one hypotheses `hg`/`hreg` beyond `F` — no new
hypothesis. -/

open BlowupDensity.Bindings.InsertionLifespan

#print axioms blowup_essSup
#print axioms insertionLifespanV2API
#print axioms insertionLifespanV2API_family

-- Hypothesis-signature check: the bound V2 API takes exactly `F`, `hg`, `hreg`,
-- the same explicit arguments as the version-one `insertionLifespanAPI`.
#check @insertionLifespanV2API
#check @insertionLifespanAPI
