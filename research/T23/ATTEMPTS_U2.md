# Lane 477 / U2 attempts

Initial scope: exact G0 counterexample and repaired quantifiers; raw local
correction, spatial extension and un-periodised cross transport.

The implementation layer cannot import Contracts. Exact Spec checks therefore
run in a standalone research probe; no substitute API is introduced.

Initial inspection: `sed` on a guessed T14/PacketImport.lean and
`rg` on T16/CompactCorrection.lean failed with `No such file or directory`.
The actual local radial-potential results live in T16/BallPotential.lean.
