/-!
# Citation records for the citation-first plan

This file contains metadata only. It deliberately does not turn a bibliography
entry into a theorem. Exact mathematical interfaces are specified in
`docs/CITATION_INTERFACE_PLAN_20260911.md`; each planned interface must be
expanded with the project's concrete solution and norm structures before it is
imported by the certified umbrella.
-/
namespace NSFormalization.Citations

structure CitationRecord where
  key : String
  authors : String
  title : String
  locator : String
  url : String
  version : String
  localArtifact : String
  status : String

 def openaiPacket : CitationRecord :=
  { key := "openai-thm-1.1"
    authors := "OpenAI"
    title := "Finite Time Blowup for Navier--Stokes"
    locator := "Theorem 1.1"
    url := "https://cdn.openai.com/pdf/32d9f210-8b73-45e0-91bc-82a30aef8a9a/navier-stokes.pdf"
    version := "official manuscript accessed 2026-09-11; Lean revision 8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538"
    localArtifact := "references/cited/OpenAI_Finite_Time_Blowup_for_Navier_Stokes.pdf"
    status := "CITED_EXACT after CandidateProperties field audit" }

def fujitaKato : CitationRecord :=
  { key := "fujita-kato-1964"
    authors := "H. Fujita and T. Kato"
    title := "On the Navier--Stokes initial value problem. I"
    locator := "Archive for Rational Mechanics and Analysis 16 (1964), 269--315"
    url := "https://doi.org/10.1007/BF00276188"
    version := "1964"
    localArtifact := "references/cited/Fujita_Kato_1964.html"
    status := "CITED_BACKGROUND; exact forced interface pending" }

end NSFormalization.Citations
