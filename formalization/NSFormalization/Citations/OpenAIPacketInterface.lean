import NSFormalization.Source.ViscosityPacket
/-! OpenAI Theorem 1.1 exact wrapper. Status: CITED_EXACT. -/
namespace NSFormalization.Citations
open NSFormalization.Source
 theorem openai_compact_packet (ν : ℝ) (hν : 0 < ν) :
    ∃ u p f K, NavierStokesR3.ProblemStatement.CandidateProperties ν u p f K := by
  obtain ⟨u,p,f,K,h,_,_⟩ := selected_packet_every_viscosity hν
  exact ⟨u,p,f,K,h⟩
end NSFormalization.Citations
