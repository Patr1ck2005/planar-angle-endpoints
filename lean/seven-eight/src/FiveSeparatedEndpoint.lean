import FiveSeparatedMargin
import FourSiteEndpoint

noncomputable section
namespace R87.Stability
open Real JSP404 R55.WeightedCollision

/-- Uniform unconditional angular gap at the physical 120-degree endpoint.
The point count only enters via the requirement that the five chosen points
can be completed by two further distinct points of the same set. -/
theorem five_separated_endpoint {ρ:ℝ} (rp:0<ρ) :
    ∃ε:ℝ,0<ε ∧ ∀(S:Finset Point),7≤S.card→∀c:Fin 5→Point,(∀i,c i∈S)→
      (∀i j,i≠j→ρ*Metric.diam (S:Set Point)≤dist (c i) (c j))→
      2*π/3+ε<maxAngle S := by
  apply five_separated _ rp
  intro m five c ci w wp hit
  exact R90.Endpoint.total_le_six ci wp (by simpa using five) hit

end R87.Stability
#print axioms R87.Stability.five_separated_endpoint

