import ExactFiveCapacity
import OrdinaryFiveStability
import BoardCombination
import OrderMaskOrbit
import FiveBoardsExact
noncomputable section
namespace R67.FiveCenter
open Real JSP404 R55.WeightedCollision R54.GapTest R56.Windows
theorem finite_law : R67.Board.FiniteBoardLaw := by
  apply R67.Final.finite_board_law
  · intro o ori
    obtain ⟨w,_,hw,h⟩:=R67.OrderOrbit.masks_of_orient o ori
    exact ⟨w,hw,h⟩
  · intro word hw u h hu hh
    exact R67.Five.of_mem hw hu hh

/-- Every five-center collision model at arbitrary positive fiber weights
obeys the original Sendov staircase. -/
theorem lower {c : Fin 5→Point} (ci : Function.Injective c) (w : Fin 5→ℕ)
    (pos : ∀i,0<w i) {θ : ℝ} (hit : θ∈attainable w c) : Jsp404.alphaN (∑i,w i)≤θ :=
  R67.Board.five_of_finite finite_law ci w pos hit

/-- Optimizing over the class of supports of sizes two, three, four or five
gives precisely the published threshold for every N at least three. -/
theorem sharp {N : ℕ} (ge : 3≤N) : IsLeast (R67.FiveConclusion.scores N) (Jsp404.alphaN N) :=
  R67.FiveConclusion.sharp_of_law finite_law ge

/-- The unrestricted remaining case consists of nonconcyclic, retention-critical
supports of cardinality at least six. -/
theorem unrestricted_iff_six {N : ℕ} (ge : 3≤N) :
    alpha N=Jsp404.alphaN N ↔
      ∀{k : ℕ},6≤k→k≤N→∀(c : Fin k→Point),Function.Injective c→
      ¬R58.CircleModel.OnCircle c→∀θ : ℝ,0≤θ→θ<π→Macro c θ→
      (∃m : Fin k→ℕ,∃R : ∀i,Row (m i),Represents R c ∧ Witnessed R c ∧ N≤R65.Retention.capacity R θ)→
      R65.Retention.Critical c N θ→Jsp404.alphaN N≤θ :=
  R67.FiveConclusion.six_of_law finite_law ge
/-- Exact five-site capacity over an interval of each angular strip. -/
theorem exact_capacity {n : ℕ} (hn : 16≤n) {θ : ℝ}
    (low : π-R64.Five.defect n≤θ) (high : θ<π-π/((n:ℝ)+1)) :
    R67.FiveCapacity.totals θ=Set.Icc 5 (R64.Five.size n) :=
  R67.FiveCapacity.interval_of_law finite_law hn low high

/-- Six ordinary points separated at the scale of the whole configuration. -/
theorem six_separated {N : ℕ} (ge : 3≤N) {ε : ℝ} (eps : 0<ε) :
    ∃δ : ℝ,0<δ ∧ ∀S : Finset Point,S.card=N → maxAngle S≤Jsp404.alphaN N-ε →
    ∃z : Fin 6→Point,(∀i,z i∈S) ∧ ∀i j,i≠j → δ*Metric.diam (S:Set Point)<dist (z i) (z j) :=
  R69.Stability.six_separated ge (sharp ge).2 eps
#print axioms exact_capacity
#print axioms six_separated
#print axioms finite_law
#print axioms lower
#print axioms sharp
#print axioms unrestricted_iff_six
end R67.FiveCenter
