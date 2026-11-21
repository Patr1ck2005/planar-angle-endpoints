import AllBlockers
import FiveCenterPublic

noncomputable section
namespace R85.CriticalMass
open Real JSP404 R54.GapTest R55.WeightedCollision R56.Windows Finset R65.Retention

/-- Necessary conditions at one actual support, including quantitative tests against
every internally compatible trial kit and the simultaneous cost of every deletion. -/
structure Profile {h : ℕ} (c : Fin (h+1)→Point) (θ : ℝ) {m : Fin (h+1)→ℕ}
    (R : ∀i,Row (m i)) (x : Fin (h+1)) (B k : ℕ) : Prop where
  least : ∀i,score R x (π-θ)≤score R i (π-θ)
  exponent : score R x (π-θ)≤k
  divides : mass R θ x ∣ B
  total : capacity R θ=B+mass R θ x
  attains : (∑i,one_light R θ x i)=B+1 ∧ θ∈attainable (one_light R θ x) c
  deletions : ∀{t : ℕ},2≤t → t<h+1 → ∀e : Fin t↪Fin (h+1),∀{p : Fin t→ℕ},∀Q : (j:Fin t)→Row (p j),
    Represents Q (c∘e) → Witnessed Q (c∘e) →
    mass R θ x+(∑j,(mass Q θ j-mass R θ (e j)))≤∑i∈removed e,mass R θ i
  obstruction : ∀j,∀r : ℕ,0<r → ∀u : Fin (score R j (π-θ)+r)→Point, InternalTrial u θ →
    mass R θ x+(2^r-1)*mass R θ j≤∑i∈blockers c θ j u,mass R θ i

theorem profile_of_critical {h b k : ℕ} (two : 2≤h) (enough : b≤h)
    {c : Fin (h+1)→Point} (ci : Function.Injective c) {θ : ℝ} (pos : 0≤θ)
    (below : θ<π) (mac : Macro c θ) {m : Fin (h+1)→ℕ} (R : ∀i,Row (m i))
    (front : Represents R c) (back : Witnessed R c) (room : b*2^k+1≤capacity R θ)
    (crit : Critical c (b*2^k+1) θ) :
    ∃x,Profile c θ R x (b*2^k) k := by
  obtain ⟨x,least⟩:=Finite.exists_min (fun i=>score R i (π-θ))
  obtain ⟨ex,dv,full⟩:=endpoint R two enough ci below front room crit x least
  refine ⟨x,least,ex,dv,full,endpoint_weighting R two enough ci pos below mac front back room crit x least,?_,?_⟩
  · intro t tt prop e p Q fwd rev
    exact deletion_budget R full crit below front tt prop e Q fwd rev
  · intro j r rp u kit
    exact all_blockers (by omega) ci pos below R front back full crit j rp u kit

/-- For both staircase endpoints, a proof on only the exact critical profiles
below suffices for the unrestricted original planar problem, for all support sizes
at once. -/
theorem unrestricted_endpoint_iff (b k : ℕ) (shape : b=4 ∨ b=5) :
    alpha (b*2^k+1)=Jsp404.alphaN (b*2^k+1) ↔
      ∀h : ℕ,5≤h → h+1≤b*2^k+1 → ∀c : Fin (h+1)→Point, Function.Injective c →
      ¬R58.CircleModel.OnCircle c → ∀θ : ℝ,0≤θ → θ<π → Macro c θ →
      ∀{m : Fin (h+1)→ℕ},∀R : (i:Fin (h+1))→Row (m i),Represents R c → Witnessed R c →
      Critical c (b*2^k+1) θ → ∀x,Profile c θ R x (b*2^k) k → Jsp404.alphaN (b*2^k+1)≤θ := by
  have power : 1≤2^k := Nat.one_le_pow _ _ (by decide)
  have ge : 3≤b*2^k+1 := by rcases shape with rfl|rfl <;> omega
  rw [R67.FiveCenter.unrestricted_iff_six ge]
  constructor
  · intro solved h five small c ci nc θ pos below mac m R front back crit x P
    have mp : 0<mass R θ x := pow_pos (by decide) _
    exact solved (by omega) small c ci nc θ pos below mac ⟨m,R,front,back,by rw [P.total];omega⟩ crit
  · rintro bounded size six small c ci nc θ pos below mac ⟨m,R,front,back,room⟩ crit
    cases size with
    | zero => omega
    | succ h =>
      have enough : b≤h := by rcases shape with rfl|rfl <;> omega
      obtain ⟨x,P⟩:=profile_of_critical (by omega) enough ci pos below mac R front back room crit
      exact bounded h (by omega) small c ci nc θ pos below mac R front back crit x P

end R85.CriticalMass
#print axioms R85.CriticalMass.profile_of_critical
#print axioms R85.CriticalMass.unrestricted_endpoint_iff
