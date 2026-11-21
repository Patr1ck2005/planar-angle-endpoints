import EnclosedAngle
import FullProblem

noncomputable section
namespace R89.Original
open Real JSP404 R54.GapTest R55.WeightedCollision R56.Windows R65.Retention R85.CriticalMass

/-- It suffices to consider endpoint profiles whose every row of exponent at
least k is an extreme site of the *full* configuration. -/
def VertexProfiles (b k : ℕ) : Prop :=
  ∀h : ℕ,5≤h → h+1≤b*2^k+1 → ∀c : Fin (h+1)→Point,Function.Injective c →
  ¬R58.CircleModel.OnCircle c → ∀θ : ℝ,0≤θ → θ<π → Macro c θ →
  ∀{m : Fin (h+1)→ℕ},∀R : (i : Fin (h+1))→Row (m i),Represents R c → Witnessed R c →
  Critical c (b*2^k+1) θ → ∀x,Profile c θ R x (b*2^k) k →
  (∀i,k≤score R i (π-θ) → c i∉convexHull ℝ (c '' {j | j≠i})) →
  Jsp404.alphaN (b*2^k+1)≤θ

theorem endpoint_top (b k : ℕ) (shape : b=4 ∨ b=5) :
    Jsp404.alphaN (b*2^k+1)≤π-π/((k:ℝ)+3) := by
  have pow:=Nat.two_pow_pos k
  rcases shape with rfl|rfl
  · have val:=(R52.ThreeCover.full_staircase (N:=4*2^k+1) (by omega)).unique
      (R52.ThreeCover.low_band (k:=k) (by omega) (by omega))
    rw [val]
    have den : 0<2*(k:ℝ)+5:=by positivity
    have den' : 0<(k:ℝ)+3:=by positivity
    apply sub_le_sub_left
    apply (div_le_div_iff₀ den' den).mpr
    nlinarith only [pi_pos]
  · exact ((R52.ThreeCover.full_staircase (N:=5*2^k+1) (by omega)).unique
      (R52.ThreeCover.high_band (k:=k) (by omega) (by omega))).le

theorem full_iff_vertices : R85.Original.AllCardinalities ↔ ∀b k,(b=4 ∨ b=5)→VertexProfiles b k := by
  rw [R85.Original.full_iff_profiles]
  constructor
  · intro all b k shape h le sz c ci nc θ pos below mac m R rep wit crit x prof _
    exact all b k shape h le sz c ci nc θ pos below mac R rep wit crit x prof
  · intro check b k shape h le sz c ci nc θ pos below mac m R rep wit crit x prof
    by_contra! bad
    have short:=bad.trans_le (endpoint_top b k shape)
    have div : π/((k:ℝ)+3)<π-θ:=by linarith only [short]
    have top:=(div_lt_iff₀ (by positivity : 0<(k:ℝ)+3)).mp div
    apply bad.not_ge (check b k shape h le sz c ci nc θ pos below mac R rep wit crit x prof _)
    intro i heavy
    exact R89.Interior.heavy_vertex ci pos below mac R rep i (by linarith only [top]) heavy
end R89.Original
#print axioms R89.Original.full_iff_vertices
