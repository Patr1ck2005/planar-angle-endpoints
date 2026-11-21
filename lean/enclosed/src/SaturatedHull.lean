import ConvexArcMass
import SaturatedCone

noncomputable section
namespace R90.ConvexArc
open JSP404 Real Finset R86.ConvexMass R55.WeightedCollision R65.Retention R54.GapTest R56.Windows R85.CriticalMass
open InnerProductGeometry

/-- A saturated complete physical row spends at least (k+2)δ of exterior
turn on the convex polygon. The only required strip inequality is strict. -/
theorem saturated_turn {n k : ℕ} {c : Site n→Point}
    {θ : ℝ} (pos : 0≤θ) (below : θ<π) (mac : Macro c θ)
    {m : Site n→ℕ} (R : ∀i,Row (m i)) (front : Represents R c)
    (top : π<((k:ℝ)+3)*(π-θ)) (i : Site n) (sat : k+1≤score R i (π-θ)) :
    ((k:ℝ)+2)*(π-θ)≤exterior c i := by
  obtain ⟨z,g⟩:=R66.Five.long_gap (R i) (sub_pos.mpr below) top sat
  obtain ⟨u,_,cover⟩:=R66.Five.viewing_cone mac pos (by nlinarith only [top,g]) i
    (R66.Five.complement_interval R front i z)
  have pn:=(primary i).1
  have nn:=(primary i).2.1
  have left:=cover _ pn.symm
  have right:=cover _ nn.symm
  rw [InnerProductGeometry.angle_comm] at left
  have tri:=angle_le_angle_add_angle (c i-c (prev i)) u (c i-c (next i))
  have eq : angle (c i-c (prev i)) (c i-c (next i))=EuclideanGeometry.angle (c (prev i)) (c i) (c (next i)) := by
    change _=angle (c (prev i)-c i) (c (next i)-c i)
    rw [←neg_sub (c (prev i)) (c i),←neg_sub (c (next i)) (c i),angle_neg_neg]
  rw [eq] at tri
  unfold exterior
  linarith only [left,right,g,tri]

/-- A family S of saturated rows forces (number of sites + (k+1)|S|)δ≤2π,
with no retention-criticality or equal-capacity requirement. -/
theorem saturated_turn_budget {n k : ℕ} {c : Site n→Point} (ci : Function.Injective c)
    (hull : HullOrder c) {θ : ℝ} (pos : 0≤θ) (below : θ<π) (mac : Macro c θ)
    {m : Site n→ℕ} (R : ∀i,Row (m i)) (front : Represents R c)
    (top : π<((k:ℝ)+3)*(π-θ)) (S : Finset (Site n)) (sat : ∀i∈S,k+1≤score R i (π-θ)) :
    (((n:ℝ)+3)+((k:ℝ)+1)*S.card)*(π-θ)≤2*π := by
  classical
  have tip (i : Site n) : (π-θ)+(if i∈S then ((k:ℝ)+1)*(π-θ) else 0)≤exterior c i := by
    by_cases mem:i∈S
    · rw [ite_eq_left mem]
      linarith only [saturated_turn pos below mac R front top i (sat i mem)]
    · rw [ite_eq_right mem,add_zero]
      have H:=primary i
      have cap:=mac (prev i) i (next i) H.1 H.2.2.1 H.2.1.symm
      unfold exterior
      linarith
  have cap:=sum_le_sum (s:=univ) (fun i _=>tip i)
  rw [total_turn ci hull,sum_add_distrib] at cap
  have target : (∑i : Site n,if i∈S then ((k:ℝ)+1)*(π-θ) else 0)=S.card*(((k:ℝ)+1)*(π-θ)) := by simp
  rw [target,sum_const,nsmul_eq_mul,card_univ,Fintype.card_fin] at cap
  push_cast at cap
  linarith only [cap]

/-- Throughout the open fourth high strip (and below it), a row of true
capacity at least eight forces at most six actual vertices of a strict convex hull. -/
theorem eight_limits_hull {n : ℕ} {c : Site n→Point} (ci : Function.Injective c)
    (hull : HullOrder c) {θ : ℝ} (pos : 0≤θ) (strict : θ<4*π/5) (mac : Macro c θ)
    {m : Site n→ℕ} (R : ∀i,Row (m i)) (front : Represents R c)
    (i : Site n) (eight : 8≤mass R θ i) : n+3≤6 := by
  have below : θ<π:=by linarith [pi_pos]
  have top : π<((2:ℝ)+3)*(π-θ):=by linarith
  have high : 3≤score R i (π-θ):=(Nat.pow_le_pow_iff_right (by decide : 1<2)).mp eight
  have cap:=saturated_turn_budget ci hull pos below mac R front top ({i}:Finset (Site n))
    (fun a h=>by simpa only [mem_singleton.mp h] using high)
  simp only [card_singleton,Nat.cast_one,mul_one] at cap
  by_contra! many
  have nat : 4≤n:=by omega
  have real : (4:ℝ)≤n:=by exact_mod_cast nat
  have mul:=mul_le_mul_of_nonneg_right real (sub_pos.mpr below).le
  norm_num at cap top
  nlinarith only [cap,top,mul]

end R90.ConvexArc
#print axioms R90.ConvexArc.saturated_turn
#print axioms R90.ConvexArc.saturated_turn_budget
#print axioms R90.ConvexArc.eight_limits_hull
