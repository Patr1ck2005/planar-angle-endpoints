import SaturatedHull

noncomputable section
namespace R90.ConvexArc
open JSP404 Real Finset R86.ConvexMass R55.WeightedCollision R65.Retention R54.GapTest R56.Windows R85.CriticalMass

/-- At B=16 two rows of capacity at least four must lie at cyclic distance
at most two (one open arc contains at most one site). -/
theorem seventeen_four_pair {n : ℕ} {c : Site n→Point} (ci : Function.Injective c)
    (hull : HullOrder c) {θ : ℝ} (pos : 0≤θ) (below : θ<π) (mac : Macro c θ)
    {m : Site n→ℕ} (R : ∀i,Row (m i)) (front : Represents R c) (back : Witnessed R c)
    (room : 17≤capacity R θ) (crit : Critical c 17 θ) {p q : Site n} (pq : p≠q)
    (P : 4≤mass R θ p) (Q : 4≤mass R θ q) :
    (arc p q).card≤1 ∨ (arc q p).card≤1 := by
  by_contra! h
  have bad:=separated_heavies (B:=16) ci hull pos below mac R front back room crit pq h.1 h.2
  omega

/-- At B=20 a capacity-eight site and any other site of capacity at least
four must lie at cyclic distance at most two in a critical convex hull. -/
theorem twenty_one_eight_four {n : ℕ} {c : Site n→Point} (ci : Function.Injective c)
    (hull : HullOrder c) {θ : ℝ} (pos : 0≤θ) (below : θ<π) (mac : Macro c θ)
    {m : Site n→ℕ} (R : ∀i,Row (m i)) (front : Represents R c) (back : Witnessed R c)
    (room : 21≤capacity R θ) (crit : Critical c 21 θ) {p q : Site n} (pq : p≠q)
    (P : 8≤mass R θ p) (Q : 4≤mass R θ q) :
    (arc p q).card≤1 ∨ (arc q p).card≤1 := by
  by_contra! h
  have bad:=separated_heavies (B:=20) ci hull pos below mac R front back room crit pq h.1 h.2
  omega

/-- Every legal strict convex hull of at least seven sites supporting 21
in the open sub-4π/5 region has 7, 8 or 9 sites, all capacities at most
four, and respectively at least four, three or two rows of capacity four. -/
theorem twenty_one_large_hull {n : ℕ} {c : Site n→Point} (ci : Function.Injective c)
    (hull : HullOrder c) {θ : ℝ} (pos : 0≤θ) (strict : θ<4*π/5) (mac : Macro c θ)
    {m : Site n→ℕ} (R : ∀i,Row (m i)) (front : Represents R c)
    (room : 21≤capacity R θ) (many : 7≤n+3) :
    n+3≤9 ∧ (∀i,mass R θ i≤4) ∧
      11≤n+3+(univ.filter (fun i=>mass R θ i=4)).card := by
  classical
  have below : θ<π:=by linarith [pi_pos]
  have top : π<((2:ℝ)+3)*(π-θ):=by linarith
  have turns:=saturated_turn_budget ci hull pos below mac R front top (∅ : Finset (Site n)) (by simp)
  simp only [card_empty,Nat.cast_zero,mul_zero,add_zero] at turns
  have count : n+3≤9:=by
    by_contra! high
    have hn : (7:ℝ)≤n:=by exact_mod_cast (show 7≤n by omega)
    nlinarith only [top,turns,mul_le_mul_of_nonneg_right hn (sub_pos.mpr below).le]
  have small (i) : mass R θ i≤4:=by
    have no : mass R θ i<8 := by
      by_contra! big
      have cut:=eight_limits_hull ci hull pos strict mac R front i big
      omega
    have rank : score R i (π-θ)<3:=(Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp no
    exact Nat.pow_le_pow_right (by decide : 0<2) (show score R i (π-θ)≤2 by omega)
  have entry (i) : mass R θ i≤2+(if mass R θ i=4 then 2 else 0) := by
    split
    · omega
    · rename_i ne
      have lt : mass R θ i<4:=lt_of_le_of_ne (small i) ne
      have ss : score R i (π-θ)<2:=(Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp lt
      exact Nat.pow_le_pow_right (by decide : 0<2) (show score R i (π-θ)≤1 by omega)
  have total:=sum_le_sum (s:=univ) (fun i _=>entry i)
  have flags : (∑i : Site n,if mass R θ i=4 then 2 else 0)=
      (univ.filter (fun i=>mass R θ i=4)).card*2 := by rw [←sum_filter];simp
  rw [sum_add_distrib,flags,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at total
  simp only [Nat.cast_id] at total
  change 21≤∑i,mass R θ i at room
  exact ⟨count,small,by omega⟩

end R90.ConvexArc
#print axioms R90.ConvexArc.seventeen_four_pair
#print axioms R90.ConvexArc.twenty_one_eight_four
#print axioms R90.ConvexArc.twenty_one_large_hull
