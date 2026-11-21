import ConvexCritical

noncomputable section
namespace R90.ConvexArc
open JSP404 Real Finset R86.ConvexMass R55.WeightedCollision

local macro "cycle_arith" : tactic => `(tactic| (simp only [ne_eq, Fin.ext_iff, Fin.lt_def] at * <;> omega))

/-- The open counterclockwise boundary arc, including arcs across label zero. -/
def arc {n : ℕ} (p q : Site n) : Finset (Site n) := by
  classical
  exact univ.filter (fun i=>Cyclic p i q)

@[simp] theorem mem_arc {n : ℕ} (p q i : Site n) : i∈arc p q ↔ Cyclic p i q := by
  classical
  simp [arc]

private theorem split_angle {n : ℕ} {c : Site n→Point} (ci : Function.Injective c)
    (hull : HullOrder c) {i j k l : Site n} (s : Cyclic i j k) (t : Cyclic i k l)
    (u : Cyclic i j l) :
    EuclideanGeometry.angle (c j) (c i) (c l)=EuclideanGeometry.angle (c j) (c i) (c k)+
      EuclideanGeometry.angle (c k) (c i) (c l) := by
  have ki : k≠i:=by unfold Cyclic at s;cycle_arith
  exact arc_split (sub_ne_zero.mpr (ci.ne ki)) (hull _ _ _ s) (hull _ _ _ t) (hull _ _ _ u)

/-- For four cyclically ordered centers p,j,k,q, one endpoint sees at
least one defect between its chord into the arc and its chord to the other endpoint. -/
theorem quad_base {n : ℕ} {c : Site n→Point} (ci : Function.Injective c)
    (hull : HullOrder c) {θ : ℝ} (mac : Macro c θ) {p j k q : Site n}
    (left : Cyclic p j k) (right : Cyclic p k q) :
    π-θ≤EuclideanGeometry.angle (c j) (c p) (c q) ∨ π-θ≤EuclideanGeometry.angle (c p) (c q) (c k) := by
  have lp := left
  have rp := right
  unfold Cyclic at lp rp
  have a:=split_angle ci hull left right (by unfold Cyclic;cycle_arith)
  have b:=split_angle ci hull (i:=k) (j:=q) (k:=p) (l:=j)
    (by unfold Cyclic;cycle_arith) (by unfold Cyclic;cycle_arith) (by unfold Cyclic;cycle_arith)
  have s:=EuclideanGeometry.angle_add_angle_add_angle_eq_pi (c k) (ci.ne (show p≠j by cycle_arith))
  have t:=EuclideanGeometry.angle_add_angle_add_angle_eq_pi (c q) (ci.ne (show p≠k by cycle_arith))
  change EuclideanGeometry.angle (c j) (c p) (c k)+EuclideanGeometry.angle (c p) (c k) (c j)+
      EuclideanGeometry.angle (c k) (c j) (c p)=π at s
  change EuclideanGeometry.angle (c k) (c p) (c q)+EuclideanGeometry.angle (c p) (c q) (c k)+
      EuclideanGeometry.angle (c q) (c k) (c p)=π at t
  have capj:=mac k j p (by cycle_arith) (by cycle_arith) (by cycle_arith)
  have capk:=mac q k j (by cycle_arith) (by cycle_arith) (by cycle_arith)
  by_contra! bad
  linarith only [s,t,a,b,capj,capk,bad.1,bad.2]

/-- One entire δ-neighborhood of a real chord, seen from one of the
two arc endpoints, contains only sites on the open arc. -/
theorem chord_neighborhood {n : ℕ} {c : Site n→Point} (ci : Function.Injective c)
    (hull : HullOrder c) {θ : ℝ} (mac : Macro c θ) {p j k q : Site n}
    (l : Cyclic p j k) (r : Cyclic p k q) :
    nearChord c (π-θ) p j⊆arc p q ∨ nearChord c (π-θ) q k⊆arc p q := by
  obtain left|right:=quad_base ci hull mac l r
  · left
    unfold Cyclic at l r
    intro a h
    obtain ⟨ap,close⟩:=(mem_filter.mp h).2
    rw [mem_arc]
    by_contra outside
    unfold Cyclic at outside
    by_cases eq:a=q
    · subst a;exact close.not_ge left
    have sh:=split_angle ci hull (i:=p) (j:=j) (k:=q) (l:=a)
      (by unfold Cyclic;cycle_arith) (by unfold Cyclic;cycle_arith) (by unfold Cyclic;cycle_arith)
    linarith only [left,close,sh,EuclideanGeometry.angle_nonneg (c q) (c p) (c a)]
  · right
    unfold Cyclic at l r
    intro a h
    obtain ⟨aq,close⟩:=(mem_filter.mp h).2
    rw [mem_arc]
    by_contra outside
    unfold Cyclic at outside
    rw [EuclideanGeometry.angle_comm (c k) (c q) (c a)] at close
    by_cases eq:a=p
    · subst a;exact close.not_ge right
    have sh:=split_angle ci hull (i:=q) (j:=a) (k:=p) (l:=k)
      (by unfold Cyclic;cycle_arith) (by unfold Cyclic;cycle_arith) (by unfold Cyclic;cycle_arith)
    linarith only [right,close,sh,EuclideanGeometry.angle_nonneg (c a) (c q) (c p)]

theorem arc_pair {n : ℕ} {p q : Site n} (two : 2≤(arc p q).card) :
    ∃j k,Cyclic p j k ∧ Cyclic p k q := by
  obtain ⟨j,hj,k,hk,ne⟩:=Finset.one_lt_card.mp (show 1<(arc p q).card by omega)
  have s:=(mem_arc ..).mp hj
  have t:=(mem_arc ..).mp hk
  unfold Cyclic at *
  by_cases jk : (p<j ∧ j<k) ∨ (j<k ∧ k<p) ∨ (k<p ∧ p<j)
  · exact ⟨j,k,jk,t⟩
  · exact ⟨k,j,by cycle_arith,s⟩

end R90.ConvexArc
#print axioms R90.ConvexArc.quad_base
#print axioms R90.ConvexArc.chord_neighborhood
