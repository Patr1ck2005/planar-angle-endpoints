import ConvexArcGeometry

noncomputable section
namespace R90.ConvexArc
open JSP404 Real Finset R86.ConvexMass R55.WeightedCollision R65.Retention R54.GapTest R56.Windows R85.CriticalMass

/-- Every boundary arc containing at least two sites pays for the cheaper
endpoint and the full endpoint surplus. -/
theorem arc_mass {n B v : ℕ} {c : Site n→Point} (ci : Function.Injective c)
    (hull : HullOrder c) {θ : ℝ} (pos : 0≤θ) (below : θ<π) (mac : Macro c θ)
    {m : Site n→ℕ} (R : ∀i,Row (m i)) (front : Represents R c) (back : Witnessed R c)
    (full : capacity R θ=B+v) (crit : Critical c (B+1) θ)
    {p q : Site n} (two : 2≤(arc p q).card) :
    v+min (mass R θ p) (mass R θ q)≤∑a∈arc p q,mass R θ a := by
  obtain ⟨j,k,l,r⟩:=arc_pair two
  have L:=l
  have K:=r
  unfold Cyclic at L K
  have pj : p≠j:=by simp only [ne_eq,Fin.ext_iff,Fin.lt_def] at *;omega
  have qk : q≠k:=by simp only [ne_eq,Fin.ext_iff,Fin.lt_def] at *;omega
  obtain a|b:=chord_neighborhood ci hull mac l r
  · exact (Nat.add_le_add_left (min_le_left ..) v).trans
      ((near_charge (by omega) ci pos below mac R front back full crit pj).trans
        (sum_le_sum_of_subset_of_nonneg a (fun _ _ _=>Nat.zero_le _)))
  · exact (Nat.add_le_add_left (min_le_right ..) v).trans
      ((near_charge (by omega) ci pos below mac R front back full crit qk).trans
        (sum_le_sum_of_subset_of_nonneg b (fun _ _ _=>Nat.zero_le _)))

private theorem mass_split {n : ℕ} (A : Site n→ℕ) {p q : Site n} (pq : p≠q) :
    A p+A q+(∑i∈arc p q,A i)+(∑i∈arc q p,A i)=∑i,A i := by
  classical
  have part : {p,q} ∪ (arc p q∪arc q p)=(univ : Finset (Site n)) := by
    ext z
    simp only [mem_union,mem_insert,mem_singleton,mem_arc,mem_univ,iff_true,Cyclic]
    simp only [ne_eq,Fin.ext_iff,Fin.lt_def] at *;omega
  have dis : Disjoint (arc p q) (arc q p) := by
    apply disjoint_left.mpr
    intro i a b
    simp only [mem_arc,Cyclic,Fin.lt_def] at a b;omega
  have dis2 : Disjoint ({p,q} : Finset (Site n)) (arc p q∪arc q p) := by
    apply disjoint_left.mpr
    intro i a b
    simp only [mem_insert,mem_singleton,mem_union,mem_arc,Cyclic,Fin.ext_iff,Fin.lt_def] at a b
    omega
  rw [←part,sum_union dis2,sum_union dis,sum_insert (by simpa using pq),sum_singleton]
  omega

/-- At any critical total B+1, independent of endpoint divisibility or
minimum-mass assumptions, two separated heavy sites force strict slack below B. -/
theorem separated_heavies {n B : ℕ} {c : Site n→Point} (ci : Function.Injective c)
    (hull : HullOrder c) {θ : ℝ} (pos : 0≤θ) (below : θ<π) (mac : Macro c θ)
    {m : Site n→ℕ} (R : ∀i,Row (m i)) (front : Represents R c) (back : Witnessed R c)
    (room : B+1≤capacity R θ) (crit : Critical c (B+1) θ)
    {p q : Site n} (pq : p≠q) (left : 2≤(arc p q).card) (right : 2≤(arc q p).card) :
    mass R θ p+mass R θ q+2*min (mass R θ p) (mass R θ q)<B := by
  let v:=capacity R θ-B
  have full : capacity R θ=B+v:=by dsimp [v];omega
  have a:=arc_mass ci hull pos below mac R front back full crit left
  have b:=arc_mass ci hull pos below mac R front back full crit right
  rw [min_comm] at b
  have sum:=mass_split (mass R θ) pq
  change _=capacity R θ at sum
  omega

/-- A two-vertex low patch bracketed by endpoints at least as heavy as
both patch sites together is impossible, at any actual target total. -/
theorem no_light_pair {n B : ℕ} {c : Site n→Point} (ci : Function.Injective c)
    (hull : HullOrder c) {θ : ℝ} (pos : 0≤θ) (below : θ<π) (mac : Macro c θ)
    {m : Site n→ℕ} (R : ∀i,Row (m i)) (front : Represents R c) (back : Witnessed R c)
    (room : B+1≤capacity R θ) (crit : Critical c (B+1) θ)
    {p q j k : Site n} (jk : j≠k) (pair : arc p q={j,k}) :
    min (mass R θ p) (mass R θ q)<mass R θ j+mass R θ k := by
  have two : 2≤(arc p q).card:=by rw [pair];simp [jk]
  let v:=capacity R θ-B
  have full : capacity R θ=B+v:=by dsimp [v];omega
  have cap:=arc_mass ci hull pos below mac R front back full crit two
  rw [pair,sum_insert (by simpa using jk),sum_singleton] at cap
  omega

end R90.ConvexArc
#print axioms R90.ConvexArc.arc_mass
#print axioms R90.ConvexArc.no_light_pair
#print axioms R90.ConvexArc.separated_heavies
