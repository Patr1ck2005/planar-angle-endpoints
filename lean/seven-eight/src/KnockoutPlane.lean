import Knockout

noncomputable section
open scoped Classical
namespace R58.Knockout
open JSP404 Real EuclideanGeometry

/-- If the angle at v is less than half the defect, the opposite side is
strictly shorter than either incident side. -/
theorem short_side {v a b : Point} {l : ℝ} (lp : 0<l) (va : v≠a) (vb : v≠b) (ab : a≠b)
    (lawA : EuclideanGeometry.angle b a v≤π-l)
    (lawB : EuclideanGeometry.angle a b v≤π-l)
    (narrow : EuclideanGeometry.angle a v b<l/2) : dist a b<dist v a := by
  have sum:=angle_add_angle_add_angle_eq_pi b va
  rw [angle_comm v b a] at sum
  have cmp : EuclideanGeometry.angle a v b<EuclideanGeometry.angle a b v := by
    linarith
  have nc : ¬Collinear ℝ ({a,b,v} : Set Point) := by
    rw [collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi]
    rintro (e|e|e|e)
    · exact ab e
    · exact vb e
    · linarith [EuclideanGeometry.angle_nonneg a v b]
    · linarith
  simpa only [dist_comm a v] using (angle_lt_iff_dist_lt nc).mp cmp

/-- Weighted dyadic capacity in the ordinary plane for arbitrary
per-vertex narrow color classes. -/
theorem planar_capacity {C : Type*} [DecidableEq C] (S : Finset Point) (c : Point→Point→C)
    (n : ℕ) (w : Point→ℕ) {l : ℝ} (lp : 0<l) (legal : maxAngle S≤π-l)
    (width : ∀ v∈S,∀a∈S,∀b∈S,v≠a → v≠b → a≠b → c v a=c v b → EuclideanGeometry.angle a v b<l/2)
    (room : ∀v∈S,w v+(colors S c v).card≤n) : (∑ v∈S,2^w v)≤2^n := by
  apply capacity S c _ n w room
  intro v hv a ha b hb va vb ab eq
  apply short_side lp va vb ab
  · exact (angle_le_maxAngle hb ha hv ab.symm vb.symm va.symm).trans legal
  · exact (angle_le_maxAngle ha hb hv ab va.symm vb.symm).trans legal
  · exact width v hv a ha b hb va vb ab eq

/-- Every nearest representative sees the query with half-defect clearance
from every other representative direction. -/
theorem nearest_sees {S : Finset Point} {x v u : Point} {l : ℝ} (lp : 0<l) (law : maxAngle S≤π-l)
    (hx : x∈S) (hv : v∈S) (hu : u∈S) (vx : v≠x) (ux : u≠x) (vu : v≠u)
    (near : dist x v≤dist x u) : l/2≤EuclideanGeometry.angle x v u := by
  by_contra! narrow
  have less:=short_side lp vx vu ux.symm
    ((angle_le_maxAngle hu hx hv ux vu.symm vx.symm).trans law)
    ((angle_le_maxAngle hx hu hv ux.symm vx.symm vu.symm).trans law) narrow
  rw [dist_comm v x] at less
  linarith

end R58.Knockout
#print axioms R58.Knockout.planar_capacity
#print axioms R58.Knockout.nearest_sees
