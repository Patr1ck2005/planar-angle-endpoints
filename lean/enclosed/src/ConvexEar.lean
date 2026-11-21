import ChordMass
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality

noncomputable section
namespace R86.ConvexMass
open scoped NNReal
open Real JSP404 R54.GapTest R55.WeightedCollision R56.Windows Finset R65.Retention R85.CriticalMass InnerProductGeometry

abbrev Site (n : ℕ) := Fin (n+3)
def prev {n : ℕ} (i : Site n) : Site n := if h:0 < i.val then ⟨i.val-1,by omega⟩ else ⟨n+2,by omega⟩
def next {n : ℕ} (i : Site n) : Site n := if h:i.val+1 < n+3 then ⟨i.val+1,h⟩ else 0

def Cyclic {n : ℕ} (i j k : Site n) := (i < j ∧ j < k) ∨ (j < k ∧ k < i) ∨ (k < i ∧ i < j)
def det (u v : Point) := u 0*v 1-u 1*v 0
/-- The standard counterclockwise orientation criterion for labeled points in
strictly convex position in their boundary order. -/
def HullOrder {n : ℕ} (c : Site n→Point) : Prop :=
  ∀i j k,Cyclic i j k → 0 < det (c j-c i) (c k-c i)

def exterior {n : ℕ} (c : Site n→Point) (i : Site n) :=
  π-EuclideanGeometry.angle (c (prev i)) (c i) (c (next i))

theorem arc_split {u w v : Point} (wn : w≠0) (uw : 0 < det u w)
    (wv : 0 < det w v) (uv : 0 < det u v) : angle u v=angle u w+angle w v := by
  apply angle_eq_angle_add_add_angle_add_of_mem_span wn
  rw [Submodule.mem_span_pair]
  let a : ℝ≥0:=⟨det w v/det u v,div_nonneg wv.le uv.le⟩
  let b : ℝ≥0:=⟨det u w/det u v,div_nonneg uw.le uv.le⟩
  refine ⟨a,b,?_⟩
  change (det w v/det u v) • u+(det u w/det u v) • v=w
  ext k
  fin_cases k
  · change (det w v/det u v)*(u 0)+(det u w/det u v)*(v 0)=w 0
    field_simp [ne_of_gt uv];unfold det;ring
  · change (det w v/det u v)*(u 1)+(det u w/det u v)*(v 1)=w 1
    field_simp [ne_of_gt uv];unfold det;ring

theorem primary {n : ℕ} (j : Site n) :
    prev j≠j ∧ next j≠j ∧ prev j≠next j ∧ Cyclic (prev j) j (next j) ∧ Cyclic (next j) (prev j) j := by
  unfold Cyclic prev next
  split_ifs <;> simp only [ne_eq,Fin.ext_iff,Fin.lt_def,Fin.val_zero] <;> omega

private theorem remaining {n : ℕ} {j a : Site n} (aj : a≠j) (ap : a≠prev j) (an : a≠next j) :
    Cyclic (prev j) (next j) a ∧ Cyclic (prev j) j a ∧
    Cyclic (next j) a (prev j) ∧ Cyclic (next j) a j := by
  unfold Cyclic prev next at *
  split_ifs at * <;> simp only [ne_eq,Fin.ext_iff,Fin.lt_def,Fin.val_zero] at * <;> omega

/-- A close peer on the convex side of an edge forces its immediate ear base
angle to be small. The input uses only determinant signs of actual positions. -/
theorem ear_two_peers {n : ℕ} {c : Site n→Point} (ci : Function.Injective c) (hull : HullOrder c)
    (θ : ℝ) (j : Site n)
    (leftPeer : ∃a,a≠prev j ∧ a≠j ∧ EuclideanGeometry.angle (c j) (c (prev j)) (c a) < π-θ)
    (rightPeer : ∃a,a≠next j ∧ a≠j ∧ EuclideanGeometry.angle (c j) (c (next j)) (c a) < π-θ) :
    exterior c j < 2*(π-θ) := by
  obtain ⟨pj,kj,pk,ord,ord'⟩:=primary j
  have left : EuclideanGeometry.angle (c j) (c (prev j)) (c (next j)) < π-θ := by
    obtain ⟨a,ap,aj,small⟩:=leftPeer
    by_cases eq:a=next j
    · simpa only [eq] using small
    obtain ⟨pka,pja,_,_⟩:=remaining aj ap eq
    have add:=arc_split (sub_ne_zero.mpr (ci.ne pk.symm)) (hull _ _ _ ord) (hull _ _ _ pka) (hull _ _ _ pja)
    change angle (c j-c (prev j)) (c a-c (prev j)) < _ at small
    change angle (c j-c (prev j)) (c (next j)-c (prev j)) < _
    linarith [angle_nonneg (c (next j)-c (prev j)) (c a-c (prev j))]
  have right : EuclideanGeometry.angle (c (prev j)) (c (next j)) (c j) < π-θ := by
    obtain ⟨a,ak,aj,small⟩:=rightPeer
    by_cases eq:a=prev j
    · simpa only [eq,EuclideanGeometry.angle_comm (c j) (c (next j)) (c (prev j))] using small
    obtain ⟨_,_,kap,kaj⟩:=remaining aj eq ak
    have add:=arc_split (sub_ne_zero.mpr (ci.ne pk)) (hull _ _ _ kap) (hull _ _ _ ord') (hull _ _ _ kaj)
    rw [EuclideanGeometry.angle_comm] at small
    change angle (c a-c (next j)) (c j-c (next j)) < _ at small
    change angle (c (prev j)-c (next j)) (c j-c (next j)) < _
    linarith [angle_nonneg (c a-c (next j)) (c (prev j)-c (next j))]
  have sum:=EuclideanGeometry.angle_add_angle_add_angle_eq_pi (c (next j)) (ci.ne pj)
  unfold exterior
  rw [EuclideanGeometry.angle_comm (c (next j)) (c j) (c (prev j))] at sum
  linarith

theorem ear_turn {n B v : ℕ} {c : Site n→Point} (ci : Function.Injective c) (hull : HullOrder c)
    {θ : ℝ} (pos : 0≤θ) (below : θ < π) (mac : Macro c θ) {p : Site n→ℕ}
    (R : ∀i,Row (p i)) (front : Represents R c) (back : Witnessed R c)
    (full : capacity R θ=B+v) (crit : Critical c (B+1) θ) (j : Site n)
    (leftMass : mass R θ j < v+mass R θ (prev j)) (rightMass : mass R θ j < v+mass R θ (next j)) :
    exterior c j < 2*(π-θ) := by
  exact ear_two_peers ci hull θ j
    (close_peer (by omega) ci pos below mac R front back full crit (primary j).1 leftMass)
    (close_peer (by omega) ci pos below mac R front back full crit (primary j).2.1 rightMass)

end R86.ConvexMass
#print axioms R86.ConvexMass.ear_turn
