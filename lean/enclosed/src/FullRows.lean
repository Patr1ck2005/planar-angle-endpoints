import KnockoutPlane
import WindowAxes

noncomputable section
open scoped Classical
namespace R58.FullRows
open JSP404 R56.Windows Real InnerProductGeometry Finset

variable {m : ℕ} (R : Row m) (l : ℝ)

def cell (j : ℕ) := ⌊(R.w (j+1)-R.w j)/l⌋₊
def cellSum (j : ℕ) := ∑ i∈Finset.range j,cell R l i
def remainder (j : ℕ) := R.w j-(cellSum R l j:ℝ)*l
def long := Finset.univ.filter (fun j : Fin m=>0<cell R l j)

theorem remainder_order (lp : 0<l) {i j : ℕ} (ij : i≤j) (jm : j≤m) :
    remainder R l i≤remainder R l j := by
  induction j with
  | zero =>
    have eq : i=0 := by omega
    rw [eq]
  | succ j ih =>
    by_cases eq : i=j+1
    · rw [eq]
    have ord:=R.ordered (a:=j) (b:=j+1) (by omega) jm
    have fl : (cell R l j:ℝ)≤(R.w (j+1)-R.w j)/l :=
      Nat.floor_le (div_nonneg (sub_nonneg.mpr ord) lp.le)
    have h:=(le_div_iff₀ lp).mp fl
    apply (ih (by omega) (by omega)).trans
    simp only [remainder,cellSum,Finset.sum_range_succ,Nat.cast_add,add_mul]
    linarith

theorem digits_plus_long : (∑ j : Fin m,R.digits j l)+(long R l).card=cellSum R l m := by
  rw [show cellSum R l m=∑ j : Fin m,cell R l j from (Fin.sum_univ_eq_sum_range (cell R l) m).symm]
  have each (j : Fin m) : cell R l j=R.digits j l+if 0<cell R l j then 1 else 0 := by
    change cell R l j=cell R l j-1+_
    split_ifs <;> omega
  calc
    _=(∑ j : Fin m,R.digits j l)+(∑ j : Fin m,if 0<cell R l j then 1 else 0) := by simp [long]
    _=_ := by rw [←Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun j _=>(each j).symm)

/-- The chart begins immediately after a long gap. Map every wall to its
next long gap, with real bearing error controlled by total rounding slack. -/
theorem color_walls (lp : 0<l) (last : 0<cell R l (m-1)) {n : ℕ}
    (full : cellSum R l m=n) (low : π-(n:ℝ)*l<l/2) :
    ∃ tag : Fin m→ℕ, (∀ j,tag j<m ∧ 0<cell R l (tag j)) ∧
      ∀ i j,tag i=tag j → |R.w i-R.w j|<l/2 := by
  classical
  have ex (i : Fin m) : ∃ j : ℕ, i.val≤j ∧ j<m ∧ 0<cell R l j :=
    ⟨m-1,by have h:=i.isLt;omega,by have h:=i.isLt;omega,last⟩
  let tag (i : Fin m) := Nat.find (ex i)
  have spec (i : Fin m) : i.val≤tag i ∧ tag i<m ∧ 0<cell R l (tag i) := Nat.find_spec (ex i)
  have fixed (i : Fin m) {j : ℕ} (lo : i.val≤j) (hi : j≤tag i) : cellSum R l j=cellSum R l i := by
    induction j with
    | zero =>
      have eq : i.val=0 := by omega
      rw [eq]
    | succ j ih =>
      by_cases eq : i.val=j+1
      · rw [eq]
      have no : cell R l j=0 := by
        by_contra! h
        have small : tag i≤j := Nat.find_min' (ex i) ⟨by omega,by have h:=(spec i).2.1;omega,by omega⟩
        omega
      simp only [cellSum,Finset.sum_range_succ,no,add_zero]
      exact ih (by omega) (by omega)
  refine ⟨tag,fun j=>(spec j).2,?_⟩
  intro i j eq
  have same : cellSum R l i=cellSum R l j :=
    (fixed i (spec i).1 (le_refl _)).symm.trans ((congrArg (cellSum R l) eq).trans (fixed j (spec j).1 (le_refl _)))
  have bounds (a : Fin m) : R.w 0≤remainder R l a ∧ remainder R l a≤R.w 0+π-(n:ℝ)*l := by
    have lo:=remainder_order R l lp (Nat.zero_le a.val) a.isLt.le
    have up:=remainder_order R l lp a.isLt.le le_rfl
    change _≤R.w m-(cellSum R l m:ℝ)*l at up
    rw [full,R.period] at up
    exact ⟨by simpa [remainder,cellSum] using lo,up⟩
  obtain ⟨ai,bi⟩:=bounds i
  obtain ⟨aj,bj⟩:=bounds j
  unfold remainder at ai bi aj bj
  rw [same] at ai bi
  exact abs_lt.mpr ⟨by linarith,by linarith⟩

theorem true_angle {x y : ℝ} {r s l : ℝ} (rn : r≠0) (sn : s≠0)
    (lp : 0<l) (upper : l≤π) (close : |x-y|<l/2)
    (legal : angle (r • circleDirection x) (s • circleDirection y)≤π-l) :
    angle (r • circleDirection x) (s • circleDirection y)<l/2 := by
  have a : angle (circleDirection x) (circleDirection y)=|x-y| := by
    rw [angle_circleDirection,←Real.cos_abs (x-y),Real.arccos_cos (abs_nonneg _) (by linarith)]
  rcases lt_or_gt_of_ne rn with hr|hr <;> rcases lt_or_gt_of_ne sn with hs|hs <;>
    simp only [angle_smul_left_of_neg,angle_smul_left_of_pos,angle_smul_right_of_neg,
      angle_smul_right_of_pos,hr,hs,angle_neg_left,angle_neg_right,a] at legal ⊢ <;> linarith

/-- Ordinary full projective row potential when the integer cell sums saturate
the available n cells in the low strip. -/
theorem capacity (S : Finset Point) (m : Point→ℕ) (R : ∀ v,Row (m v))
    {l : ℝ} (lp : 0<l) (upper : l≤π) (legal : maxAngle S≤π-l) {n : ℕ} (low : π-(n:ℝ)*l<l/2)
    (last : ∀ v∈S,0<cell (R v) l (m v-1)) (full : ∀ v∈S,cellSum (R v) l (m v)=n)
    (rep : ∀ v∈S,∀ u∈S,v≠u → ∃ j : Fin (m v),∃ r : ℝ,r≠0 ∧ u-v=r • circleDirection ((R v).w j)) :
    (∑ v∈S,2^(∑ j : Fin (m v),(R v).digits j l))≤2^n := by
  classical
  have row (v : Point) (hv : v∈S) := color_walls (R v) l lp (last v hv) (full v hv) low
  choose tag ok small using row
  let present (v u : Point) := v∈S ∧ u∈S ∧ v≠u
  let wall (v u : Point) (h : present v u) := (rep v h.1 u h.2.1 h.2.2).choose
  let c (v u : Point) := if h : present v u then tag v h.1 (wall v u h) else 0
  apply R58.Knockout.planar_capacity S c n (fun v=>∑ j : Fin (m v),(R v).digits j l) lp legal
  · intro v hv a ha b hb va vb ab eq
    have pa : present v a:=⟨hv,ha,va⟩
    have pb : present v b:=⟨hv,hb,vb⟩
    simp only [c,dite_eq_left pa,dite_eq_left pb] at eq
    have close:=small v hv _ _ eq
    obtain ⟨r,rn,ea⟩:=(rep v hv a ha va).choose_spec
    obtain ⟨s,sn,eb⟩:=(rep v hv b hb vb).choose_spec
    have law:=(angle_le_maxAngle ha hv hb va.symm ab vb).trans legal
    change angle (a-v) (b-v)≤_ at law
    change angle (a-v) (b-v)<_
    rw [ea,eb] at law ⊢
    exact true_angle rn sn lp upper close law
  · intro v hv
    have sub : R58.Knockout.colors S c v⊆(long (R v) l).image Fin.val := by
      intro x hx
      obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp hx
      obtain ⟨ne,us⟩:=Finset.mem_erase.mp hu
      have h : present v u:=⟨hv,us,ne.symm⟩
      simp only [c,dite_eq_left h]
      let t:=tag v hv (wall v u h)
      have htag:=ok v hv (wall v u h)
      exact Finset.mem_image.mpr ⟨⟨t,htag.1⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,htag.2⟩,rfl⟩
    have bound:=(Finset.card_le_card sub).trans Finset.card_image_le
    have sum:=digits_plus_long (R v) l
    rw [full v hv] at sum
    omega

end R58.FullRows
#print axioms R58.FullRows.color_walls
#print axioms R58.FullRows.capacity
