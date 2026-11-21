import FiveDyadicBoundary
import ClusterContraction
noncomputable section
namespace R66.Five
open Real JSP404 R54.GapTest R55.WeightedCollision R56.Windows Finset
open InnerProductGeometry R51.Anchored

theorem long_gap {h k : ℕ} (R : Row h) {l : ℝ} (lp : 0<l)
    (period : π<((k:ℝ)+3)*l) (sat : k+1≤∑j,R.digits j l) :
    ∃j : Fin h, ((k:ℝ)+2)*l≤R.w (j.val+1)-R.w j := by
  classical
  let g (j : Fin h):=R.w (j.val+1)-R.w j
  let b (j : Fin h):=⌊g j/l⌋₊
  let H:=univ.filter (fun j=>0<b j)
  have sumg : (∑j,g j)=π := by
    calc _=∑j∈range h,(R.w (j+1)-R.w j) := Fin.sum_univ_eq_sum_range _ _
         _=R.w h-R.w 0 := Finset.sum_range_sub ..
         _=_ := by rw [R.period];ring
  have floors (j) : (b j:ℝ)*l≤g j := (le_div_iff₀ lp).mp
    (Nat.floor_le (div_nonneg (sub_nonneg.mpr (R.ordered (Nat.le_succ _) j.isLt)) lp.le))
  have sumfloors:=sum_le_sum (s:=univ) (fun j _=>floors j)
  rw [←sum_mul,←Nat.cast_sum,sumg] at sumfloors
  have cap : (∑j,b j)≤k+2 := by
    by_contra! big
    have n : k+3≤∑j,b j := by omega
    have rr : (k:ℝ)+3≤(∑j,b j : ℕ) := by exact_mod_cast n
    nlinarith only [mul_le_mul_of_nonneg_right rr lp.le,sumfloors,period]
  have count : (∑j,b j)=(∑j,R.digits j l)+H.card := by
    have each (i) : b i=R.digits i l + (if 0<b i then 1 else 0) := by
      change b i=b i-1+_;split <;> omega
    calc (∑i,b i)=∑i,(R.digits i l+(if 0<b i then 1 else 0)) := sum_congr rfl (fun i _=>each i)
         _=_ := by simp [H,sum_add_distrib]
  have one : H.card≤1 := by omega
  have some : ∃j,0<b j := by
    by_contra! none
    have ez : (∑j,b j)=0 := sum_eq_zero (fun i _=>Nat.eq_zero_of_le_zero (none i))
    omega
  obtain ⟨j,jp⟩:=some
  have unique (i) (diff : i≠j) : b i=0 := by
    by_contra! pos
    exact diff ((card_le_one.mp one) i (mem_filter.mpr ⟨mem_univ _,Nat.pos_of_ne_zero pos⟩) j
      (mem_filter.mpr ⟨mem_univ _,jp⟩))
  have allj : (∑i,b i)=b j := sum_eq_single j (fun i _ ne=>unique i ne) (by simp)
  have jh : 1≤H.card := card_pos.mpr ⟨j,mem_filter.mpr ⟨mem_univ _,jp⟩⟩
  have val : k+2≤b j := by omega
  have cast : (k:ℝ)+2≤(b j:ℝ) := by exact_mod_cast val
  exact ⟨j,(mul_le_mul_of_nonneg_right cast lp.le).trans (floors j)⟩

/-- All projective peers in a row lie in the complementary interval of a long gap. -/
theorem complement_interval {I : Type*} {c : I→Point} {m : I→ℕ} (R : ∀i,Row (m i))
    (front : Represents R c) (i : I) (z : Fin (m i)) :
    ∀j,i≠j → ∃t : ℝ,(R i).w (z.val+1)≤t ∧ t≤(R i).w z+π ∧ Bearing (c j-c i) t := by
  intro j ne
  obtain ⟨a,le,ray⟩:=front i j ne
  by_cases left : a≤z.val
  · refine ⟨(R i).w a+π,?_,?_,bearing_closes ray⟩
    have H:=(R i).ordered (Nat.succ_le_of_lt z.isLt) (le_refl _)
    rw [(R i).period] at H
    linarith only [H,(R i).ordered (Nat.zero_le a) le]
    have H:=(R i).ordered left z.isLt.le
    linarith
  · refine ⟨(R i).w a,(R i).ordered (by omega) le,?_,ray⟩
    have H:=(R i).ordered le (le_refl _)
    rw [(R i).period] at H
    linarith only [H,(R i).ordered (Nat.zero_le _) z.isLt.le]

private theorem basic {a b u v : ℝ} (av : a≤u) (ub : u≤b) (aw : a≤v) (vb : v≤b)
    (small : b-a≤π) : angle (circleDirection u) (circleDirection v)=|u-v| := by
  rw [angle_circleDirection,←cos_abs,arccos_cos (abs_nonneg _) (abs_le.mpr ⟨by linarith,by linarith⟩)]

/-- A narrow unsigned interval at a legal apex has one orientation shared by all peers. -/
theorem viewing_cone {I : Type*} [Fintype I] [Nontrivial I] {c : I→Point}
    {θ a b : ℝ} (legal : Macro c θ) (zero : 0≤θ) (width : b-a<π-θ)
    (i : I) (cover : ∀j,i≠j → ∃t : ℝ,a≤t ∧ t≤b ∧ Bearing (c j-c i) t) :
    ∃v : Point,v≠0 ∧ ∀j,i≠j → angle v (c i-c j)≤(b-a)/2 := by
  classical
  let P:={j : I // i≠j}
  obtain ⟨k,ne⟩:=exists_ne i
  let p : P:=⟨k,ne.symm⟩
  choose t lower upper r rp e signs eq using fun j : P=>cover j.val j.property
  let mid:=(a+b)/2
  have amin : a≤mid := by dsimp [mid];linarith [lower p,upper p]
  have mb : mid≤b := by dsimp [mid];linarith [lower p,upper p]
  have equal (j : P) : e j=e p := by
    by_contra diff
    have distinct : j.val≠p.val := by intro same;exact diff (congrArg e (Subtype.ext same))
    have cap:=legal j.val i p.val j.property.symm distinct p.property
    change angle (c j.val-c i) (c p.val-c i)≤θ at cap
    rw [eq j,eq p,angle_smul_left_of_pos _ _ (rp j),angle_smul_right_of_pos _ _ (rp p)] at cap
    have d:=basic (lower j) (upper j) (lower p) (upper p) (by linarith : b-a≤π)
    have ad : |t j-t p|≤b-a := abs_le.mpr ⟨by linarith [lower j,upper p],by linarith [upper j,lower p]⟩
    rcases signs j with a1|a1 <;> rcases signs p with a2|a2 <;>
      simp only [a1,a2,one_smul,neg_one_smul,angle_neg_left,angle_neg_right,d] at cap diff <;> first | exact diff trivial | linarith
  have vec : circleDirection mid≠0 := by
    intro eq0
    have nr:=norm_circleDirection mid
    rw [eq0,norm_zero] at nr
    norm_num at nr
  refine ⟨-(e p • circleDirection mid),neg_ne_zero.mpr (by rcases signs p with t|t <;> simp [t,vec]),?_⟩
  intro j ne
  let q : P:=⟨j,ne⟩
  have h : c i-c j= -(r q • (e q • circleDirection (t q))) := by
    rw [←eq q];simp [q]
  rw [h,angle_neg_left,angle_neg_right,angle_smul_right_of_pos _ _ (rp q),equal q]
  have d:=basic amin mb (lower q) (upper q) (by linarith : b-a≤π)
  have ad : |mid-t q|≤(b-a)/2 := abs_le.mpr ⟨by dsimp [mid];linarith [upper q],by dsimp [mid];linarith [lower q]⟩
  rcases signs p with sg|sg <;> simp only [sg,one_smul,neg_one_smul,angle_neg_left,angle_neg_right,d] <;> linarith

#print axioms long_gap
#print axioms viewing_cone
end R66.Five