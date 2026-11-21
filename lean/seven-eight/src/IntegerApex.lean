import SaturatedCone
import PlanarProfile
import Mathlib.Tactic

noncomputable section
namespace R70.IntegerApex
open Real Finset JSP404 R37.SignedFan InnerProductGeometry R55.WeightedCollision
open R54.GapTest R56.Windows

/-- A general Euclidean angle in a strictly substraight legal tuple is positive. -/
theorem strict_angle {I : Type*} {c : I→Point} (ci : Function.Injective c)
    {θ : ℝ} (lt : θ<π) (mac : Macro c θ) {i j k : I} (ij : i≠j) (ik : i≠k) (jk : j≠k) :
    0<EuclideanGeometry.angle (c i) (c j) (c k) := by
  apply lt_of_le_of_ne (EuclideanGeometry.angle_nonneg _ _ _)
  intro e
  rcases EuclideanGeometry.angle_eq_zero_iff_ne_and_wbtw.mp e.symm with ⟨_,h⟩|⟨_,h⟩
  · have p:=EuclideanGeometry.angle_eq_pi_iff_sbtw.mpr (show Sbtw ℝ (c j) (c i) (c k) from ⟨h,ci.ne ij,ci.ne ik⟩)
    linarith [mac j i k ij.symm jk ik]
  · have p:=EuclideanGeometry.angle_eq_pi_iff_sbtw.mpr (show Sbtw ℝ (c j) (c k) (c i) from ⟨h,ci.ne jk.symm,ci.ne ik.symm⟩)
    linarith [mac j k i jk ij.symm ik.symm]

abbrev Fan := R37.SignedFan.Row
abbrev Peer {I : Type*} (i : I) := {j : I // i≠j}

private def wall (F : Fan) (i : ℕ) : ℝ := if h:i<F.n+1 then F.bearing ⟨i,h⟩ else F.bearing 0+π

def row (F : Fan) : R56.Windows.Row (F.n+1) where
  w:=wall F
  ordered:=by
    intro i j ij hj
    by_cases h : j<F.n+1
    · have hi:=lt_of_le_of_lt ij h
      simpa only [wall,dite_eq_left hi,dite_eq_left h] using F.sorted.monotone (show (⟨i,hi⟩:Fin (F.n+1))≤⟨j,h⟩ from ij)
    · by_cases hi : i<F.n+1
      · simp only [wall,dite_eq_left hi,dite_eq_right h]
        linarith [(F.bounds ⟨i,hi⟩).2,(F.bounds 0).1]
      · simp [wall,h,hi]
  period:=by simp [wall]

theorem gap_pos (F : Fan) (j : Fin (F.n+1)) : 0<(row F).w (j.val+1)-(row F).w j := by
  by_cases h : j.val+1<F.n+1
  · simp only [row,wall,dite_eq_left h,dite_eq_left j.isLt,sub_pos]
    exact F.sorted (show j<⟨j.val+1,h⟩ by exact Nat.lt_succ_self _)
  · simp only [row,wall,dite_eq_right h,dite_eq_left j.isLt,sub_pos]
    linarith [(F.bounds j).2,(F.bounds 0).1]

private theorem project {v : Point} {t r : ℝ} {b : Bool} (hr : 0<r) (e : v=r • oriented t b) : Bearing v t := by
  cases b
  · exact ⟨r,hr,-1,Or.inl rfl,by simpa [oriented] using e⟩
  · exact ⟨r,hr,1,Or.inr rfl,by simpa [oriented] using e⟩

theorem frame {I : Type*} [Fintype I] [DecidableEq I] [Nontrivial I] {c : I→Point} (ci : Function.Injective c)
    {θ : ℝ} (lt : θ<π) (nn : 0≤θ) (mac : Macro c θ) :
    ∃ F : I→Fan, Represents (fun i=>row (F i)) c ∧ Witnessed (fun i=>row (F i)) c ∧
      ∀i,Fintype.card (Peer i)≤(F i).n+1 := by
  classical
  have one (i : I) : ∃ F : Fan,F.Represents (fun j : Peer i=>c j.val-c i) := by
    obtain ⟨j,ne⟩:=exists_ne i
    let _ : Nonempty (Peer i):=⟨⟨j,ne.symm⟩⟩
    obtain ⟨F,h,_⟩:=exists_row (fun j : Peer i=>c j.val-c i) (sub_pos.mpr lt)
      (fun q=>sub_ne_zero.mpr (ci.ne q.2.symm)) (by
        intro a b
        by_cases eq : a=b
        · subst b;simp [angle_self (sub_ne_zero.mpr (ci.ne a.2.symm)),nn]
        · have res:=mac a.val i b.val a.2.symm (fun e=>eq (Subtype.ext e)) b.2
          change angle (c a.val-c i) (c b.val-c i)≤θ at res
          simpa using res)
    exact ⟨F,h⟩
  choose F hf using one
  refine ⟨F,?_,?_,?_⟩
  · intro i j ne
    obtain ⟨k,r,rp,eq⟩:=(hf i).1 ⟨j,ne⟩
    refine ⟨k.val,k.isLt.le,?_⟩
    change Bearing _ _
    simpa only [row,wall,dite_eq_left k.isLt] using project rp eq
  · intro i j hj
    by_cases h : j<(F i).n+1
    · obtain ⟨k,r,rp,eq⟩:=(hf i).2 ⟨j,h⟩
      exact ⟨k.val,k.property,by simpa [row,wall,h] using project rp eq⟩
    · obtain ⟨k,r,rp,eq⟩:=(hf i).2 0
      exact ⟨k.val,k.property,by simpa [row,wall,h] using bearing_closes (project rp eq)⟩
  · intro i
    choose f r rp eq using (hf i).1
    dsimp only at eq
    have inj : Function.Injective f := by
      intro a b e;by_contra ne
      have pos:=strict_angle ci lt mac a.2.symm (fun z=>ne (Subtype.ext z)) b.2
      change 0<angle (c a.val-c i) (c b.val-c i) at pos
      rw [eq a,eq b,e,angle_smul_left_of_pos _ _ (rp a),angle_smul_right_of_pos _ _ (rp b),
        angle_self (by intro z; have h:=norm_circleDirection ((F i).bearing (f b)); cases sg:(F i).sign (f b) <;> simp [oriented,sg] at z <;> rw [z,norm_zero] at h <;> norm_num at h)] at pos
      linarith
    simpa using Fintype.card_le_of_injective f inj

/-- At integral circumference, three genuine positive gaps force one almost-full gap. -/
theorem top_gap {m k : ℕ} (hm : 3≤m) (R : R56.Windows.Row m) {l : ℝ} (lp : 0<l)
    (per : (k+2:ℕ)*l=π) (strict : ∀j : Fin m,0<R.w (j.val+1)-R.w j)
    (high : k≤∑j,R.digits j l) (kp : 0<k) :
    ∃j : Fin m,((k:ℝ)+1)*l≤R.w (j.val+1)-R.w j := by
  classical
  let g (j : Fin m):=R.w (j.val+1)-R.w j
  let b (j : Fin m):=⌊g j/l⌋₊
  let H:=univ.filter (fun j=>0<b j)
  have sumg : (∑j,g j)=π := by
    calc _=∑j∈range m,(R.w (j+1)-R.w j) := Fin.sum_univ_eq_sum_range _ _
         _=R.w m-R.w 0 := Finset.sum_range_sub ..
         _=_ := by rw [R.period];ring
  have fl (j : Fin m) : (b j:ℝ)*l≤g j := (le_div_iff₀ lp).mp (Nat.floor_le (div_nonneg (strict j).le lp.le))
  have count : (∑j,b j)=(∑j,R.digits j l)+H.card := by
    have each (j : Fin m) : b j=R.digits j l + if 0<b j then 1 else 0 := by
      change b j=b j-1+_;split_ifs <;> omega
    calc (∑j,b j)=∑j,(R.digits j l + if 0<b j then 1 else 0) := sum_congr rfl (fun j _=>each j)
         _=_ := by simp [H,sum_add_distrib]
  have bound : (∑j,b j)≤k+2 := by
    have h:=sum_le_sum (s:=univ) (fun j _=>fl j)
    rw [←sum_mul,←Nat.cast_sum,sumg,←per] at h
    exact_mod_cast (le_of_mul_le_mul_right h lp)
  have one : H.card≤1 := by
    by_contra! z
    have two : H.card=2 := by omega
    have ex : ∃j : Fin m,j∉H := by
      by_contra! none
      have eq : H=univ := Finset.eq_univ_of_forall none
      have h:=congrArg Finset.card eq
      simp at h;omega
    obtain ⟨j,hj⟩:=ex
    have zero : b j=0 := by simp [H] at hj;omega
    have lt:=Finset.sum_lt_sum (s:=univ) (fun i _=>fl i) ⟨j,mem_univ _,by simpa [zero,g] using strict j⟩
    rw [←sum_mul,←Nat.cast_sum,sumg,←per] at lt
    have h : (∑j,b j)<k+2 := by exact_mod_cast (lt_of_mul_lt_mul_right lt lp.le)
    omega
  have some : ∃j,0<b j := by
    by_contra! none
    have zero : (∑j,b j)=0 := sum_eq_zero (fun i _=>Nat.eq_zero_of_le_zero (none i))
    omega
  obtain ⟨j,hj⟩:=some
  have hsum : (∑i,b i)=b j := sum_eq_single j (fun i _ ne=>by
    by_contra! bad
    exact ne ((card_le_one.mp one) _ (mem_filter.mpr ⟨mem_univ _,Nat.pos_of_ne_zero bad⟩) _ (mem_filter.mpr ⟨mem_univ _,hj⟩))) (by simp)
  have hc : 1≤H.card:=card_pos.mpr ⟨j,mem_filter.mpr ⟨mem_univ _,hj⟩⟩
  have cast : (k:ℝ)+1≤(b j:ℝ) := by exact_mod_cast (by omega : k+1≤b j)
  exact ⟨j,(mul_le_mul_of_nonneg_right cast lp.le).trans (fl j)⟩

end R70.IntegerApex
#print axioms R70.IntegerApex.frame
#print axioms R70.IntegerApex.top_gap
