import IntegerApex
noncomputable section
namespace R70.IntegerApex
open Real Finset JSP404 R37.SignedFan InnerProductGeometry R55.WeightedCollision
open R54.GapTest R56.Windows

/-- Three distinct genuine walls resolve the possible antipodal tie in a closed chart. -/
theorem closed_chart {I : Type*} [Fintype I] [DecidableEq I] {c : I→Point}
    (ci : Function.Injective c) {θ a b : ℝ} (legal : Macro c θ) (lt : θ<π) (nn : 0≤θ)
    (width : b-a≤π-θ) (i : I) (many : 3≤Fintype.card (Peer i))
    (cover : ∀j,i≠j → ∃t : ℝ,a≤t ∧ t≤b ∧ Bearing (c j-c i) t) :
    ∃ t : Peer i→ℝ,(∀j,a≤t j ∧ t j≤b) ∧ ∀j k : Peer i,
      EuclideanGeometry.angle (c j.val) (c i) (c k.val)=|t j-t k| := by
  classical
  choose t low high r rp e signs eq using fun j : Peer i=>cover j.val j.property
  have val (j k:Peer i) : EuclideanGeometry.angle (c j.val) (c i) (c k.val)=
      if e j=e k then |t j-t k| else π-|t j-t k| := by
    change angle (c j.val-c i) (c k.val-c i)=_
    rw [eq j,eq k,angle_smul_left_of_pos _ _ (rp j),angle_smul_right_of_pos _ _ (rp k)]
    have d : angle (circleDirection (t j)) (circleDirection (t k))=|t j-t k| := by
      rw [angle_circleDirection,←cos_abs,arccos_cos (abs_nonneg _) (abs_le.mpr ⟨by linarith [low j,high k],by linarith [high j,low k]⟩)]
    rcases signs j with u|u <;> rcases signs k with v|v <;>
      norm_num [u,v,angle_neg_left,angle_neg_right,d]
  have inj : Function.Injective t := by
    intro j k same; by_contra ne
    have jk : j.val≠k.val := fun eq=>ne (Subtype.ext eq)
    have p:=strict_angle ci lt legal j.property.symm jk k.property
    have h:=legal j.val i k.val j.property.symm jk k.property
    rw [val,same,sub_self,abs_zero] at p h
    by_cases z : e j=e k
    · simp [z] at p
    · simp [z] at h
      linarith
  have mid : ∃ p : Peer i,a<t p ∧ t p<b := by
    by_contra! fail
    have sub : (univ.image t) ⊆ {a,b} := by
      rintro _ h;obtain ⟨j,_,rfl⟩:=mem_image.mp h
      simp only [mem_insert,mem_singleton]
      by_cases z : a<t j
      · exact Or.inr (le_antisymm (high j) (fail j z))
      · exact Or.inl (le_antisymm (not_lt.mp z) (low j))
    have cn:=card_le_card sub
    rw [card_image_of_injective _ inj,card_univ] at cn
    have lim : ({a,b}:Finset ℝ).card≤2 := by by_cases h:a=b <;> simp [h]
    omega
  obtain ⟨p,pl,ph⟩:=mid
  have common (j : Peer i) : e j=e p := by
    by_contra ne
    have jk : j.val≠p.val := fun eq=>ne (congrArg e (Subtype.ext eq))
    have h:=legal j.val i p.val j.property.symm jk p.property
    rw [val,ite_eq_right ne] at h
    have near : |t j-t p|<b-a := abs_lt.mpr ⟨by linarith [low j],by linarith [high j]⟩
    linarith
  exact ⟨t,fun j=>⟨low j,high j⟩,fun j k=>by rw [val,ite_eq_left ((common j).trans (common k).symm)]⟩

/-- A strictly positive multiwall row has no full-period gap. -/
theorem gap_lt {m : ℕ} (hm : 2≤m) (R : R56.Windows.Row m)
    (strict : ∀i:Fin m,0<R.w (i.val+1)-R.w i) (j:Fin m) :
    R.w (j.val+1)-R.w j<π := by
  let g (i:Fin m):=R.w (i.val+1)-R.w i
  have other : ∃i : Fin m,i≠j := by
    by_contra! fail
    have small : (univ : Finset (Fin m)).card≤1 := card_le_one.mpr (fun i _ k _=>(fail i).trans (fail k).symm)
    simp at small; omega
  obtain ⟨i,ne⟩:=other
  have s : ∑i,g i=π := by
    calc _=∑i∈range m,(R.w (i+1)-R.w i) := Fin.sum_univ_eq_sum_range _ _
         _=R.w m-R.w 0 := Finset.sum_range_sub ..
         _=_ := by rw [R.period];ring
  have inc := Finset.sum_lt_sum (s:=univ) (f:=fun i=>if i=j then g j else 0) (g:=g)
    (fun t _=>by by_cases z:t=j <;> simp [z,(strict t).le,g]) ⟨i,mem_univ _,by simpa [ne,g] using strict i⟩
  simpa [s] using inc

/-- A high admissible fiber forces its entire genuine Euclidean fan into a closed narrow cone. -/
theorem apexes {I : Type*} [Fintype I] [DecidableEq I] [Nontrivial I] {c : I→Point}
    (ci : Function.Injective c) {w:I→ℕ} {l : ℝ} (lp:0<l) {k:ℕ} (kp:0<k)
    (per : (k+2:ℕ)*l=π) (many : ∀i:I,3≤Fintype.card (Peer i))
    (A : Admissible w c (π-l)) : ∀i,dim w i≤k ∧ (k≤dim w i → ∀ j h : Peer i,
        EuclideanGeometry.angle (c j.val) (c i) (c h.val)≤l) := by
  classical
  obtain ⟨F,front,back,size⟩:=frame ci (by linarith : π-l<π) A.1 A.2.1
  intro i
  have d : dim w i≤∑j,(row (F i)).digits j l := by
    simpa only [R56.Windows.score,R51.Anchored.gapScore,R56.Windows.Row.digits] using
      admissible_bound (fun j=>row (F j)) lp back A i
  have three:3≤(F i).n+1 := (many i).trans (size i)
  have eq : ((k:ℝ)+2)*l=π := by simpa using per
  constructor
  · by_contra! too
    obtain ⟨j,big⟩:=R66.Five.long_gap (row (F i)) lp (by nlinarith only [eq,lp] : π<((k:ℝ)+3)*l)
      ((show k+1≤dim w i by omega).trans d)
    exact (gap_lt (by omega) _ (gap_pos _) j).not_ge (eq ▸ big)
  · intro high
    obtain ⟨z,big⟩:=top_gap three (row (F i)) lp per (gap_pos _) (high.trans d) kp
    have cover:=R66.Five.complement_interval (fun h=>row (F h)) front i z
    obtain ⟨t,within,actual⟩:=closed_chart ci A.2.1 (by linarith) A.1 (by nlinarith only [big,eq]) i (many i) cover
    intro j h
    rw [actual]
    exact abs_le.mpr ⟨by nlinarith only [(within j).1,(within h).2,eq,big],by nlinarith only [(within j).2,(within h).1,eq,big]⟩
end R70.IntegerApex
#print axioms R70.IntegerApex.closed_chart
#print axioms R70.IntegerApex.apexes
