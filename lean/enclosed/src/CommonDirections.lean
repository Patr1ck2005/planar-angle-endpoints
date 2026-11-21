import WitnessReserve
noncomputable section
namespace R66.Common
open Real JSP404 InnerProductGeometry R54.GapTest R55.WeightedCollision
def det (u v : Point) : ℝ := u 0*v 1-u 1*v 0
def Visible {I : Type*} (c : I→Point) (u : Point) : Prop :=
  ∀i,∃j,∃s:ℝ,s≠0 ∧ c j-c i=s • u

private theorem oriented {I : Type*} [Fintype I] [Nonempty I] {c : I→Point}
    {u v : Point} (ind : det u v ≠ 0) (U : Visible c u) (V : Visible c v)
    {θ : ℝ} (mac : Macro c θ) : angle u v≤θ := by
  classical
  let F (x : Point) := ((v 1-u 1)*x 0+(u 0-v 0)*x 1)/det u v
  have Fu : F u=1 := by dsimp [F];field_simp [ind];unfold det;ring
  have Fv : F v=1 := by dsimp [F];field_simp [ind];unfold det;ring
  have diff {a b x : Point} {s : ℝ} (e : b-a=s • x) : F b-F a=s*F x := by
    have e0:=congrArg (fun z : Point=>z 0) e
    have e1:=congrArg (fun z : Point=>z 1) e
    change b 0-a 0=s*x 0 at e0
    change b 1-a 1=s*x 1 at e1
    dsimp [F];rw [show b 0=a 0+s*x 0 by linarith,show b 1=a 1+s*x 1 by linarith];ring
  obtain ⟨i,_,mi⟩:=Finset.exists_min_image Finset.univ (fun i=>F (c i)) Finset.univ_nonempty
  obtain ⟨j,s,sn,eqs⟩:=U i
  obtain ⟨k,t,tn,eqt⟩:=V i
  have sj:=diff eqs
  have tk:=diff eqt
  rw [Fu,mul_one] at sj
  rw [Fv,mul_one] at tk
  have sp : 0<s := lt_of_le_of_ne (by linarith [mi j (Finset.mem_univ _)]) (Ne.symm sn)
  have tp : 0<t := lt_of_le_of_ne (by linarith [mi k (Finset.mem_univ _)]) (Ne.symm tn)
  have ji : j≠i := by intro e;subst j;linarith
  have ki : k≠i := by intro e;subst k;linarith
  have jk : j≠k := by
    intro e;subst k
    have eq:=eqs.symm.trans eqt
    have l:=congrArg (fun z : Point=>z 0) eq
    have m:=congrArg (fun z : Point=>z 1) eq
    change s*u 0=t*v 0 at l
    change s*u 1=t*v 1 at m
    apply ind
    unfold det
    have : s*(u 0*v 1-u 1*v 0)=0 := by linear_combination (v 1)*l-(v 0)*m
    exact (mul_eq_zero.mp this).resolve_left sn
  have bound:=mac j i k ji jk ki.symm
  change angle (c j-c i) (c k-c i)≤θ at bound
  simpa only [eqs,eqt,angle_smul_left_of_pos _ _ sp,angle_smul_right_of_pos _ _ tp] using bound

theorem visible_neg {I : Type*} {c : I→Point} {u : Point} (U : Visible c u) :
    Visible c (-u) := by
  intro i
  obtain ⟨j,s,n,e⟩:=U i
  exact ⟨j,-s,neg_ne_zero.mpr n,by simpa using e⟩

theorem signed_common {I : Type*} [Fintype I] [Nonempty I] {c : I→Point}
    {u v : Point} (ind : det u v ≠ 0) (U : Visible c u) (V : Visible c v)
    {θ : ℝ} (mac : Macro c θ) (s : ℝ) (sg : s= -1 ∨ s=1) :
    angle (s • u) v≤θ := by
  rcases sg with rfl|rfl
  · simp only [neg_one_smul]
    exact oriented (by simpa [det,neg_mul,sub_eq_add_neg,add_comm] using (neg_ne_zero.mpr ind)) (visible_neg U) V mac
  · simpa using oriented ind U V mac

theorem signed_budget {J : Type*} [Fintype J] (u : J→Point)
    (nz : ∀j,u j≠0) {l : ℝ} (lp : 0<l) (lepi : l≤π)
    (safe : ∀j k,j≠k→∀s:ℝ,(s= -1 ∨ s=1)→angle (s • u j) (u k)≤π-l) :
    Fintype.card J≤⌊π/l⌋₊ := by
  classical
  choose a lo hi line using fun j=>polar (u j) (nz j)
  let S:=Finset.univ.image a
  have dist (j k : J) (ne : j≠k) : l≤|a j-a k| :=
    apart (line j) (line k) (abs_le.mpr ⟨by linarith [lo j,hi k],by linarith [hi j,lo k]⟩) (safe j k ne)
  have inj : Function.Injective a := by
    intro j k eq
    by_contra ne
    have h:=dist j k ne
    rw [eq,sub_self,abs_zero] at h
    linarith
  have card : S.card=Fintype.card J := by simp [S,Finset.card_image_of_injective _ inj]
  rcases S.eq_empty_or_nonempty with z|ne
  · rw [←card,z];simp
  let x:=S.min' ne
  let y:=S.max' ne
  have xm:=S.min'_mem ne
  have ym:=S.max'_mem ne
  obtain ⟨j,_,ej⟩:=Finset.mem_image.mp xm
  obtain ⟨k,_,ek⟩:=Finset.mem_image.mp ym
  change a j=x at ej
  change a k=y at ek
  have wrap : y-x+l≤π := by
    by_cases e : j=k
    · subst k;linarith
    have h:=apart (bearing_closes (line j)) (line k)
      (show |a j+π-a k|≤π from abs_le.mpr ⟨by linarith [lo j,hi k,pi_pos],
        by have h:=S.min'_le _ ym;change x≤y at h;linarith⟩) (safe j k e)
    rw [abs_of_nonneg (by linarith [lo j,hi k])] at h
    linarith
  have span:=R51.Anchored.interval_span S lp ne x y (fun z hz=>⟨S.min'_le _ hz,S.le_max' _ hz⟩) (by
    intro p hp q hq ne
    obtain ⟨m,_,rfl⟩:=Finset.mem_image.mp hp
    obtain ⟨n,_,rfl⟩:=Finset.mem_image.mp hq
    exact dist m n (fun e=>ne (congrArg a e)))
  apply Nat.le_floor
  rw [le_div_iff₀ lp,←card] 
  linarith
#print axioms signed_common
#print axioms signed_budget
end R66.Common
