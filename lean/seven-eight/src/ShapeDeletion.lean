import CircleSurgery

noncomputable section
namespace R58.CircleModel
open Real JSP404 R55.WeightedCollision

namespace Lift
variable {t : ℕ} (C : CircleModel.Lift t)

theorem delete_maximal (ht : 5≤t) {w : Fin t→ℕ} (hw : ∀i,0<w i) {lam : ℝ} (lp : 0<lam)
    (hit : π-lam∈attainable w C.centers) :
    ∃ T : ℕ, ∃ e : Fin T ↪ Fin t, ∃ v : Fin T→ℕ, (T+1=t ∨ T+2=t) ∧
      (∀i,w (e i)≤v i) ∧ (∑i,w i)≤∑i,v i ∧ π-lam∈attainable v (fun i=>C.centers (e i)) := by
  obtain ⟨r,rfl⟩ : ∃r,t=r+5 := ⟨t-5,by omega⟩
  obtain ⟨pos,leg,fits⟩ := (C.spectrum_at (by omega) hw lp).mp hit
  have mass : (∑i,w i)≤C.mass lam := Finset.sum_le_sum (fun i _=>fits i)
  obtain ⟨n,cut⟩ := C.best_cut lp leg
  have bridge {T h : ℕ} (sum : T+h=r+5) (room : 3≤T)
      (bound : C.mass lam≤(C.erase T h sum (by omega) n).mass lam) :
      ∃e : Fin T ↪ Fin (r+5), ∃v : Fin T→ℕ, (∀i,w (e i)≤v i) ∧
      (∑i,w i)≤∑i,v i ∧ π-lam∈attainable v (fun i=>C.centers (e i)) := by
    let Q := C.erase T h sum (by omega) n
    obtain ⟨e,fixed⟩ := C.survivors sum (by omega) n
    have sub := restrict_attainable hit e e.injective
    have E : Q.centers=(fun i=>C.centers (e i)) := funext fixed
    rw [←E] at sub
    obtain ⟨_,law,can⟩ := (Q.spectrum_at room (fun i=>hw (e i)) lp).mp sub
    have top := Q.attainable_maximal room lp law pos
    rw [E] at top
    exact ⟨e,_,can,mass.trans bound,top⟩
  rcases cut with h|h
  · obtain ⟨e,v,fits,mass,hit⟩ := bridge (T:=r+4) (h:=1) (by omega) (by omega) h
    exact ⟨_,e,v,Or.inl (by omega),fits,mass,hit⟩
  · obtain ⟨e,v,fits,mass,hit⟩ := bridge (T:=r+3) (h:=2) (by omega) (by omega) h
    exact ⟨_,e,v,Or.inr (by omega),fits,mass,hit⟩

end Lift

private theorem exact_allocation {K : Type*} [Fintype K] (lo hi : K→ℕ) (le : ∀i,lo i≤hi i)
    (N : ℕ) (lb : (∑i,lo i)≤N) (ub : N≤∑i,hi i) :
    ∃v : K→ℕ, (∀i,lo i≤v i) ∧ (∀i,v i≤hi i) ∧ (∑i,v i)=N := by
  classical
  have fill (k : ℕ) (fits : (∑i,lo i)+k≤∑i,hi i) :
      ∃v : K→ℕ, (∀i,lo i≤v i) ∧ (∀i,v i≤hi i) ∧ (∑i,v i)=(∑i,lo i)+k := by
    induction k with
    | zero => exact ⟨lo,fun _=>le_rfl,le,by simp⟩
    | succ k ih =>
      obtain ⟨v,lower,upper,total⟩ := ih (by omega)
      have room : ∃i,v i<hi i := by
        by_contra! full
        have eq : v=hi := funext (fun i=>le_antisymm (upper i) (full i))
        rw [eq] at total
        omega
      obtain ⟨j,free⟩ := room
      refine ⟨fun i=>v i+if i=j then 1 else 0,fun i=>(lower i).trans (Nat.le_add_right _ _),?_,?_⟩
      · intro i;by_cases e : i=j
        · subst i;simp;omega
        · simp [e,upper i]
      · simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true,total]
        omega
  obtain ⟨v,a,b,z⟩ := fill (N-∑i,lo i) (by omega)
  exact ⟨v,a,b,by omega⟩

theorem trim {I : Type*} [Fintype I] {c : I→Point} {v w : I→ℕ} {θ : ℝ}
    (le : ∀i,w i≤v i) (hit : θ∈attainable v c) : θ∈attainable w c := by
  intro ε he
  obtain ⟨f,fi,rad,cap⟩ := hit ε he
  let F : Label w→Label v := fun a=>⟨a.1,a.2.castLE (le a.1)⟩
  have inj : Function.Injective F := by
    rintro ⟨i,j⟩ ⟨k,l⟩ e
    obtain rfl : i=k := congrArg Sigma.fst e
    have eq := (Sigma.mk.inj_iff.mp e).2.eq
    exact congrArg (Sigma.mk i) (Fin.ext (congrArg (fun z : Fin (v i)=>z.val) eq))
  refine ⟨f∘F,fi.comp inj,fun a=>rad (F a),lt_of_le_of_lt (maxAngle_mono ?_) cap⟩
  intro x hx
  obtain ⟨z,_,rfl⟩ := Finset.mem_image.mp hx
  exact Finset.mem_image_of_mem f (Finset.mem_univ (F z))

/-- Delete one or two actual macrocenters from a concyclic configuration. All
remaining multiplicities may be increased so that the old total is kept exactly,
at the same angle cap and the same retained centers. -/
theorem circle_delete {I : Type*} [Fintype I] (size : 5≤Fintype.card I)
    (c : I→Point) (ci : Function.Injective c) (circle : OnCircle c)
    {w : I→ℕ} (hw : ∀i,0<w i) {lam : ℝ} (lp : 0<lam) (hit : π-lam∈attainable w c) :
    ∃ T : ℕ, ∃ e : Fin T ↪ I, ∃ v : Fin T→ℕ, (T+1=Fintype.card I ∨ T+2=Fintype.card I) ∧
      (∀i,w (e i)≤v i) ∧ (∑i,v i)=(∑i,w i) ∧ π-lam∈attainable v (fun i=>c (e i)) := by
  classical
  have nt : Nontrivial I := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨C,ord,eq⟩ := sort_circle c ci circle
  have sorted := restrict_attainable hit ord ord.injective
  rw [←funext eq] at sorted
  obtain ⟨T,e,v,sz,lower,cap,got⟩ := C.delete_maximal size (fun i=>hw (ord i)) lp sorted
  let S := e.trans ord.toEmbedding
  have eql (i) : C.centers (e i)=c (S i) := eq _
  rw [funext eql] at got
  have upper : (∑i,w i)≤∑i,v i := (Equiv.sum_comp ord w).symm.trans_le cap
  have within : (∑i,w (S i))≤∑i,w i := by
    calc (∑i,w (S i)) = ∑j∈Finset.univ.image S,w j := (Finset.sum_image S.injective.injOn).symm
         _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _=>Nat.zero_le _)
  obtain ⟨exactly,sl,su,total⟩ := exact_allocation (fun i=>w (S i)) v lower _ within upper
  exact ⟨T,S,exactly,sz,sl,total,trim su got⟩

#print axioms circle_delete
end R58.CircleModel
