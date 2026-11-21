import BoardArcLengths
noncomputable section
namespace R67.Board
open Real JSP404 R55.WeightedCollision R67.Circle Finset
def edgeOf : Fin 5→Fin 5→Fin 10 := ![![0,0,1,2,3],![0,0,4,5,6],![0,0,0,7,8],![0,0,0,0,9],![0,0,0,0,0]]
theorem edge_law : ∀i j : Fin 5,i<j→ends (edgeOf i j)=(i,j) := by decide
def idx (o : Equiv.Perm (Fin 10)) (i j : Fin 5) := o.symm (edgeOf i j)
def TripleOK (g : Slot→ℝ) (p q r : Slot) : Prop :=
  1≤length g (univ \ arc p q) ∧ 1≤length g (univ \ arc q r) ∧ 1≤length g (univ \ arc r p)
def OrientOK (o : Equiv.Perm (Fin 10)) : Prop := ∀i j k : Fin 5,i<j→j<k→
  (idx o i j < idx o i k ∧ idx o i k < idx o j k) ∨ (idx o j k < idx o i k ∧ idx o i k < idx o i j)
def MacroOK (o : Equiv.Perm (Fin 10)) (g : Slot→ℝ) : Prop := ∀i j k : Fin 5,i<j→j<k→
  if idx o i j < idx o j k then TripleOK g (idx o i j) (idx o i k) (idx o j k)
  else TripleOK g (idx o j k) (idx o i k) (idx o i j)

private theorem normalized {x y θ : ℝ} (t : θ<π) (xy : x≤y) (upper : |x-y|≤θ) :
    1≤π/(π-θ)-(y/(π-θ)-x/(π-θ)) := by
  rw [←sub_div,←sub_div,le_div_iff₀ (sub_pos.mpr t)]
  rw [abs_of_nonpos (sub_nonpos.mpr xy)] at upper
  linarith
private theorem normalized_span {x y θ : ℝ} (t : θ<π) (xy : x≤y) (lower : π-θ≤|x-y|) :
    1≤y/(π-θ)-x/(π-θ) := by
  rw [←sub_div,le_div_iff₀ (sub_pos.mpr t)]
  rw [abs_of_nonpos (sub_nonpos.mpr xy)] at lower
  linarith

private theorem cyclic_three (x : Slot→ℝ) (T : ℝ) {p q r : Slot} (pq : p<q) (qr : q<r)
    (a : 1≤T-(x q-x p)) (b : 1≤T-(x r-x q)) (d : 1≤x r-x p) :
    TripleOK (gaps x T) p q r := by
  simp only [TripleOK,arc_complement,ite_eq_left pq.le,ite_eq_left qr.le,ite_eq_right (not_le.mpr (pq.trans qr))]
  exact ⟨a,b,by linarith⟩

theorem macro_data {c : Fin 5→Point} (C : Chart c) (ci : Function.Injective c)
    {θ : ℝ} (lt : θ<π) (mac : Macro c θ) (o : Equiv.Perm (Fin 10))
    (mono : Monotone (bearing C ∘ o)) :
    OrientOK o ∧ MacroOK o (gaps (fun s=>bearing C (o s)/(π-θ)) (π/(π-θ))) := by
  let x (s : Slot):=bearing C (o s)/(π-θ)
  have eq (i j : Fin 5) (h : i<j) : (bearing C ∘ o) (idx o i j)=C.u i j := by
    simp [idx,bearing,edge_law i j h]
  have main (i j k : Fin 5) (ij : i<j) (jk : j<k) :
      (idx o i j < idx o i k ∧ idx o i k < idx o j k ∧ TripleOK (gaps x (π/(π-θ))) (idx o i j) (idx o i k) (idx o j k)) ∨
      (idx o j k < idx o i k ∧ idx o i k < idx o i j ∧ TripleOK (gaps x (π/(π-θ))) (idx o j k) (idx o i k) (idx o i j)) := by
    obtain ⟨order,wide,left,right⟩:=triangle C ci lt mac ij jk
    have ik:=ij.trans jk
    have X (a b : Fin 5) (h : a<b) : x (idx o a b)=C.u a b/(π-θ) := congrArg (fun z:ℝ=>z/(π-θ)) (eq a b h)
    rcases order with ⟨p,q⟩|⟨p,q⟩
    · have ab : idx o i j < idx o i k := lt_of_not_ge (fun h=>p.not_ge (by simpa only [eq _ _ ij,eq _ _ ik] using mono h))
      have bc : idx o i k < idx o j k := lt_of_not_ge (fun h=>q.not_ge (by simpa only [eq _ _ ik,eq _ _ jk] using mono h))
      left;refine ⟨ab,bc,cyclic_three x _ ab bc ?_ ?_ ?_⟩ <;> simp only [X _ _ ij,X _ _ jk,X _ _ ik]
      · exact normalized lt p.le left
      · exact normalized lt q.le right
      · exact normalized_span lt (p.trans q).le wide
    · have ab : idx o j k < idx o i k := lt_of_not_ge (fun h=>p.not_ge (by simpa only [eq _ _ jk,eq _ _ ik] using mono h))
      have bc : idx o i k < idx o i j := lt_of_not_ge (fun h=>q.not_ge (by simpa only [eq _ _ ik,eq _ _ ij] using mono h))
      right;refine ⟨ab,bc,cyclic_three x _ ab bc ?_ ?_ ?_⟩ <;> simp only [X _ _ ij,X _ _ jk,X _ _ ik]
      · exact normalized lt p.le (by simpa only [abs_sub_comm (C.u j k) (C.u i k)] using right)
      · exact normalized lt q.le (by simpa only [abs_sub_comm (C.u i k) (C.u i j)] using left)
      · exact normalized_span lt (p.trans q).le (by simpa only [abs_sub_comm (C.u j k) (C.u i j)] using wide)
  constructor
  · intro i j k ij jk
    rcases main i j k ij jk with ⟨a,b,_⟩|⟨a,b,_⟩
    · exact Or.inl ⟨a,b⟩
    · exact Or.inr ⟨a,b⟩
  · intro i j k ij jk
    rcases main i j k ij jk with ⟨a,b,h⟩|⟨a,b,h⟩
    · simpa only [ite_eq_left (a.trans b)] using h
    · simpa only [ite_eq_right ((a.trans b).asymm)] using h

def classify (s : Fin 4→Slot) (v : Slot) : Fin 4 :=
  if v<s 0 then 3 else if v<s 1 then 0 else if v<s 2 then 1 else if v<s 3 then 2 else 3
def group (o : Equiv.Perm (Fin 10)) (i : Fin 5) := classify (slots o i)

private theorem member (a b v : Slot) :
    v∈arc a b ↔ if a≤b then a≤v ∧ v<b else a≤v ∨ v<b := by
  by_cases h:a≤b
  · simp only [arc,ite_eq_left h,interval,pre,Finset.mem_sdiff,Finset.mem_filter,Finset.mem_univ,true_and]
    change (v.val<b.val ∧ ¬v.val<a.val) ↔ a.val≤v.val ∧ v.val<b.val
    omega
  · simp only [arc,ite_eq_right h,interval,pre,Finset.mem_sdiff,Finset.mem_filter,Finset.mem_univ,true_and]
    change ¬(v.val<a.val ∧ ¬v.val<b.val) ↔ a.val≤v.val ∨ v.val<b.val
    omega

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem finite_classify : ∀a b c d : Slot,a<b→b<c→c<d→∀j : Fin 4,∀v : Slot,
    classify ![a,b,c,d] v=j ↔ v∈arc (![a,b,c,d] j) (![a,b,c,d] (j+1)) := by decide +kernel
private theorem classify_eq (s : Fin 4→Slot) (asc : StrictMono s) (j : Fin 4) (v : Slot) :
    classify s v=j ↔ v∈arc (s j) (s (j+1)) := by
  have eq : ![s 0,s 1,s 2,s 3]=s := by funext a;fin_cases a <;> rfl
  simpa only [eq] using finite_classify _ _ _ _ (asc (show (0:Fin 4)<1 by decide))
    (asc (show (1:Fin 4)<2 by decide)) (asc (show (2:Fin 4)<3 by decide)) j v

theorem group_eq (o : Equiv.Perm (Fin 10)) (i : Fin 5) (j : Fin 4) :
    univ.filter (fun v=>group o i v=j)=arc (slots o i j) (slots o i (j+1)) := by
  ext v
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ,true_and]
  exact classify_eq (slots o i) (slots o i).strictMono j v

theorem slot_cost_eq (o : Equiv.Perm (Fin 10)) (x : Slot→ℝ) (T : ℝ) (i : Fin 5) :
    slotCost o x T i=∑j : Fin 4,(⌊length (gaps x T) (univ.filter (fun v=>group o i v=j))⌋₊-1) := by
  unfold slotCost
  apply sum_congr rfl;intro j _
  rw [group_eq,arc_sum]
  have asc:StrictMono (slots o i):=(slots o i).strictMono
  fin_cases j <;> norm_num [Fin.reduceAdd,ite_eq_left (asc (show (0:Fin 4)<1 by decide)).le,
    ite_eq_left (asc (show (1:Fin 4)<2 by decide)).le,ite_eq_left (asc (show (2:Fin 4)<3 by decide)).le,
    ite_eq_right ((asc (show (0:Fin 4)<3 by decide)).not_ge)]
#print axioms macro_data
#print axioms group_eq
#print axioms slot_cost_eq
end R67.Board
