import OrderOrbitTables

namespace R67.OrderOrbit
abbrev E := Fin 10
abbrev V := Fin 5
abbrev Tri := E × E × E

def edge (a b : V) : E := Fin.ofNat 10 (edgeTable[(5*a.val+b.val)]!)
def nibble (v k : Nat) := (v >>> (4*k)) % 16
def representative (r : Fin 20) (s : E) : E := Fin.ofNat 10 (nibble repTable[r.val]! s.val)
def labels (p : Fin 120) (i : V) : V := Fin.ofNat 5 (nibble permTable[p.val]! i.val)
def ends : E→V×V := ![(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]
def edgeAction (p : Fin 120) (e : E) : E := edge (labels p (ends e).1) (labels p (ends e).2)
def slotAction (t : E) (rev : Bool) (j : E) := if rev then t-j else t+j

structure Sym where
  r : Fin 20
  p : Fin 120
  t : E
  rev : Bool
deriving Repr

def Sym.image (w : Sym) (j : E) := edgeAction w.p (representative w.r (slotAction w.t w.rev j))
def imageWord (w : Sym) : List E := List.ofFn w.image

theorem labels_bijective : ∀p,Function.Bijective (labels p) := by decide +kernel
theorem rep_bijective : ∀r,Function.Bijective (representative r) := by decide +kernel
theorem edge_ends : ∀ e,edge (ends e).1 (ends e).2=e := by decide +kernel

def StrictBetween (x y z : E) := x<y ∧ y<z ∨ z<y ∧ y<x
def Legal (o : Equiv.Perm E) : Prop := ∀ i j k : V,i<j→j<k→
  StrictBetween (o.symm (edge i j)) (o.symm (edge i k)) (o.symm (edge j k))

def triples : List Tri := [(0,1,4),(0,2,5),(0,3,6),(1,2,7),(1,3,8),(2,3,9),
  (4,5,7),(4,6,8),(5,6,9),(7,8,9)]

private theorem from_vertices : ∀t∈triples,∃i j k : V,i<j ∧ j<k ∧
    t=(edge i j,edge i k,edge j k) := by decide +kernel

def triOK (p : List E) (e : E) (t : Tri) : Bool :=
  let (a,b,c):=t
  if e=b then decide ((a∈p) ↔ c∉p)
  else if e=a then decide ((b∈p) ↔ c∈p)
  else if e=c then decide ((b∈p) ↔ a∈p)
  else true

def allowed (p : List E) (e : E) : Bool := decide (e∉p) && triples.all (triOK p e)
inductive Cert where
  | leaf (w : Sym)
  | node (sub : List (E × Cert))
def child (e : E) : List (E × Cert) → Option Cert
  | [] => none
  | (j,t)::ts => if j=e then some t else child e ts

def check : ℕ → List E → Cert → Bool
  | 0,p,.leaf w => decide (p=imageWord w)
  | n+1,p,.node ts => (List.finRange 10).all fun e =>
    if allowed p e then match child e ts with
      | some t => check n (p++[e]) t
      | none => false
    else true
  | _,_,_ => false

private def initialWord (o : Equiv.Perm E) (n : ℕ) (hn : n≤10) : List E :=
  List.ofFn fun i : Fin n => o ⟨i.val,by omega⟩

private theorem initialWord_mem (o : Equiv.Perm E) (n : ℕ) (hn : n≤10) (e : E) :
    e∈initialWord o n hn ↔ (o.symm e).val<n := by
  simp only [initialWord,List.mem_ofFn]
  constructor
  · rintro ⟨i,eq⟩
    rw [←eq,Equiv.symm_apply_apply]
    exact i.isLt
  · intro small
    exact ⟨⟨(o.symm e).val,small⟩,o.apply_symm_apply e⟩

private theorem initialWord_succ (o : Equiv.Perm E) (n : ℕ) (hn : n<10) :
    initialWord o (n+1) hn=initialWord o n hn.le++[o ⟨n,hn⟩] := by
  simp only [initialWord,List.ofFn_succ',List.concat_eq_append] <;> rfl

private theorem legal_step (o : Equiv.Perm E) (law : Legal o) (n : ℕ) (hn : n<10) :
    allowed (initialWord o n hn.le) (o ⟨n,hn⟩)=true := by
  simp only [allowed,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true]
  constructor
  · simp [initialWord_mem]
  · intro t mem
    obtain ⟨i,j,k,ij,jk,rfl⟩:=from_vertices t mem
    have h:=law i j k ij jk
    generalize aeq : edge i j=a at *
    generalize beq : edge i k=b at *
    generalize ceq : edge j k=c at *
    have ht : ((o.symm a).val<(o.symm b).val ∧ (o.symm b).val<(o.symm c).val) ∨
        ((o.symm c).val<(o.symm b).val ∧ (o.symm b).val<(o.symm a).val) := h
    dsimp only [triOK]
    have idx (e : E) (eq : o ⟨n,hn⟩=e) : (o.symm e).val=n := by rw [←eq,Equiv.symm_apply_apply]
    split_ifs with hb ha hc
    · simp only [decide_eq_true_eq,initialWord_mem]
      have mid:=idx _ hb
      rcases ht with ⟨ab,bc⟩|⟨cb,ba⟩ <;> omega
    · simp only [decide_eq_true_eq,initialWord_mem]
      have endp:=idx _ ha
      rcases ht with ⟨ab,bc⟩|⟨cb,ba⟩ <;> omega
    · simp only [decide_eq_true_eq,initialWord_mem]
      have endp:=idx _ hc
      rcases ht with ⟨ab,bc⟩|⟨cb,ba⟩ <;> omega
    · rfl

private theorem path_sound (o : Equiv.Perm E) (law : Legal o) (t n : ℕ) (hn : n≤10)
    (sum : n+t=10) (T : Cert) (pass : check t (initialWord o n hn) T=true) :
    ∃ w : Sym,List.ofFn (fun j=>o j)=imageWord w := by
  induction t generalizing n T with
  | zero =>
    have eq : n=10 := by omega
    subst n
    cases T with
    | leaf w => refine ⟨w,?_⟩; simpa [check,initialWord] using pass
    | node cs => simp [check] at pass
  | succ t ih =>
    have next : n<10 := by omega
    cases T with
    | leaf w => simp [check] at pass
    | node cs =>
      simp only [check,List.all_eq_true] at pass
      let e:=o (⟨n,next⟩:E)
      have branch:=pass e (by simp)
      have ok : allowed (initialWord o n hn) e=true := legal_step o law n next
      rw [ite_eq_left ok] at branch
      cases childEq : child e cs with
      | none => simp [childEq] at branch
      | some childT =>
        rw [childEq] at branch
        apply ih (n+1) next (by omega) childT
        simpa only [initialWord_succ o n next] using branch

theorem sound (T : Cert) (pass : check 10 [] T=true) (o : Equiv.Perm E) (law : Legal o) :
    ∃ w : Sym, ∀ j : E,o j=w.image j := by
  obtain ⟨w,h⟩:=path_sound o law 10 0 (by decide) (by decide) T (by simpa [initialWord] using pass)
  refine ⟨w,?_⟩
  exact congrFun (List.ofFn_injective h)

def checkedLeaves (P : Sym→Bool) : ℕ→Cert→Bool
  | 0,.leaf w => P w
  | n+1,.node cs => cs.all (fun x=>checkedLeaves P n x.2)
  | _,_ => false

private theorem child_mem {e : E} {cs : List (E×Cert)} {t : Cert}
    (h : child e cs=some t) : (e,t)∈cs := by
  induction cs with
  | nil => simp [child] at h
  | cons q qs ih =>
    obtain ⟨b,z⟩:=q
    by_cases eq : b=e
    · subst b
      simp [child] at h
      subst z
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih (by simpa [child,eq] using h))

private theorem path_marked (P : Sym → Bool) (o : Equiv.Perm E) (law : Legal o) (t n : ℕ) (hn : n≤10)
    (sum : n+t=10) (T : Cert) (pass : check t (initialWord o n hn) T=true) (marked : checkedLeaves P t T=true) :
    ∃ w : Sym, P w=true ∧ List.ofFn (fun j=>o j)=imageWord w := by
  induction t generalizing n T with
  | zero =>
    have eq : n=10 := by omega
    subst n
    cases T with
    | leaf w => refine ⟨w,marked,?_⟩; simpa [check,initialWord] using pass
    | node cs => simp [check] at pass
  | succ t ih =>
    have next : n<10 := by omega
    cases T with
    | leaf w => simp [check] at pass
    | node cs =>
      simp only [check,List.all_eq_true] at pass
      let e:=o (⟨n,next⟩:E)
      have branch:=pass e (by simp)
      have ok : allowed (initialWord o n hn) e=true := legal_step o law n next
      rw [ite_eq_left ok] at branch
      cases childEq : child e cs with
      | none => simp [childEq] at branch
      | some childT =>
        rw [childEq] at branch
        apply ih (n+1) next (by omega) childT
        · simpa only [initialWord_succ o n next] using branch
        · exact List.all_eq_true.mp marked (e,childT) (child_mem childEq)

theorem sound_marked (P : Sym→Bool) (T : Cert) (pass : check 10 [] T=true)
    (marks : checkedLeaves P 10 T=true) (o : Equiv.Perm E) (law : Legal o) :
    ∃ w : Sym,P w=true ∧ ∀ j : E,o j=w.image j := by
  obtain ⟨w,ok,h⟩:=path_marked P o law 10 0 (by decide) (by decide) T
    (by simpa [initialWord] using pass) marks
  exact ⟨w,ok,congrFun (List.ofFn_injective h)⟩

end R67.OrderOrbit
#print axioms R67.OrderOrbit.sound
