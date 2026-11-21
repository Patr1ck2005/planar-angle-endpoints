import FiveBoardModel
namespace R67.Five
open R67.Farkas

def total (g : ℕ→ℝ) (a : Arc) : ℝ := (a.map g).sum
def rowSum (q : ℕ→ℕ→ℕ) (v : ℕ) : ℕ := q v 0+q v 1+q v 2+q v 3

def clip (q : ℕ→ℕ) (m a : ℕ) : ℕ :=
  match a with
  | 0=>min (q 0) m
  | 1=>min (q 1) (m-q 0)
  | 2=>min (q 2) (m-q 0-q 1)
  | _=>min (q 3) (m-q 0-q 1-q 2)

private theorem clip_lt (q : ℕ→ℕ) (m a : ℕ) (ha : a<4) : clip q m a≤q a := by
  interval_cases a <;> exact min_le_left _ _

private theorem clip_sum (q : ℕ→ℕ) (m : ℕ) (hm : m≤q 0+q 1+q 2+q 3) :
    clip q m 0+clip q m 1+clip q m 2+clip q m 3=m := by
  simp only [clip];omega

private def x (g : ℕ→ℝ) (p : ℕ→ℕ) (k : ℕ) : ℕ→ℝ
  | 0=>1
  | j+1=> if j<10 then g j else if j<26 then (p (j-10):ℝ) else (k:ℝ)

private theorem xg (g : ℕ→ℝ) (p : ℕ→ℕ) (k j : ℕ) (hj : j<10) : x g p k (j+1)=g j := by simp [x,hj]
private theorem xq (g : ℕ→ℝ) (p : ℕ→ℕ) (k j : ℕ) (hj : j<16) : x g p k (10+j+1)=p j := by
  simp [x,show ¬10+j<10 by omega,show 10+j<26 by omega]
private theorem xk (g : ℕ→ℝ) (p : ℕ→ℕ) (k : ℕ) : x g p k (26+1)=k := by simp [x]

private theorem totals (x' : ℕ→ℝ) (g : ℕ→ℝ) (l : List ℕ) (z : ℤ)
    (same : ∀i∈l,x' (i+1)=g i) :
    ((terms l z).map (fun p=>(p.2:ℝ)*x' (p.1+1))).sum=(z:ℝ)*total g l := by
  induction l with
  | nil=>simp [terms,total]
  | cons a l ih=>
    have ha:=same a (List.mem_cons_self)
    have rest:=ih (fun i hi=>same i (List.mem_cons_of_mem _ hi))
    change (z:ℝ)*x' (a+1)+((terms l z).map (fun p=>(p.2:ℝ)*x' (p.1+1))).sum=_
    rw [ha,rest];simp [total];ring

private theorem bounded_sum (g : ℕ→ℝ) (a : Arc) (h : ∀j∈a,g j≤2) :
    total g a≤2*(a.length:ℝ) := by
  induction a with
  | nil=>simp [total]
  | cons i a ih=>
    have hi:=h i List.mem_cons_self
    have rest:=ih (fun j hj=>h j (List.mem_cons_of_mem _ hj))
    simp only [total,List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one] at *
    linarith

theorem mem_arc {ps : List ℕ} {a i : ℕ} (hi : i∈arc ps a) : i<10 := by
  obtain ⟨j,_,rfl⟩:=List.mem_map.mp hi
  exact Nat.mod_lt _ (by decide)

private theorem mem_compl {a : Arc} {i : ℕ} (hi : i∈complement a) : i<10 :=
  List.mem_range.mp (List.mem_filter.mp hi).1

private theorem valid_tri {w : Word} {a : Arc} (ha : a∈triComplements w) {i : ℕ} (hi : i∈a) : i<10 := by
  obtain ⟨_,_,hh⟩:=List.mem_flatMap.mp ha
  obtain ⟨_,_,rfl⟩:=List.mem_map.mp hh
  exact mem_compl hi

private theorem marked_ok {u b : ℕ} (hu : u<5) (hb : b<4) :
    (marked u).getD b 5<5 ∧ (marked u).getD b 5≠u := by
  interval_cases u <;> interval_cases b <;> decide

/-- Direct geometric data for the exact rational board certificate. Angles and gaps are real.
The integer costs can exceed the required row sums. -/
theorem bound {w : Word} {u h k : ℕ} (cert : Proved w u h) (hu : u<5) (hk : k≤30)
    (g : ℕ→ℝ) (q : ℕ→ℕ→ℕ) (lower : ∀j,j<10 → 0≤g j) (upper : ∀j,j<10 → g j≤2)
    (tri : ∀ a∈triComplements w,1≤total g a)
    (pos : ∀ v,v<5 → v≠u → ∀ a,a<4 → 0<q v a → (q v a:ℝ)+1≤total g (rowArc w v a))
    (scores : ∀ v,v<5 → v≠u → k+weight v h≤rowSum q v) :
    (2:ℝ)*k+goal h≤2*total g (List.range 10) := by
  let qa (v a : ℕ) := clip (q v) (k+weight v h) a
  let p (j : ℕ) := qa (vertex u j) (j%4)
  let xx:=x g p k
  have nonneg : ∀i,0≤xx i := by
    intro i;cases i with
    | zero=>exact zero_le_one
    | succ i=>dsimp [xx,x];split
              next hi=>exact lower _ hi
              next _=>split <;> positivity
  have x0 : xx 0=1 := rfl
  have ones (a : Arc) (range : ∀i∈a,i<10) (z : ℤ) :=
    totals xx g a z (fun i hi=>xg g p k i (range i hi))
  have localPos (j : ℕ) (hj : j<16) (pj : 0<p j) : (p j:ℝ)+1≤total g (ar w u j) := by
    have vb := marked_ok hu (show j/4<4 by omega)
    have ab := Nat.mod_lt j (by decide : 0<4)
    have l := clip_lt (q (vertex u j)) (k+weight (vertex u j) h) (j%4) ab
    change p j≤_ at l
    exact le_trans (by exact_mod_cast Nat.add_le_add_right l 1) (pos _ vb.1 vb.2 _ ab (lt_of_lt_of_le pj l))
  have active (j : ℕ) (hj : j<16) (hp : 0<xx (10+j+1)) : 0≤val xx ((model w u h).active j) := by
    have xj := xq g p k j hj
    have pj : 0<p j := by change 0<x g p k (10+j+1) at hp;rw [xj] at hp;exact_mod_cast hp
    change 0≤val xx (positive j (ar w u j))
    rw [positive,val_aff,List.map_cons,List.sum_cons,x0]
    rw [ones (ar w u j) (fun _ hm=>mem_arc hm) 1]
    change 0≤_+((_ : ℝ)* x g p k (10+j+1)+_)
    rw [xj];push_cast;linarith [localPos j hj pj]
  have good : Good xx (model w u h).base := by
    intro l hl
    simp only [model,List.mem_append,List.mem_map,List.mem_cons,List.not_mem_nil,or_false,List.mem_flatMap] at hl
    rcases hl with ((((ht|hc)|hk')|ha)|hr)|hb
    · obtain ⟨a,ha,rfl⟩:=ht
      rw [triRule,val_aff,x0,ones _ (fun _ hm=>valid_tri ha hm)]
      push_cast;linarith [tri a ha]
    · obtain ⟨i,hi,rfl⟩:=hc
      simp [capRule,val_aff,x0,show xx (i+1)=g i from xg g p k i (List.mem_range.mp hi)]
      exact upper _ (List.mem_range.mp hi)
    · subst l
      simp [kRule,val_aff,x0,show xx 27=k from xk g p k]
      exact_mod_cast hk
    · obtain ⟨j,hj,rfl⟩:=ha
      have jr:=List.mem_range.mp hj
      let a:=ar w u j
      have arange : ∀i∈a,i<10 := fun _ hm=>mem_arc hm
      have Q : ℝ := 2*(a.length:ℝ)-1
      have qj : xx (10+j+1)=p j := xq g p k j jr
      change 0≤val xx (arcRule j a)
      rw [arcRule,val_aff,List.map_cons,List.sum_cons,ones _ arange,qj]
      push_cast
      by_cases zero : p j=0
      · rw [zero];push_cast
        by_cases emp : a=[]
        · simp [emp,total]
        · have len : (1:ℝ)≤a.length := by exact_mod_cast List.length_pos_iff.mpr emp
          have mass : 0≤total g a := List.sum_nonneg (fun v hv=>by obtain ⟨_,hi,rfl⟩:=List.mem_map.mp hv;exact lower _ (arange _ hi))
          nlinarith [mul_nonneg mass (show 0≤2*(a.length:ℝ)-1 by linarith)]
      · have real := localPos j jr (Nat.pos_of_ne_zero zero)
        change (p j:ℝ)+1≤total g a at real
        have up:=bounded_sum g a (fun i hi=>upper i (arange i hi))
        have len : 0≤2*(a.length:ℝ)-1 := by linarith
        nlinarith [mul_nonneg len (sub_nonneg.mpr real)]
    · obtain ⟨b,hb,eq⟩:=hr
      have br := List.mem_range.mp hb
      let v:=(marked u).getD b 5
      have vb:=marked_ok hu br
      have exactSum := clip_sum (q v) (k+weight v h) (scores v vb.1 vb.2)
      have qp (a : ℕ) (ha : a<4) : xx (10+4*b+a+1)=qa v a := by
        rw [show 10+4*b+a+1=10+(4*b+a)+1 by omega]
        change x g p k _=_
        rw [xq g p k _ (by omega)]
        congr 1
        change clip _ _ _=clip _ _ _
        have div : (4*b+a)/4=b := by omega
        have md : (4*b+a)%4=a := by omega
        simp only [vertex,div,md,v]
      have evalRow (z : ℤ) : val xx (rowRule z b h v)=
          (z:ℝ)*((weight v h:ℝ)+k-(qa v 0+qa v 1+qa v 2+qa v 3:ℕ)) := by
        simp only [rowRule,val_aff,List.map_cons,List.sum_cons,x0,mul_one,Int.cast_mul,Int.cast_natCast]
        rw [show (List.range 4)=[0,1,2,3] by decide]
        simp [terms,show xx 27=k from xk g p k,qp,show xx (10+4*b+1)=qa v 0 from qp 0 (by decide)]
        ring
      have eqn : (qa v 0+qa v 1+qa v 2+qa v 3:ℕ)=k+weight v h := exactSum
      have any (z : ℤ) : 0≤val xx (rowRule z b h v) := by rw [evalRow,eqn];push_cast;ring_nf;exact le_rfl
      rcases eq with eq|eq <;> subst l <;> exact any _
    · obtain ⟨j,_,rfl⟩:=List.mem_map.mp (show l∈(List.range 28).map (fun j=>unitAt j 1) from hb)
      simpa [val_unit] using nonneg j
  have targetBound := run cert nonneg x0 (fun j le=>by
    rcases lt_or_eq_of_le le with h|h
    · exact ⟨_,xq g p k j h⟩
    · subst j;exact ⟨k,xk g p k⟩) active good
  simp only [target,val_aff,List.map_cons,List.sum_cons,x0,mul_one,Int.cast_neg,Int.cast_natCast] at targetBound
  rw [ones _ (fun _ hi=>List.mem_range.mp hi) 2] at targetBound
  change 0≤_+((-2:ℝ)*x g p k 27+_) at targetBound
  rw [xk] at targetBound;push_cast at targetBound;linarith

end R67.Five
#print axioms R67.Five.bound
