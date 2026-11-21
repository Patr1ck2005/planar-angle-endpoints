import PhysicalBoardData
import FiveBoardDigits
import FiveBoard

noncomputable section
namespace R68.Raw
open R67 R67.Circle Finset

def word (o : Equiv.Perm Slot) : Five.Word := List.ofFn (fun j=>(o j).val)
def mask (l : List ℕ) : Finset Slot := univ.filter (fun j=>j.val∈l)
def cycle (a b : Slot) : List ℕ :=
  (List.range ((b.val+10-a.val)%10)).map (fun n=>(a.val+n)%10)

theorem word_get (o : Equiv.Perm Slot) (j : Slot) : (word o).getD j.val 10=(o j).val := by
  fin_cases j <;> rfl

theorem total_mask (l : List ℕ) (nodup : l.Nodup) (bd : ∀i∈l,i<10)
    (g : Slot→ℝ) (G : ℕ→ℝ) (agree : ∀i : Slot,G i.val=g i) :
    Five.total G l=length g (mask l) := by
  rw [Five.total,←List.sum_toFinset G nodup]
  symm
  apply Finset.sum_bij (fun (i : Slot) _=>i.val)
  · intro i hi;exact List.mem_toFinset.mpr (mem_filter.mp hi).2
  · intro i _ j _ eq;exact Fin.ext eq
  · intro n hn
    have inList:=List.mem_toFinset.mp hn
    exact ⟨⟨n,bd n inList⟩,mem_filter.mpr ⟨mem_univ _,inList⟩,rfl⟩
  · intro i _;exact (agree i).symm

/-- Only ten possible starts and ten stops enter this finite identity. -/
theorem cycle_mask : ∀a b : Slot,mask (cycle a b)=Circle.arc a b ∧
    (cycle a b).Nodup ∧ ∀i∈cycle a b,i<10 := by decide +kernel

theorem complement_mask (l : List ℕ) : mask (Five.complement l)=univ \ mask l := by
  ext i;simp [mask,Five.complement]

theorem complement_total (l : List ℕ) (g : Slot→ℝ) (G : ℕ→ℝ) (agree : ∀i : Slot,G i.val=g i) :
    Five.total G (Five.complement l)=length g (univ \ mask l) := by
  rw [←complement_mask,total_mask]
  · exact List.Pairwise.filter _ List.nodup_range
  · intro i hi;exact List.mem_range.mp (List.mem_filter.mp hi).1
  · exact agree

theorem word_incident (o : Equiv.Perm Slot) (i : Fin 5) (j : Slot) :
    Five.incident (word o) i.val j.val=true ↔ Board.incident i (o j) := by
  have table : ∀(i : Fin 5)(e : Slot),
      (let v:=Five.ends.getD e.val (5,5); i.val==v.1 || i.val==v.2)=true ↔ Board.incident i e := by decide
  unfold Five.incident;rw [word_get];exact table _ _

theorem sorted_filter (test : ℕ→Bool) {n : ℕ} (s : Fin n→Slot) (asc : StrictMono s)
    (covers : ∀i : Slot,test i.val=true ↔ ∃j,s j=i) :
    (List.range 10).filter test=List.ofFn (fun j=>(s j).val) := by
  apply List.Pairwise.eq_of_mem_iff (r:=(·<·))
  · exact List.Pairwise.filter _ List.pairwise_lt_range
  · exact List.pairwise_ofFn.mpr (fun _ _ hij=>asc hij)
  · intro a
    rw [List.mem_filter,List.mem_range,List.mem_ofFn]
    constructor
    · rintro ⟨small,hit⟩
      obtain ⟨j,eq⟩:=(covers ⟨a,small⟩).mp hit
      exact ⟨j,congrArg Fin.val eq⟩
    · rintro ⟨j,rfl⟩
      exact ⟨(s j).isLt,(covers _).mpr ⟨j,rfl⟩⟩

theorem row_positions (o : Equiv.Perm Slot) (i : Fin 5) :
    (List.range 10).filter (Five.incident (word o) i.val)=List.ofFn (fun j=>(Board.slots o i j).val) := by
  apply sorted_filter _ _ (Board.slots o i).strictMono
  intro j
  rw [word_incident]
  constructor
  · intro h
    have member : j∈Board.slotSet o i := by
      apply mem_map.mpr
      exact ⟨o j,mem_filter.mpr ⟨mem_univ _,h⟩,o.symm_apply_apply j⟩
    change j∈Set.range (Board.slots o i)
    unfold Board.slots
    rw [Finset.range_orderEmbOfFin]
    exact member
  · rintro ⟨a,rfl⟩
    exact Board.slot_inc o i a

theorem row_literal (o : Equiv.Perm Slot) (i : Fin 5) (a : Fin 4) :
    Five.rowArc (word o) i.val a.val=cycle (Board.slots o i a) (Board.slots o i (a+1)) := by
  unfold Five.rowArc
  rw [row_positions]
  unfold Five.arc
  simp only [List.length_ofFn]
  fin_cases a <;> rfl

theorem row_mask (o : Equiv.Perm Slot) (i : Fin 5) (a : Fin 4) :
    mask (Five.rowArc (word o) i.val a.val)=Board.fiber (Board.group o) i a := by
  rw [row_literal,(cycle_mask _ _).1]
  rw [←Board.group_eq]
  ext j;simp [Board.fiber]

theorem row_width (o : Equiv.Perm Slot) (g : Slot→ℝ) (G : ℕ→ℝ) (agree : ∀i : Slot,G i.val=g i)
    (i : Fin 5) (a : Fin 4) :
    Five.total G (Five.rowArc (word o) i.val a.val)=Board.width g (Board.fiber (Board.group o) i a) := by
  rw [←row_mask]
  apply total_mask _ _ _ _ _ agree <;> rw [row_literal]
  · exact (cycle_mask _ _).2.1
  · exact (cycle_mask _ _).2.2

theorem row_score (o : Equiv.Perm Slot) (g : Slot→ℝ) (G : ℕ→ℝ) (agree : ∀i : Slot,G i.val=g i)
    (i : Fin 5) : Board.exponent (Board.group o) g i=
    Five.rowSum (fun v a=>Five.digit (Five.total G (Five.rowArc (word o) v a))) i.val := by
  have atSlot (a : Fin 4) := row_width o g G agree i a
  unfold Board.exponent Five.rowSum
  rw [Fin.sum_univ_four]
  change _=Five.digit (Five.total G (Five.rowArc (word o) i.val (0 : Fin 4).val))+
    Five.digit (Five.total G (Five.rowArc (word o) i.val (1 : Fin 4).val))+
    Five.digit (Five.total G (Five.rowArc (word o) i.val (2 : Fin 4).val))+
    Five.digit (Five.total G (Five.rowArc (word o) i.val (3 : Fin 4).val))
  simp only [atSlot]
  rfl

#print axioms sorted_filter
#print axioms row_mask
#print axioms row_width
#print axioms row_score
end R68.Raw
