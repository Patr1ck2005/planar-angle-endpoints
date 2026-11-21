import RawBoardRows
import FiveBoardCases

noncomputable section
namespace R68.Raw
open R67 R67.Circle Finset

def triangle (i j k : Fin 5) : List ℕ :=
  [(Board.edgeOf i j).val,(Board.edgeOf i k).val,(Board.edgeOf j k).val]

private theorem triple_sound : ∀l∈Five.triples,∃ i j k : Fin 5,i<j ∧ j<k ∧ l=triangle i j k := by
  decide +kernel

private theorem triple_complete : ∀i j k : Fin 5,i<j → j<k → triangle i j k∈Five.triples := by
  decide +kernel

def tests (w : Five.Word) (tri : List ℕ) : List Five.Arc :=
  let positions:=(List.range 10).filter (fun i=>tri.contains (w.getD i 10))
  (List.range 3).map (fun a=>Five.complement (Five.arc positions a))

private def sectorTests (a b c : Slot) : List Five.Arc :=
  [Five.complement (cycle a b),Five.complement (cycle b c),Five.complement (cycle c a)]

theorem sorted_triple (o : Equiv.Perm Slot) (tri : List ℕ) {a b c : Slot}
    (ab : a<b) (bc : b<c)
    (members : ∀i : Slot,(o i).val∈tri ↔ i=a ∨ i=b ∨ i=c) :
    tests (word o) tri=sectorTests a b c := by
  let s : Fin 3→Slot:=![a,b,c]
  have asc : StrictMono s:=by
    intro i j h
    fin_cases i <;> fin_cases j <;> first | exact ab | exact bc | exact ab.trans bc | exact False.elim ((by decide : ¬ _) h)
  have mem (i : Slot) : tri.contains ((word o).getD i.val 10)=true ↔ ∃j,s j=i := by
    rw [word_get,List.contains_iff_mem,members]
    constructor
    · rintro (rfl|rfl|rfl)
      · exact ⟨0,rfl⟩
      · exact ⟨1,rfl⟩
      · exact ⟨2,rfl⟩
    · rintro ⟨j,rfl⟩;fin_cases j <;> simp [s]
  unfold tests
  rw [sorted_filter _ s asc mem]
  change (List.range 3).map (fun n=>Five.complement (Five.arc [a.val,b.val,c.val] n))=_
  rw [show List.range 3=[0,1,2] by decide]
  simp only [List.map_cons,List.map_nil,Five.arc,List.length_cons,List.length_nil]
  rfl

private theorem idx_test (o : Equiv.Perm Slot) (v e : Slot) :
    (o v).val=e.val ↔ v=o.symm e := by
  constructor
  · intro eq
    exact o.injective (by rw [o.apply_symm_apply];exact Fin.ext eq)
  · rintro rfl;simp

private theorem triangle_members (o : Equiv.Perm Slot) (i j k : Fin 5) (v : Slot) :
    (o v).val∈triangle i j k ↔ v=Board.idx o i j ∨ v=Board.idx o i k ∨ v=Board.idx o j k := by
  simp only [triangle,List.mem_cons,List.not_mem_nil,or_false,idx_test,Board.idx]

private theorem sectors_iff (g : Slot→ℝ) (G : ℕ→ℝ) (agree : ∀i : Slot,G i.val=g i)
    (a b c : Slot) : (∀l∈sectorTests a b c,1≤Five.total G l) ↔ Board.TripleOK g a b c := by
  have val (u v : Slot) : Five.total G (Five.complement (cycle u v))=length g (univ \ Circle.arc u v) := by
    rw [complement_total _ g G agree,(cycle_mask _ _).1]
  simp [sectorTests,Board.TripleOK,val]

private theorem triangle_tests_iff (o : Equiv.Perm Slot) (ok : Board.OrientOK o)
    (g : Slot→ℝ) (G : ℕ→ℝ) (agree : ∀i : Slot,G i.val=g i)
    (i j k : Fin 5) (ij : i<j) (jk : j<k) :
    (∀l∈tests (word o) (triangle i j k),1≤Five.total G l) ↔
      if Board.idx o i j<Board.idx o j k then
        Board.TripleOK g (Board.idx o i j) (Board.idx o i k) (Board.idx o j k)
      else Board.TripleOK g (Board.idx o j k) (Board.idx o i k) (Board.idx o i j) := by
  rcases ok i j k ij jk with ⟨ab,bc⟩|⟨cb,ba⟩
  · rw [ite_eq_left (ab.trans bc),sorted_triple o _ ab bc (triangle_members o i j k)]
    exact sectors_iff _ _ agree _ _ _
  · rw [ite_eq_right (cb.trans ba).asymm,sorted_triple o _ cb ba (fun v=>?_)]
    · exact sectors_iff _ _ agree _ _ _
    · rw [triangle_members];tauto

/-- Literal complement tests coincide with all the geometric macro inequalities, for
every legal edge order, including sorts with tied disjoint edges. -/
theorem macro_iff (o : Equiv.Perm Slot) (ok : Board.OrientOK o)
    (g : Slot→ℝ) (G : ℕ→ℝ) (agree : ∀i : Slot,G i.val=g i) :
    Board.MacroOK o g ↔ ∀l∈Five.triComplements (word o),1≤Five.total G l := by
  constructor
  · intro mac l hl
    change l∈Five.triples.flatMap (tests (word o)) at hl
    obtain ⟨t,mem,hm⟩:=List.mem_flatMap.mp hl
    obtain ⟨i,j,k,ij,jk,rfl⟩:=triple_sound t mem
    exact ((triangle_tests_iff o ok g G agree i j k ij jk).mpr (mac i j k ij jk)) l hm
  · intro checks i j k ij jk
    apply (triangle_tests_iff o ok g G agree i j k ij jk).mp
    intro l hl
    exact checks l (List.mem_flatMap.mpr ⟨triangle i j k,triple_complete i j k ij jk,hl⟩)

theorem all_width (g : Slot→ℝ) (G : ℕ→ℝ) (agree : ∀i : Slot,G i.val=g i) :
    Five.total G (List.range 10)=Board.total g := by
  rw [total_mask _ List.nodup_range (fun _ h=>List.mem_range.mp h) g G agree]
  have eq : mask (List.range 10)=univ := by ext v;simp [mask]
  rw [eq];rfl

def requests (o : Equiv.Perm Slot) (A : Finset Slot) : Prop :=
  ∃l∈Five.triComplements (word o),A=mask l

theorem requested_width (o : Equiv.Perm Slot) (g : Slot→ℝ) (G : ℕ→ℝ) (agree : ∀i : Slot,G i.val=g i)
    {l : Five.Arc} (member : l∈Five.triComplements (word o)) : Five.total G l=Board.width g (mask l) := by
  obtain ⟨_,_,h⟩:=List.mem_flatMap.mp member
  obtain ⟨a,_,rfl⟩:=List.mem_map.mp h
  rw [complement_total _ g G agree,complement_mask];rfl

theorem literal_legal (o : Equiv.Perm Slot) (g : Slot→ℝ) (G : ℕ→ℝ) (agree : ∀i : Slot,G i.val=g i) :
    Board.legal (requests o) g ↔ ∀l∈Five.triComplements (word o),1≤Five.total G l := by
  constructor
  · intro h l hl
    rw [requested_width o g G agree hl]
    exact h _ ⟨l,hl,rfl⟩
  · rintro h _ ⟨l,hl,rfl⟩
    rw [←requested_width o g G agree hl]
    exact h l hl

#print axioms requested_width
#print axioms literal_legal
#print axioms macro_iff
#print axioms all_width
end R68.Raw
