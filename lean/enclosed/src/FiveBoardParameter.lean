import FiveCanonicalWords
namespace R67.Five

private theorem lengths_ok : canonical.all (fun w=>(List.range 5).all (fun v=>
    decide (rowSum (fun i a=>(rowArc w i a).length) v=10)))=true := by decide +kernel

theorem lengths {w : Word} (hw : w∈canonical) (v : ℕ) (hv : v<5) :
    rowSum (fun i a=>(rowArc w i a).length) v=10 := by
  have h:=lengths_ok
  simp only [List.all_eq_true,List.mem_range,decide_eq_true_eq] at h
  exact h _ hw _ hv

private theorem cap {w : Word} (g : ℕ→ℝ) (upper : ∀j,j<10 → g j≤2) (v a : ℕ) :
    digit (total g (rowArc w v a))≤2*(rowArc w v a).length := by
  let ar:=rowArc w v a
  have size (l : List ℕ) (ha : ∀j∈l,j<10) : total g l≤(2*l.length:ℕ) := by
    induction l with
    | nil=>simp [total]
    | cons j l ih=>
      have rest:=ih (fun i hi=>ha i (List.mem_cons_of_mem _ hi))
      have first:=upper j (ha _ List.mem_cons_self)
      change g j+total g l≤_
      push_cast at *;simp only [List.length_cons,Nat.cast_succ] at *;linarith
  have s := Nat.floor_mono (size ar (fun _ hh=>mem_arc hh))
  simp only [Nat.floor_natCast] at s
  exact (Nat.sub_le _ 1).trans s

/-- Global width bounds and just one marked row force k≤20 on every canonical board. -/
theorem k_le_twenty {w : Word} (hw : w∈canonical) {u h k : ℕ} (_hu : u<5) (g : ℕ→ℝ)
    (upper : ∀j,j<10 → g j≤2)
    (scores : ∀v,v<5 → v≠u → k+weight v h≤rowSum (fun i a=>digit (total g (rowArc w i a))) v) :
    k≤20 := by
  let v:=if u=0 then 1 else 0
  have hv : v<5 ∧ v≠u := by dsimp [v];split <;> omega
  have l:=lengths hw v hv.1
  have r:=scores v hv.1 hv.2
  simp only [rowSum] at l r
  have a:=cap (w:=w) g upper v 0;have b:=cap (w:=w) g upper v 1
  have c:=cap (w:=w) g upper v 2;have d:=cap (w:=w) g upper v 3
  omega

end R67.Five
#print axioms R67.Five.k_le_twenty
