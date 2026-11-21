import OrderOrb0
import OrderOrb4
import OrderOrb7
import OrderOrb9

namespace R67.OrderOrbit

private def root : Cert := .node [(0,tree0),(4,tree4),(7,tree7),(9,tree9)]
private theorem accepted : check 10 [] root=true := by
  rw [root,check,List.all_eq_true]
  intro e _
  fin_cases e
  · exact pass0
  · rfl
  · rfl
  · rfl
  · exact pass4
  · rfl
  · rfl
  · exact pass7
  · rfl
  · exact pass9

/-- The representative list follows the order of the twenty Python certificates.
For an actual slot j, first read representative slot t+j or t−j modulo ten,
then relabel the two unordered endpoints. -/
theorem classify (o : Equiv.Perm E) (h : Legal o) :
    ∃ w : Sym, ∀ j : E,o j=edgeAction w.p (representative w.r (slotAction w.t w.rev j)) :=
  sound root accepted o h

noncomputable def vertexPerm (p : Fin 120) : Equiv.Perm V := Equiv.ofBijective _ (labels_bijective p)
noncomputable def boardPerm (r : Fin 20) : Equiv.Perm E := Equiv.ofBijective _ (rep_bijective r)
def representativeWord (r : Fin 20) := List.ofFn (fun j : E => (representative r j).val)

theorem classify_permutation (o : Equiv.Perm E) (h : Legal o) :
    ∃ (r : Fin 20) (p : Equiv.Perm V) (t : E) (rev : Bool),∀ j : E,
      let e := boardPerm r (slotAction t rev j)
      o j=edge (p (ends e).1) (p (ends e).2) := by
  obtain ⟨w,ok⟩:=classify o h
  exact ⟨w.r,vertexPerm w.p,w.t,w.rev,ok⟩

theorem classify_marked (P : Sym→Bool)
    (a : checkedLeaves P 9 tree0=true) (b : checkedLeaves P 9 tree4=true)
    (c : checkedLeaves P 9 tree7=true) (d : checkedLeaves P 9 tree9=true)
    (o : Equiv.Perm E) (h : Legal o) : ∃w : Sym,P w=true ∧ ∀j : E,o j=w.image j :=
  sound_marked P root accepted (by simpa only [root,checkedLeaves,List.all_cons,List.all_nil,
    Bool.and_true] using (show (checkedLeaves P 9 tree0 && (checkedLeaves P 9 tree4 &&
      (checkedLeaves P 9 tree7 && checkedLeaves P 9 tree9)))=true by simp only [a,b,c,d,Bool.and_true])) o h

end R67.OrderOrbit
#print axioms R67.OrderOrbit.classify
#print axioms R67.OrderOrbit.classify_permutation
