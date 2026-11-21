import OrderOrbit
import PhysicalBoardData

namespace R67.OrderOrbit
open JSP404 Real R55.WeightedCollision

theorem official_ends (e : E) : ends e=R67.Board.ends e := rfl
theorem edge_of_pair : ∀i j : V,i<j → R67.Board.ends (edge i j)=(i,j) := by decide +kernel

theorem actual_edge : ∀i j : V,i<j → edge i j=R67.Board.edgeOf i j := by decide +kernel

theorem legal_of_orient {o : Equiv.Perm E} (h : R67.Board.OrientOK o) : Legal o := by
  intro i j k ij jk
  rw [actual_edge i j ij,actual_edge i k (ij.trans jk),actual_edge j k jk]
  exact h i j k ij jk

/-- Any nondecreasing sort of the actual bearings works, including any
tie-breaking order on disjoint chords with exactly equal directions. -/
theorem actual_legal {c : V→Point} (C : R67.Board.Chart c) (ci : Function.Injective c)
    {θ : ℝ} (lt : θ<π) (mac : Macro c θ) (o : Equiv.Perm E)
    (asc : Monotone (R67.Board.bearing C ∘ o)) : Legal o := by
  have pull {a b : E} (ab : R67.Board.bearing C a<R67.Board.bearing C b) : o.symm a<o.symm b := by
    by_contra! ord
    have reverse:=asc ord
    simp only [Function.comp_apply,Equiv.apply_symm_apply] at reverse
    exact (not_lt_of_ge reverse) ab
  have val (i j : V) (ij : i<j) : R67.Board.bearing C (edge i j)=C.u i j := by
    simp [R67.Board.bearing,edge_of_pair i j ij]
  intro i j k ij jk
  obtain ⟨bet,_⟩:=R67.Board.triangle C ci lt mac ij jk
  rw [←val i j ij,←val i k (ij.trans jk),←val j k jk] at bet
  rcases bet with ⟨a,b⟩|⟨a,b⟩
  · exact Or.inl ⟨pull a,pull b⟩
  · exact Or.inr ⟨pull a,pull b⟩

theorem actual_orbit {c : V→Point} (C : R67.Board.Chart c) (ci : Function.Injective c)
    {θ : ℝ} (lt : θ<π) (mac : Macro c θ) (o : Equiv.Perm E)
    (asc : Monotone (R67.Board.bearing C ∘ o)) :
    ∃ w : Sym,∀j : E,o j=w.image j :=
  classify o (actual_legal C ci lt mac o asc)

end R67.OrderOrbit
#print axioms R67.OrderOrbit.actual_legal
#print axioms R67.OrderOrbit.actual_orbit
