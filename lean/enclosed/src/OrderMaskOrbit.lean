import OrderMask0
import OrderMask4
import OrderMask7
import OrderMask9
import OrderOrbitPhysical
import FiveCanonicalWords

namespace R67.OrderOrbit

theorem representative_mem : ∀r : Fin 20,representativeWord r∈R67.Five.canonical := by decide +kernel

/-- The same witness classifies the edges and both families of gap masks.
The equalities are multiset equalities at both levels, retaining repetitions. -/
theorem masks_of_legal (o : Equiv.Perm E) (h : Legal o) :
    ∃ w : Sym, (∀j : E,o j=w.image j) ∧ representativeWord w.r∈R67.Five.canonical ∧
      MaskLaw w (actualWord o) := by
  obtain ⟨w,tests,slots⟩:=classify_marked maskTest masks0 masks4 masks7 masks9 o h
  refine ⟨w,slots,representative_mem _,?_⟩
  have eq : (o : E→E)=w.image := funext slots
  rw [eq]
  exact maskTest_sound w tests

theorem masks_of_orient (o : Equiv.Perm E) (h : R67.Board.OrientOK o) :
    ∃ w : Sym, (∀j : E,o j=w.image j) ∧ representativeWord w.r∈R67.Five.canonical ∧
      MaskLaw w (actualWord o) := masks_of_legal o (legal_of_orient h)

open JSP404 Real R55.WeightedCollision in
theorem physical_masks {c : V→Point} (C : R67.Board.Chart c) (ci : Function.Injective c)
    {θ : ℝ} (lt : θ<π) (mac : Macro c θ) (o : Equiv.Perm E)
    (asc : Monotone (R67.Board.bearing C ∘ o)) :
    ∃ w : Sym, (∀j : E,o j=w.image j) ∧ representativeWord w.r∈R67.Five.canonical ∧
      MaskLaw w (actualWord o) := masks_of_legal o (actual_legal C ci lt mac o asc)

end R67.OrderOrbit
#print axioms R67.OrderOrbit.masks_of_legal
#print axioms R67.OrderOrbit.masks_of_orient
#print axioms R67.OrderOrbit.physical_masks

