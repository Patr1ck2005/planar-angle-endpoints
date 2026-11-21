import SectorCharge

noncomputable section
namespace R86.ConvexMass
open Real JSP404 R54.GapTest R55.WeightedCollision R56.Windows Finset R65.Retention R85.CriticalMass InnerProductGeometry

variable {m : ℕ} {c : Fin m→Point} {θ : ℝ} {p : Fin m→ℕ}

def nearChord (c : Fin m→Point) (δ : ℝ) (i j : Fin m) : Finset (Fin m) := by
  classical
  exact univ.filter fun a=>a≠i ∧ EuclideanGeometry.angle (c j) (c i) (c a)<δ

/-- Every actual directed chord of a critical profile carries nearby original
mass in its ordinary true-ray angular neighborhood. -/
theorem near_charge {B v : ℕ} (three : 3≤m) (ci : Function.Injective c)
    (pos : 0≤θ) (below : θ<π) (mac : Macro c θ) (R : ∀i,Row (p i))
    (front : Represents R c) (back : Witnessed R c) (full : capacity R θ=B+v)
    (crit : Critical c (B+1) θ) {i j : Fin m} (ij : i≠j) :
    v+mass R θ i≤∑a∈nearChord c (π-θ) i j,mass R θ a := by
  classical
  let z:=c j-c i
  have nz : z≠0 := sub_ne_zero.mpr (ci.ne ij.symm)
  obtain ⟨old,_,clear,test⟩:=physical_sectors three ci pos below R front back full crit i
  have fit (q) (r : ℝ) (sg : r= -1 ∨ r=1) : angle (r • z) (old q)≤θ := by
    have h:=clear j ij q r sg
    rcases sg with rfl|rfl
    · simpa only [z,neg_one_smul,angle_neg_left,angle_comm (old q) (c j-c i)] using h
    · simpa only [z,one_smul,angle_comm (old q) (c j-c i)] using h
  have inc : sector c θ i z⊆nearChord c (π-θ) i j := by
    intro a h
    obtain ⟨ai,ray⟩:=(mem_filter.mp h).2
    apply mem_filter.mpr;refine ⟨mem_univ _,ai,?_⟩
    change angle z (c a-c i)<π-θ
    rcases ray with front|back
    · by_cases ja:j=a
      · subst a;rw [show c j-c i=z from rfl,angle_self nz];linarith
      · exact False.elim ((not_lt_of_ge (mac j i a ij.symm ja ai.symm)) front)
    · rw [angle_neg_left] at back;linarith
  exact (test z nz fit).trans (sum_le_sum_of_subset_of_nonneg inc (fun _ _ _=>Nat.zero_le _))

theorem close_peer {B v : ℕ} (three : 3≤m) (ci : Function.Injective c)
    (pos : 0≤θ) (below : θ<π) (mac : Macro c θ) (R : ∀i,Row (p i))
    (front : Represents R c) (back : Witnessed R c) (full : capacity R θ=B+v)
    (crit : Critical c (B+1) θ) {i j : Fin m} (ij : i≠j)
    (light : mass R θ j<v+mass R θ i) :
    ∃a,a≠i ∧ a≠j ∧ EuclideanGeometry.angle (c j) (c i) (c a)<π-θ := by
  classical
  by_contra! fail
  have sub : nearChord c (π-θ) i j⊆{j} := by
    intro a mem
    obtain ⟨ai,small⟩:=(mem_filter.mp mem).2
    apply mem_singleton.mpr
    exact by_contra (fun ne=>small.not_ge (fail a ai ne))
  have z:=near_charge three ci pos below mac R front back full crit ij
  have lim:=sum_le_sum_of_subset_of_nonneg (f:=mass R θ) sub (fun _ _ _=>Nat.zero_le _)
  simpa using (not_le_of_gt light) (z.trans (by simpa using lim))

end R86.ConvexMass
#print axioms R86.ConvexMass.near_charge
#print axioms R86.ConvexMass.close_peer
