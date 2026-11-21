import ConvexPeeling

noncomputable section
namespace R86.ConvexMass
open Real JSP404 R54.GapTest R55.WeightedCollision R56.Windows Finset R65.Retention R85.CriticalMass

/-- Any locally affordable family in a retention-critical support has
strictly insufficient exterior turn for a one-ear deletion. -/
theorem critical_turn_budget {n N : ℕ} {c : Site n→Point} (ci : Function.Injective c)
    (hull : HullOrder c) {θ : ℝ} (below : θ<π) (mac : Macro c θ)
    {m : Site n→ℕ} (R : ∀i,Row (m i)) (front : Represents R c)
    (full : N≤capacity R θ) (crit : Critical c N θ)
    (U : Finset (Site n)) (un : U.Nonempty)
    (cheap : ∀j∈U,mass R θ j≤mass R θ (prev j) ∧ mass R θ j≤mass R θ (next j)) :
    2*π<(∑j∈univ \ U,exterior c j)+U.card*(2*(π-θ)) := by
  by_contra! budget
  obtain ⟨j,mem,big⟩:=eligible_ear ci hull U un budget
  obtain ⟨p,Q,fwd,rev⟩:=actual_rows (c∘j.succAboveEmb) (ci.comp j.succAboveEmb.injective)
  have improve:=delete_ear ci hull below mac R front j big (cheap j mem).1 (cheap j mem).2 Q rev
  have loss:=crit (h:=n+2) (by omega) (by omega) j.succAboveEmb Q fwd rev
  omega

/-- An equal-capacity strictly convex critical hull lies in the exact
necessary window π < number_of_sites * defect ≤ 2π. -/
theorem critical_equal_window {n N : ℕ} {c : Site n→Point} (ci : Function.Injective c)
    (hull : HullOrder c) {θ : ℝ} (below : θ<π) (mac : Macro c θ)
    {m : Site n→ℕ} (R : ∀i,Row (m i)) (front : Represents R c)
    (full : N≤capacity R θ) (crit : Critical c N θ)
    (flat : ∀i,mass R θ i=mass R θ 0) :
    π<((n:ℝ)+3)*(π-θ) ∧ ((n:ℝ)+3)*(π-θ)≤2*π := by
  have lower:=critical_turn_budget ci hull below mac R front full crit univ univ_nonempty
    (fun j _=>⟨((flat j).trans (flat _).symm).le,((flat j).trans (flat _).symm).le⟩)
  rw [show (univ \ (univ : Finset (Site n))) = ∅ by ext; simp, sum_empty, zero_add, card_univ, Fintype.card_fin] at lower
  push_cast at lower
  have each (i : Site n) : π-θ≤exterior c i := by
    have h:=primary i
    have angle_bound:=mac (prev i) i (next i) h.1 h.2.2.1 h.2.1.symm
    unfold exterior
    linarith only [angle_bound]
  have upper:=sum_le_sum (s:=(univ : Finset (Site n))) (fun i _=>each i)
  rw [total_turn ci hull,sum_const,nsmul_eq_mul,card_univ,Fintype.card_fin] at upper
  push_cast at upper
  exact ⟨by linarith only [lower],upper⟩

end R86.ConvexMass
#print axioms R86.ConvexMass.critical_turn_budget
#print axioms R86.ConvexMass.critical_equal_window
