import ConvexEar

noncomputable section
namespace R86.ConvexMass
open Real JSP404 R54.GapTest R55.WeightedCollision R56.Windows Finset R65.Retention R85.CriticalMass InnerProductGeometry

/-- Delete a site whose mass is at most the mass at an apex where its true
ray is angularly isolated. The actual freed chord supplies one new axis. -/
theorem delete_isolated {t : ℕ} {c : Fin (t+1)→Point} (ci : Function.Injective c)
    {θ : ℝ} (below : θ<π) (mac : Macro c θ) {m : Fin (t+1)→ℕ} (R : ∀i,Row (m i))
    (front : Represents R c) {i j : Fin (t+1)} (ij : i≠j) (cheaper : mass R θ j≤mass R θ i)
    (isolated : ∀a,a≠i → a≠j → π-θ≤EuclideanGeometry.angle (c j) (c i) (c a))
    {p : Fin t→ℕ} (Q : ∀a,Row (p a)) (back : Witnessed Q (c∘j.succAboveEmb)) :
    capacity R θ≤capacity Q θ := by
  let A:=full_axes R (sub_pos.mpr below) front
  let z:=c j-c i
  have nz : z≠0 := sub_ne_zero.mpr (ci.ne ij.symm)
  let V : Fin (score R i (π-θ)+1)→Point := Fin.cons z (A.v i)
  have kit : InternalTrial V θ := by
    refine ⟨Fin.cases nz (A.nonzero i),?_⟩
    intro a b ne s sg
    cases a using Fin.cases with
    | zero =>
      cases b using Fin.cases with
      | zero => exact False.elim (ne rfl)
      | succ b =>
        have h:=A.outside i j ij b s sg
        change angle (s • z) (A.v i b)≤θ
        rcases sg with rfl|rfl <;> simpa only [z,one_smul,neg_one_smul,angle_neg_left,angle_comm (A.v i b) (c j-c i),sub_sub_cancel] using h
    | succ a =>
      cases b using Fin.cases with
      | zero => change angle (s • A.v i a) (c j-c i)≤θ
                simpa only [sub_sub_cancel] using A.outside i j ij a s sg
      | succ b => change angle (s • A.v i a) (A.v i b)≤θ
                  simpa only [one_smul,sub_sub_cancel] using A.internal i a b (fun eq=>ne (congrArg Fin.succ eq)) s 1 sg (Or.inr rfl)
  obtain ⟨b,hb⟩:=Fin.exists_succAbove_eq ij
  have clean (a:Fin t) (ba:b≠a) : Compatible V θ ((c∘j.succAboveEmb) a-(c∘j.succAboveEmb) b) := by
    intro k s sg
    change angle (s • V k) (c (j.succAbove a)-c (j.succAbove b))≤θ
    rw [hb]
    have ai : j.succAbove a≠i := hb ▸ (fun eq=>ba.symm (Fin.succAbove_right_injective eq))
    have aj:=Fin.succAbove_ne j a
    cases k using Fin.cases with
    | zero =>
      change angle (s • z) (c (j.succAbove a)-c i)≤θ
      rcases sg with rfl|rfl
      · rw [neg_one_smul,angle_neg_left]
        have dig:=isolated _ ai aj
        change π-θ≤angle z (c (j.succAbove a)-c i) at dig
        linarith
      · rw [one_smul]
        exact mac j i _ ij.symm aj.symm ai.symm
    | succ k => change angle (s • A.v i k) (c (j.succAbove a)-c i)≤θ
                simpa only [sub_sub_cancel] using A.outside i _ ai.symm k s sg
  have fit:=trial_fits Q back below b V kit clean
  have double : mass R θ i+mass R θ i≤mass Q θ b := by
    have z:=Nat.pow_le_pow_right (by decide : 0<2) fit
    simpa only [pow_succ,Nat.mul_two] using z
  have step (a:Fin t) : mass R θ (j.succAbove a)+(if a=b then mass R θ j else 0)≤mass Q θ a := by
    by_cases ab:a=b
    · subst a;simp only [hb,ite_true];omega
    · rw [ite_eq_right ab,add_zero]
      exact Nat.pow_le_pow_right (by decide) (R62.Contraction.retained_row R front j.succAboveEmb Q back (sub_pos.mpr below) a)
  have tot:=sum_le_sum (s:=univ) (fun a _=>step a)
  rw [sum_add_distrib] at tot
  simp only [sum_ite_eq',mem_univ,ite_true] at tot
  change (∑a,mass R θ a)≤∑a,mass Q θ a
  rw [Fin.sum_univ_succAbove _ j,add_comm]
  exact tot

/-- Any large-turn, locally light tip can actually be removed with its full mass. -/
theorem delete_ear {n : ℕ} {c : Site n→Point} (ci : Function.Injective c) (hull : HullOrder c)
    {θ : ℝ} (below : θ<π) (mac : Macro c θ) {m : Site n→ℕ} (R : ∀i,Row (m i))
    (front : Represents R c) (j : Site n) (large : 2*(π-θ)≤exterior c j)
    (light₁ : mass R θ j≤mass R θ (prev j)) (light₂ : mass R θ j≤mass R θ (next j))
    {p : Fin (n+2)→ℕ} (Q : ∀a,Row (p a)) (back : Witnessed Q (c∘j.succAboveEmb)) :
    capacity R θ≤capacity Q θ := by
  have pn := (primary j).1
  have nn := (primary j).2.1
  by_cases le : ∃a,a≠prev j ∧ a≠j ∧ EuclideanGeometry.angle (c j) (c (prev j)) (c a)<π-θ
  · have no : ¬∃a,a≠next j ∧ a≠j ∧ EuclideanGeometry.angle (c j) (c (next j)) (c a)<π-θ :=
      fun ri=>large.not_gt (ear_two_peers ci hull θ j le ri)
    push Not at no
    exact delete_isolated ci below mac R front nn light₂ no Q back
  · push Not at le
    exact delete_isolated ci below mac R front pn light₁ le Q back

end R86.ConvexMass
#print axioms R86.ConvexMass.delete_isolated
#print axioms R86.ConvexMass.delete_ear
