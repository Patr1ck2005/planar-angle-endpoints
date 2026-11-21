import CriticalCenters
noncomputable section
namespace R65.Retention
open Real JSP404 R54.GapTest R55.WeightedCollision R56.Windows Finset R62.Contraction

variable {h N : ℕ} {c : Fin (h+1)→Point} {θ : ℝ}
    {m : Fin (h+1)→ℕ} (R : ∀i,Row (m i))

/-- The retained row doubles its dyadic capacity as soon as its exponent grows.
The deleted row must have strictly larger original exponent. -/
theorem deletion_gain_lt (two : 2≤h) (below : θ<π) (front : Represents R c)
    (room : N≤capacity R θ) (crit : Critical c N θ)
    (x : Fin (h+1)) {s : Fin h→ℕ} (Q : ∀i,Row (s i))
    (fwd : Represents Q (c∘x.succAboveEmb)) (rev : Witnessed Q (c∘x.succAboveEmb))
    (j : Fin h) (grow : score R (x.succAbove j) (π-θ)<score Q j (π-θ)) :
    score R (x.succAbove j) (π-θ)<score R x (π-θ) := by
  classical
  let A (i : Fin (h+1)):=2^(score R i (π-θ))
  let B (i : Fin h):=2^(score Q i (π-θ))
  have monot (i : Fin h) : A (x.succAbove i)≤B i :=
    Nat.pow_le_pow_right (by decide) (retained_row R front x.succAboveEmb Q rev (sub_pos.mpr below) i)
  have twice : A (x.succAbove j)+A (x.succAbove j)≤B j := by
    have step:=Nat.pow_le_pow_right (by decide : 0<2) (Nat.succ_le_iff.mpr grow)
    simpa only [pow_succ,Nat.mul_two,A,B] using step
  have cmp (i : Fin h) : A (x.succAbove i)+(if i=j then A (x.succAbove j) else 0)≤B i := by
    by_cases eq : i=j
    · subst i;simpa using twice
    · simpa [eq] using monot i
  have sumfit:=sum_le_sum (s:=univ) (fun i _=>cmp i)
  rw [sum_add_distrib] at sumfit
  simp only [sum_ite_eq',mem_univ,ite_true] at sumfit
  have full : N≤A x+∑i,A (x.succAbove i) := by
    change N≤∑i,A i at room
    rwa [Fin.sum_univ_succAbove A x] at room
  have small : (∑i,B i)<N := crit two (by omega) x.succAboveEmb Q fwd rev
  by_contra! bad
  have opp : A x≤A (x.succAbove j) := Nat.pow_le_pow_right (by decide) bad
  omega

def Gain (c : Fin (h+1)→Point) (θ : ℝ) (i x : Fin (h+1)) : Prop :=
  ∃ j : Fin h,x.succAbove j=i ∧ ∃s : Fin h→ℕ,∃Q : ∀k,Row (s k),
    Represents Q (c∘x.succAboveEmb) ∧ Witnessed Q (c∘x.succAboveEmb) ∧
    score R i (π-θ)<score Q j (π-θ)

theorem gain_wellFounded (two : 2≤h) (below : θ<π) (front : Represents R c)
    (room : N≤capacity R θ) (crit : Critical c N θ) : WellFounded (Gain R c θ) := by
  apply Subrelation.wf (r:=fun i x=>score R i (π-θ)<score R x (π-θ)) ?_
    (measure (fun i=>score R i (π-θ))).wf
  rintro i x ⟨j,rfl,s,Q,fwd,rev,grow⟩
  exact deletion_gain_lt R two below front room crit x Q fwd rev j grow

theorem maximal_stable (two : 2≤h) (below : θ<π) (front : Represents R c)
    (room : N≤capacity R θ) (crit : Critical c N θ)
    (x : Fin (h+1)) {s : Fin h→ℕ} (Q : ∀i,Row (s i))
    (fwd : Represents Q (c∘x.succAboveEmb)) (rev : Witnessed Q (c∘x.succAboveEmb))
    (j : Fin h) (maximal : ∀i, score R i (π-θ)≤score R (x.succAbove j) (π-θ)) :
    score Q j (π-θ)=score R (x.succAbove j) (π-θ) := by
  apply le_antisymm _ (retained_row R front x.succAboveEmb Q rev (sub_pos.mpr below) j)
  exact le_of_not_gt (fun grows=>(maximal x).not_gt (deletion_gain_lt R two below front room crit x Q fwd rev j grows))

#print axioms deletion_gain_lt
#print axioms gain_wellFounded
#print axioms maximal_stable
end R65.Retention