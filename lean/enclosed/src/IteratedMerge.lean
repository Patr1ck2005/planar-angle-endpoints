import FixedWeightMerge
noncomputable section
open scoped Classical
namespace R64.Merge
open Real JSP404 Finset R51.Anchored R54.GapTest R55.WeightedCollision R56.Windows R62.Contraction

structure Shape where
  size : ℕ
  two : 2≤size
  c : Fin size→Point
  ci : Function.Injective c
  w : Fin size→ℕ
  wp : ∀i,0<w i

def collapse (S : Shape) {h : ℕ} (two : 2≤h) (e : Fin h↪Fin S.size) (a : Fin h) : Shape where
  size:=h
  two:=two
  c:=S.c∘e
  ci:=S.ci.comp e.injective
  w:=weights S.w e a
  wp:=positive S.wp e a

/-- Concrete exterior angular parallax and sufficient space in every retained gap. -/
structure Test (δ : ℝ) (S : Shape) {h : ℕ} (e : Fin h↪Fin S.size) (a : Fin h) where
  q : Fin h→ℕ
  Q : ∀j,Row (q j)
  front : Represents Q (S.c∘e)
  back : Witnessed Q (S.c∘e)
  initial : 0≤(Q a).w 0 ∧ (Q a).w 0<π
  error : ℕ→ℝ
  wall : ∀j≤q a,Wall (univ.image S.c) ((mergedFiber e a).image S.c)
    ((Q a).w 0) ((Q a).w j) (error j)
  fit : ∀j : Fin (q a),(Q a).w (j.val+1)-(Q a).w j+error j+error (j.val+1)<
    (((Q a).digits j δ:ℝ)+2)*δ

inductive Reduces (δ : ℝ) : Shape→Prop where
  | terminal (S : Shape) (four : S.size≤4) : Reduces δ S
  | cyclic (S : Shape) (onCircle : R58.CircleModel.OnCircle S.c) : Reduces δ S
  | step (S : Shape) {h : ℕ} (two : 2≤h) (less : h<S.size) (e : Fin h↪Fin S.size) (a : Fin h)
      (test : Test δ S e a) (tail : Reduces δ (collapse S two e a)) : Reduces δ S

private theorem fin_nontrivial {k : ℕ} (two : 2≤k) : Nontrivial (Fin k) :=
  ⟨⟨⟨0,by omega⟩,⟨1,by omega⟩,by intro e; have z:=congrArg Fin.val e;contradiction⟩⟩

/-- Any finite chain of matching geometric gap tests, of any depth and arity,
gives the literal Sendov lower bound at the original number of labels. -/
theorem lower_of_chain {δ : ℝ} (dp : 0<δ) (S : Shape) (chain : Reduces δ S) :
    3≤∑i,S.w i → π-δ∈attainable S.w S.c → Jsp404.alphaN (∑i,S.w i)≤π-δ := by
  induction chain with
  | terminal S four =>
    intro many hit
    exact (R53.FourCover.full_staircase many).2 (R59.Concyclic.four_scores S.two four S.c S.ci S.wp hit)
  | cyclic S onCircle =>
    intro many hit
    have two : 2≤Fintype.card (Fin S.size) := by simpa using S.two
    exact R59.Concyclic.concyclic_staircase two S.c S.ci onCircle S.wp many hit
  | step S two less e a cert tail ih =>
    intro many hit
    letI : Nontrivial (Fin S.size):=fin_nontrivial S.two
    have moved:=fixed_merge S.ci S.wp dp hit e a cert.Q cert.front cert.back cert.initial cert.error cert.wall cert.fit
    have mass : (∑i,(collapse S two e a).w i)=∑i,S.w i := total S.w e a
    have ans:=ih (mass ▸ many) moved
    rwa [mass] at ans

end R64.Merge
#print axioms R64.Merge.lower_of_chain
