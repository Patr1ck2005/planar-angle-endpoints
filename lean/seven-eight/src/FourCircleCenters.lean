import ShapeDeletion

noncomputable section
namespace R58.CircleModel
open Real JSP404 R55.WeightedCollision

private theorem descent_fin (t : ℕ) : ∀ (sz : 3≤t) (c : Fin t→Point),
    Function.Injective c → OnCircle c → ∀ (w : Fin t→ℕ), (∀i,0<w i) → ∀ {lam : ℝ}, 0<lam →
    π-lam∈attainable w c →
    ∃ k : ℕ, ∃ e : Fin k ↪ Fin t, ∃ v : Fin k→ℕ, 3≤k ∧ k≤4 ∧ (∀i,w (e i)≤v i) ∧
      (∑i,v i)=(∑i,w i) ∧ π-lam∈attainable v (fun i=>c (e i)) := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
    intro sz c ci circle w wp lam lp hit
    by_cases stop : t≤4
    · exact ⟨t,Function.Embedding.refl _,w,sz,stop,fun _=>le_rfl,rfl,hit⟩
    · have big : 5≤Fintype.card (Fin t) := by simp;omega
      obtain ⟨T,e,x,count,kept,total,smallHit⟩ := circle_delete big c ci circle wp lp hit
      simp only [Fintype.card_fin] at count
      have round : OnCircle (fun i=>c (e i)) := by
        obtain ⟨o,r,H⟩ := circle
        exact ⟨o,r,fun i=>H _⟩
      obtain ⟨k,g,v,klo,khi,more,eq,finalHit⟩ := ih T (by omega) (by omega) (fun i=>c (e i))
        (ci.comp e.injective) round x (fun i=>(wp _).trans_le (kept i)) lp smallHit
      exact ⟨k,g.trans e,v,klo,khi,fun i=>(kept _).trans (more i),eq.trans total,finalHit⟩

/-- Every attained angle cap below π on at least three distinct concyclic
macrocenters can already be attained using three or four of those same centers.
The total number of actual labeled points is unchanged, and no retained center
loses multiplicity. -/
theorem reduce_to_four {I : Type*} [Fintype I] (size : 3≤Fintype.card I)
    (c : I→Point) (ci : Function.Injective c) (circle : OnCircle c)
    {w : I→ℕ} (hw : ∀i,0<w i) {lam : ℝ} (lp : 0<lam) (hit : π-lam∈attainable w c) :
    ∃ k : ℕ, ∃ e : Fin k ↪ I, ∃ v : Fin k→ℕ, 3≤k ∧ k≤4 ∧ (∀i,w (e i)≤v i) ∧
      (∑i,v i)=(∑i,w i) ∧ π-lam∈attainable v (fun i=>c (e i)) := by
  classical
  let ord := (Fintype.equivFin I).symm
  have round : OnCircle (fun i=>c (ord i)) := by
    obtain ⟨o,r,H⟩ := circle
    exact ⟨o,r,fun i=>H _⟩
  obtain ⟨k,e,v,lo,hi,kept,total,cap⟩ := descent_fin _ size (fun i=>c (ord i))
    (ci.comp ord.injective) round (fun i=>w (ord i)) (fun i=>hw _) lp (restrict_attainable hit ord ord.injective)
  exact ⟨k,e.trans ord.toEmbedding,v,lo,hi,kept,total.trans (Equiv.sum_comp ord w),cap⟩

#print axioms reduce_to_four
end R58.CircleModel
