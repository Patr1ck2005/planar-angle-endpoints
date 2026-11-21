import FourCircleCenters
import FourCenterStaircase

noncomputable section
namespace R59.Concyclic
open R58.CircleModel Real JSP404 R55.WeightedCollision

/-- A fixed two-, three-, or four-center profile has a nondegenerate sample
baseline, so its absolute tolerance yields R53's relative four-cover tolerance. -/
theorem four_scores {k : ℕ} (two : 2≤k) (four : k≤4) (c : Fin k→Point)
    (ci : Function.Injective c) {w : Fin k→ℕ} (wp : ∀i,0<w i) {θ : ℝ}
    (hit : θ∈attainable w c) : θ∈R53.FourCover.scores (∑i,w i) := by
  classical
  let a : Fin k:=⟨0,by omega⟩
  let b : Fin k:=⟨1,by omega⟩
  have ab : a≠b := fun h=>Nat.zero_ne_one (congrArg Fin.val h)
  let D:=dist (c a) (c b)
  have dp : 0<D := dist_pos.mpr (ci.ne ab)
  intro δ pos
  let e:=min δ (min (D/4) (δ*(D/2)))
  have ep : 0<e := lt_min pos (lt_min (by positivity) (by positivity))
  obtain ⟨f,inj,near,ang⟩:=hit e ep
  let p:=f (representative wp a)
  let q:=f (representative wp b)
  have mp (i : Fin k) : f (representative wp i)∈points f :=
    Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have pa : dist (c a) p<e := by simpa [p,representative,dist_comm] using near (representative wp a)
  have qb : dist q (c b)<e := near (representative wp b)
  have ee : e≤D/4 := (min_le_right _ _).trans (min_le_left _ _)
  have half : D/2≤dist p q := by
    have t₁:=dist_triangle (c a) p (c b)
    have t₂:=dist_triangle p q (c b)
    change D≤_ at t₁
    linarith
  have pq : p≠q := dist_pos.mp (lt_of_lt_of_le (by positivity : 0<D/2) half)
  refine ⟨points f,?_,ang.trans_le (add_le_add_right (min_le_left _ _) _),p,mp a,q,mp b,pq,?_,?_⟩
  · simp [points,Finset.card_image_of_injective _ inj,Fintype.card_sigma]
  · exact fun j : Fin 4=>if h : j.val<k then c ⟨j.val,h⟩ else c a
  · rintro x hx
    obtain ⟨y,_,rfl⟩:=Finset.mem_image.mp hx
    let j : Fin 4:=⟨y.1.val,by have h:=y.1.isLt;omega⟩
    refine ⟨j,?_⟩
    simp only [j,dif_pos y.1.isLt,Fin.eta]
    exact (near y).le.trans (((min_le_right _ _).trans (min_le_right _ _)).trans
      (mul_le_mul_of_nonneg_left half pos.le))

private theorem staircase_le_pi (N : ℕ) : Jsp404.alphaN N≤π := by
  rcases N with _|_|_|_|n
  all_goals first | exact pi_pos.le | exact (by change π/3≤π;linarith [pi_pos]) | skip
  rw [Jsp404.alphaN_succ_add]
  split <;> apply le_trans (mul_le_mul_of_nonneg_right (sub_le_self _ (by positivity)) pi_pos.le) <;> simp

/-- Every actual attainable profile with at least two distinct concyclic
macrocenters satisfies the full conjectured Sendov staircase, for every N≥3. -/
theorem concyclic_staircase {I : Type*} [Fintype I] (two : 2≤Fintype.card I)
    (c : I→Point) (ci : Function.Injective c) (circle : OnCircle c)
    {w : I→ℕ} (wp : ∀i,0<w i) (size : 3≤∑i,w i) {θ : ℝ} (hit : θ∈attainable w c) :
    Jsp404.alphaN (∑i,w i)≤θ := by
  classical
  by_cases big : π≤θ
  · exact (staircase_le_pi _).trans big
  apply (R53.FourCover.full_staircase size).2
  by_cases three : 3≤Fintype.card I
  · have e : π-(π-θ)=θ := by ring
    obtain ⟨k,g,v,lo,hi,more,sz,att⟩:=reduce_to_four three c ci circle wp
      (show 0<π-θ by linarith) (by simpa only [e] using hit)
    rw [e] at att
    rw [←sz]
    exact four_scores (by omega) hi _ (ci.comp g.injective) (fun j=>(wp _).trans_le (more j)) att
  · let g := (Fintype.equivFin I).symm
    have h:=four_scores two (by omega) _ (ci.comp g.injective) (fun j=>wp (g j))
      (restrict_attainable hit g g.injective)
    rwa [Equiv.sum_comp g w] at h

#print axioms four_scores
#print axioms concyclic_staircase
end R59.Concyclic

