import NoJump
import ConcyclicStaircase
noncomputable section
open scoped Classical
namespace R64.Merge
open Real JSP404 Finset R51.Anchored R54.GapTest R55.WeightedCollision R56.Windows R62.Contraction
variable {I J : Type*} [Fintype I] [Fintype J]

open Classical in
def weights (w : I→ℕ) (e : J ↪ I) (a j : J) : ℕ :=
  if j=a then ∑i∈mergedFiber e a,w i else w (e j)

theorem center_mem (e : J↪I) (a : J) : e a∈mergedFiber e a := by
  classical
  simp [mergedFiber]

theorem positive {w : I→ℕ} (pos : ∀i,0<w i) (e : J↪I) (a j : J) : 0<weights w e a j := by
  classical
  by_cases eq : j=a
  · subst j
    rw [weights,if_pos rfl]
    exact lt_of_lt_of_le (pos (e a)) (single_le_sum (fun i _=>Nat.zero_le (w i)) (center_mem e a))
  · simpa [weights,eq] using pos (e j)

theorem total (w : I→ℕ) (e : J↪I) (a : J) : ∑j,weights w e a j=∑i,w i := by
  classical
  rw [←sum_erase_add _ _ (mem_univ a)]
  have out : (∑j∈univ.erase a,weights w e a j)=∑i∈(univ.erase a).map e,w i := by
    rw [sum_map]
    apply sum_congr rfl
    intro j hj
    simp [weights,(mem_erase.mp hj).1]
  rw [out,weights,if_pos rfl,add_comm]
  exact sum_sdiff (subset_univ ((univ.erase a).map e))

/-- A geometric no-jump test merges all source labels into the retained
representative and keeps the other weights, at the original angle threshold. -/
theorem fixed_merge [Nontrivial I] {c : I→Point} (ci : Function.Injective c)
    {w : I→ℕ} (wp : ∀i,0<w i) {δ : ℝ} (dp : 0<δ) (hit : π-δ∈attainable w c)
    (e : J↪I) (a : J) {q : J→ℕ} (Q : ∀j,Row (q j)) (front : Represents Q (c∘e))
    (back : Witnessed Q (c∘e)) (ht : 0≤(Q a).w 0 ∧ (Q a).w 0<π) (η : ℕ→ℝ)
    (wall : ∀j≤q a,Wall (univ.image c) ((mergedFiber e a).image c) ((Q a).w 0) ((Q a).w j) (η j))
    (fit : ∀j : Fin (q a),(Q a).w (j.val+1)-(Q a).w j+η j+η (j.val+1)<(((Q a).digits j δ:ℝ)+2)*δ) :
    π-δ ∈ attainable (weights w e a) (c∘e) := by
  classical
  obtain ⟨m,R,rf,rb⟩:=actual_rows c ci
  have data:=((fixed_centers_iff R ci rf rb wp _).mp hit).resolve_left (by linarith)
  have subtract : π-(π-δ)=δ := by ring
  rw [subtract] at data
  obtain ⟨θp,legal,old⟩:=data
  have qp : 0<q a := by
    by_contra! bad
    have h:=(Q a).period
    have hh:=congrArg (Q a).w (show q a=0 by omega)
    linarith [pi_pos]
  have fitsum : ∑i∈mergedFiber e a,w i≤2^score Q a δ := by
    apply weighted_cluster ci wp hit (mergedFiber e a) qp _ ht _ η (fun j=>(Q a).digits j δ) rfl (Q a).period wall (by linarith)
    simpa only [subtract] using fit
  apply gap_realization Q dp front back (positive wp e a) (ci.comp e.injective) θp
    (fun i j k ij ik jk=>legal _ _ _ (e.injective.ne ij) (e.injective.ne ik) (e.injective.ne jk))
  intro j
  by_cases eq : j=a
  · subst j
    apply (Nat.clog_le_iff_le_pow (by decide : 1<2)).mpr
    simpa [weights] using fitsum
  · have cap := (old (e j)).trans (retained_row R rf e Q back dp j)
    simpa [dim,weights,eq] using cap
end R64.Merge
#print axioms R64.Merge.total
#print axioms R64.Merge.fixed_merge
