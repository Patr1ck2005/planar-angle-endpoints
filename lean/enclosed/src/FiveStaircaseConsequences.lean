import FivePhysicalReduction
import CriticalCenters
noncomputable section
namespace R67.FiveConclusion
open Real JSP404 R55.WeightedCollision R54.GapTest R56.Windows R67.Board
/-- All cap values obtainable at no more than five distinct macroscopic sites. -/
def scores (N : ℕ) : Set ℝ := {θ | ∃ k : ℕ,2≤k ∧ k≤5 ∧ ∃ c : Fin k→Point,Function.Injective c ∧
  ∃w : Fin k→ℕ,(∀i,0<w i) ∧ (∑i,w i)=N ∧ θ∈attainable w c}

theorem sharp_of_law (law : FiniteBoardLaw) {N : ℕ} (ge : 3≤N) : IsLeast (scores N) (Jsp404.alphaN N) := by
  constructor
  · obtain ⟨k,two,c,ci,circle,w,wp,sz,hit⟩:=(R59.Concyclic.full_staircase ge).1
    by_cases small:k≤5
    · exact ⟨k,two,small,c,ci,w,wp,sz,hit⟩
    · have count:=Finset.sum_le_sum (s:=Finset.univ) (fun i _=>show 1≤w i from wp i)
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one,sz] at count
      have pos:=sub_pos.mpr (Jsp404.alphaN_lt_pi (show 4≤N by omega))
      have lifted : π-(π-Jsp404.alphaN N)∈attainable w c := by simpa using hit
      obtain ⟨h,e,v,lo,hi,le,eq,att⟩:=R58.CircleModel.reduce_to_four (by simpa using (show 3≤k by omega)) c ci circle wp pos lifted
      exact ⟨h,by omega,by omega,(fun i=>c (e i)),ci.comp e.injective,v,fun i=>(wp _).trans_le (le i),eq.trans sz,by simpa only [sub_sub_cancel] using att⟩
  · rintro θ ⟨k,two,sm,c,ci,w,wp,sz,att⟩
    by_cases four:k≤4
    · have val:=(R53.FourCover.full_staircase (sz ▸ ge)).2 (R59.Concyclic.four_scores two four c ci wp att)
      simpa only [sz] using val
    · have eq:k=5:=by omega
      subst k
      simpa only [sz] using five_of_finite law ci w wp att

/-- For unrestricted ordinary N, only nonconcyclic supports of six or more
centers that are minimal under every proper retained subconfiguration remain. -/
theorem six_of_law (law : FiniteBoardLaw) {N : ℕ} (ge : 3≤N) :
    alpha N=Jsp404.alphaN N ↔
      ∀{k : ℕ},6≤k→k≤N→∀(c : Fin k→Point),Function.Injective c→
      ¬R58.CircleModel.OnCircle c→∀θ : ℝ,0≤θ→θ<π→Macro c θ→
      (∃m : Fin k→ℕ,∃R : ∀i,Row (m i),Represents R c ∧ Witnessed R c ∧ N≤R65.Retention.capacity R θ)→
      R65.Retention.Critical c N θ→Jsp404.alphaN N≤θ := by
  rw [R65.Retention.unrestricted_iff ge]
  constructor
  · intro h k six;exact h (by omega)
  · intro all k five small c ci circle θ pos lt mac system critical
    by_cases six : 6≤k
    · exact all six small c ci circle θ pos lt mac system critical
    · have eq:k=5:=by omega
      subst k
      obtain ⟨m,R,front,back,room⟩:=system
      obtain ⟨w,wp,sz,att⟩:=(R65.Retention.positive_mass_iff ci R front back pos lt mac N).mpr ⟨by simpa using small,room⟩
      simpa only [sz] using five_of_finite law ci w wp att
#print axioms sharp_of_law
#print axioms six_of_law
end R67.FiveConclusion
