import IteratedMerge
import AllConcyclic
noncomputable section
namespace R64.Merge
open Real JSP404 R55.WeightedCollision

/-- The observed score itself specifies the clearance used by the geometric tests. -/
def scores (N : ℕ) : Set ℝ := {θ | ∃S : Shape,(∑i,S.w i)=N ∧ θ∈attainable S.w S.c ∧ Reduces (π-θ) S}

/-- The exact printed staircase for arbitrary-depth finite geometric contractions. -/
theorem staircase {N : ℕ} (many : 3≤N) : IsLeast (scores N) (Jsp404.alphaN N) := by
  constructor
  · obtain ⟨k,two,c,ci,circle,w,pos,size,hit⟩:=(R59.Concyclic.full_staircase many).1
    let S : Shape:=⟨k,two,c,ci,w,pos⟩
    exact ⟨S,size,hit,Reduces.cyclic S circle⟩
  · rintro θ ⟨S,size,hit,chain⟩
    by_cases high : π≤θ
    · by_cases four : 4≤N
      · exact (Jsp404.alphaN_lt_pi four).le.trans high
      · have three : N=3 := by omega
        rw [three]
        change π/3≤θ
        linarith [pi_pos]
    have revertAngle : π-(π-θ)=θ := by ring
    have a:=lower_of_chain (sub_pos.mpr (lt_of_not_ge high)) S chain (size ▸ many) (by simpa only [revertAngle] using hit)
    simpa only [size,revertAngle] using a
end R64.Merge
#print axioms R64.Merge.staircase
