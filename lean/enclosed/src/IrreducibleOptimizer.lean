import ContractionStaircase
import GlobalBoundary
import Jsp000404.UpperBound
noncomputable section
namespace R64.Merge
open JSP404 Real R54.Profile R55.WeightedCollision

/-- No proper geometric contraction to two or more retained points passes the local gap test. -/
def Irreducible (δ : ℝ) (S : Shape) := ∀ {h : ℕ},2≤h → h<S.size →
  ∀ (e : Fin h↪Fin S.size) (a : Fin h),¬Nonempty (Test δ S e a)

private theorem alpha_below_pi {N : ℕ} (many : 3≤N) : alpha N<π := by
  apply (Jsp404.alpha_le_alphaN N many).trans_lt
  by_cases four : 4≤N
  · exact Jsp404.alphaN_lt_pi four
  · have eq : N=3 := by omega
    rw [eq]
    change π/3<π
    linarith [pi_pos]

/-- The ordinary extremal value is attained by a profile with no allowable
proper contraction. The weights need not be prescribed in advance. -/
theorem irreducible_optimizer {N : ℕ} (many : 3≤N) :
    ∃ S : Shape,(∑i,S.w i)=N ∧ alpha N∈attainable S.w S.c ∧ Irreducible (π-alpha N) S := by
  classical
  obtain ⟨m,two,_,c,ci,_,w,wp,sz,_,ad⟩:=realized_minimum many
  let P (k : ℕ) := ∃S : Shape,S.size=k ∧ (∑i,S.w i)=N ∧ alpha N∈attainable S.w S.c
  have someK : ∃k,P k := by
    let S : Shape:=⟨m,two,c,ci,w,wp⟩
    exact ⟨m,S,rfl,sz,(fixed_profile wp (fin_other two) ci).mpr ad⟩
  obtain ⟨S,size,cnt,hit⟩:=Nat.find_spec someK
  refine ⟨S,cnt,hit,?_⟩
  intro h htwo less e a possible
  obtain ⟨test⟩:=possible
  letI : Nontrivial (Fin S.size):=Fin.nontrivial_iff_two_le.mpr S.two
  have delta : 0<π-alpha N:=sub_pos.mpr (alpha_below_pi many)
  have original : π-(π-alpha N)∈attainable S.w S.c := by simpa only [sub_sub_cancel] using hit
  have moved:=fixed_merge S.ci S.wp delta original e a test.Q test.front test.back test.initial test.error test.wall test.fit
  let B:=collapse S htwo e a
  rw [sub_sub_cancel] at moved
  have smaller : P h := by
    refine ⟨B,rfl,(total S.w e a).trans cnt,?_⟩
    exact moved
  exact (not_le_of_gt (less.trans_eq size)) (Nat.find_min' someK smaller)

/-- Exact reduction of the unrestricted problem to all nonconcyclic irreducible
profiles of at least five centers, at every original cardinality. -/
theorem unrestricted_iff_irreducible {N : ℕ} (many : 3≤N) :
    alpha N=Jsp404.alphaN N ↔
    ∀ S : Shape, 5≤S.size → ¬R58.CircleModel.OnCircle S.c → (∑i,S.w i)=N →
    ∀θ∈attainable S.w S.c,Irreducible (π-θ) S → Jsp404.alphaN N≤θ := by
  constructor
  · intro solved S _ _ sz θ hit _
    have b:=alpha_bound (sz ▸ many) hit
    simpa only [sz,solved] using b
  · intro all
    obtain ⟨S,sz,hit,no⟩:=irreducible_optimizer many
    apply le_antisymm (Jsp404.alpha_le_alphaN N many)
    have dp:=sub_pos.mpr (alpha_below_pi many)
    have fromTerminal (cert : Reduces (π-alpha N) S) : Jsp404.alphaN N≤alpha N := by
      have h:=lower_of_chain dp S cert (sz ▸ many) (by simpa only [sub_sub_cancel] using hit)
      simpa only [sub_sub_cancel,sz] using h
    by_cases four : S.size≤4
    · exact fromTerminal (.terminal S four)
    by_cases circle : R58.CircleModel.OnCircle S.c
    · exact fromTerminal (.cyclic S circle)
    exact all S (by omega) circle sz _ hit no
end R64.Merge
#print axioms R64.Merge.irreducible_optimizer
#print axioms R64.Merge.unrestricted_iff_irreducible
