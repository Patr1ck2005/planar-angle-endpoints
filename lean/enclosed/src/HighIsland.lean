import TwoIslands
noncomputable section
namespace R53.Islands
open Real JSP404 R51.Anchored R52.TwoAnchor

/-- If two disjoint isolated subsets each contain more than 2^k points, all remaining
points together count as one part, irrespective of their geometry. -/
theorem high {S F H : Finset Point} {a b : Point} {η : ℝ} (I : Island S F a η)
    (J : Island S H b η) (disj : Disjoint F H) {k : ℕ}
    (large : 5*2^k<S.card) (big : 2^k<F.card) (big' : 2^k<H.card) :
    ((k:ℝ)+3)*defect S≤π+4*η := by
  have bf : b∈S\F := Finset.mem_sdiff.mpr ⟨J.sub J.mem,Finset.disjoint_left.mp disj.symm J.mem⟩
  have ah : a∈S\H := Finset.mem_sdiff.mpr ⟨I.sub I.mem,Finset.disjoint_left.mp disj I.mem⟩
  by_cases huge : 2*2^k<F.card
  · linarith [oversize I ⟨b,bf⟩ huge,I.pos]
  by_cases huge' : 2*2^k<H.card
  · linarith [oversize J ⟨a,ah⟩ huge',J.pos]
  have card:=Finset.card_sdiff_add_card_eq_card (Finset.union_subset I.sub J.sub)
  rw [Finset.card_union_of_disjoint disj] at card
  have leftover : 2^k<(S\(F∪H)).card := by omega
  obtain ⟨t,dim⟩:=capacity big
  obtain ⟨s,dim'⟩:=capacity big'
  obtain ⟨_,dr⟩:=capacity leftover
  have dl : 0≤defect S := sub_nonneg.mpr (maxAngle_le_pi S)
  rcases three_budgets I J disj t s with x|y|z
  · nlinarith [mul_nonneg (sub_nonneg.mpr dim) dl]
  · nlinarith [mul_nonneg (sub_nonneg.mpr dim') dl]
  · nlinarith [mul_nonneg (sub_nonneg.mpr dr) dl,I.pos]

theorem high_stability {S F H : Finset Point} {a b : Point} {η : ℝ} (I : Island S F a η)
    (J : Island S H b η) (disj : Disjoint F H) {k : ℕ}
    (large : 5*2^k<S.card) (big : 2^k<F.card) (big' : 2^k<H.card)
    {ε : ℝ} (ang : maxAngle S≤π-π/((k:ℝ)+3)-ε) : ((k:ℝ)+3)*ε≤4*η := by
  let B:=(k:ℝ)+3
  have bp : 0<B := by dsimp [B];positivity
  have h : π/B+ε≤defect S := by dsimp [B,defect];linarith
  have h':=mul_le_mul_of_nonneg_left h bp.le
  rw [mul_add,show B*(π/B)=π by field_simp] at h'
  linarith [high I J disj large big big']

end R53.Islands
#print axioms R53.Islands.high
#print axioms R53.Islands.high_stability
