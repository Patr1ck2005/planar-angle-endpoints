import ClusterCorners

noncomputable section
namespace R52.TwoAnchor
open Real JSP404 R51.Anchored

def ConeBound {S : Finset Point} {a b c : Point} (A : Corner S a b c) (η : ℝ) :=
  A.eL ≤ η ∧ A.eR ≤ η

private theorem budget_info {h : ℕ} {F : Finset Point} (large : 2^h < F.card) :
    2 ≤ F.card ∧ (h:ℝ)+1 ≤ bits F := by
  have one : 0 < (2:ℕ)^h := by positivity
  have dim : h < Nat.clog 2 F.card :=
    lt_of_not_ge (fun z => (Nat.not_lt_of_ge ((Nat.clog_le_iff_le_pow (by decide : 1<2)).mp z)) large)
  exact ⟨by omega, by exact_mod_cast Nat.succ_le_of_lt dim⟩

private theorem err {S : Finset Point} {a b c : Point} {A : Corner S a b c} {η : ℝ}
    (E : ConeBound A η) : A.error ≤ 2*η := by
  dsimp [Corner.error]; linarith [E.1,E.2]

private theorem single_large {S : Finset Point} {a b c : Point} (A : Corner S a b c)
    {k : ℕ} {η : ℝ} (E : ConeBound A η) (big : 2*(2^k) < A.points.card) :
    ((k:ℝ)+3)*defect S ≤ π+4*η := by
  have big' : 2^(k+1)<A.points.card := by simpa [pow_succ,Nat.mul_comm] using big
  obtain ⟨two,dim⟩ := budget_info big'
  have h := anchored_budget A.sub two A.left A.outsideL
    (sub_ne_zero.mpr (fun z => A.outsideL (z.symm ▸ A.middle)) : b-a≠0) A.posL A.coneL
  have dl : 0≤defect S := sub_nonneg.mpr (maxAngle_le_pi S)
  push_cast at dim
  change (bits A.points+1)*defect S≤π+2*A.eL at h
  nlinarith [mul_nonneg (sub_nonneg.mpr dim) dl,E.1,A.posL]

private theorem pair_large {S : Finset Point} {a b c : Point} (A : Corner S a b c) (B : Corner S b c a)
    {k : ℕ} {η : ℝ} (E : ConeBound A η) (G : ConeBound B η)
    (big : 2^k<A.points.card) (big' : 2^k<B.points.card) :
    ((k:ℝ)+3)*defect S≤π+4*η ∨ (2*(k:ℝ)+5)*defect S≤2*π+4*η := by
  obtain ⟨a2,ad⟩ := budget_info big
  obtain ⟨b2,bd⟩ := budget_info big'
  have dl : 0≤defect S := sub_nonneg.mpr (maxAngle_le_pi S)
  have ca := mul_nonneg (sub_nonneg.mpr ad) dl
  have cb := mul_nonneg (sub_nonneg.mpr bd) dl
  rcases two_corners A B a2 b2 with x|x|x
  · left; nlinarith [err E]
  · left; nlinarith [err G]
  · right; nlinarith [err E,err G]

/-- Uniform three-cluster bound when each cloud has more than 2^k points. -/
theorem balanced {S : Finset Point} {a b c : Point} (A : Corner S a b c) (B : Corner S b c a)
    (C : Corner S c a b) {k : ℕ} {η : ℝ} (E : ConeBound A η) (G : ConeBound B η)
    (H : ConeBound C η) (acard : 2^k<A.points.card) (bcard : 2^k<B.points.card)
    (ccard : 2^k<C.points.card) : ((k:ℝ)+3)*defect S≤π+4*η := by
  obtain ⟨a2,ad⟩ := budget_info acard
  obtain ⟨b2,bd⟩ := budget_info bcard
  obtain ⟨c2,cd⟩ := budget_info ccard
  have dl : 0≤defect S := sub_nonneg.mpr (maxAngle_le_pi S)
  have ca := mul_nonneg (sub_nonneg.mpr ad) dl
  have cb := mul_nonneg (sub_nonneg.mpr bd) dl
  have cc := mul_nonneg (sub_nonneg.mpr cd) dl
  have epos := A.posL.trans E.1
  rcases three_corners A B C a2 b2 c2 with x|x|x|x
  · nlinarith [err E]
  · nlinarith [err G]
  · nlinarith [err H]
  · nlinarith [err E,err G,err H,mul_nonneg (Nat.cast_nonneg k : 0≤(k:ℝ)) dl]

/-- Applies in particular to a partition of the whole ordinary configuration.
The proof also works directly with three subcloud cardinalities. -/
theorem lower_half {S : Finset Point} {a b c : Point} (A : Corner S a b c) (B : Corner S b c a)
    (C : Corner S c a b) {k : ℕ} {η : ℝ} (E : ConeBound A η) (G : ConeBound B η)
    (H : ConeBound C η) (total : 4*2^k < A.points.card+B.points.card+C.points.card) :
    ((k:ℝ)+3)*defect S≤π+4*η ∨ (2*(k:ℝ)+5)*defect S≤2*π+4*η := by
  by_cases x : 2*2^k<A.points.card
  · exact Or.inl (single_large A E x)
  by_cases y : 2*2^k<B.points.card
  · exact Or.inl (single_large B G y)
  by_cases z : 2*2^k<C.points.card
  · exact Or.inl (single_large C H z)
  by_cases u : 2^k<A.points.card
  · by_cases v : 2^k<B.points.card
    · exact pair_large A B E G u v
    · exact pair_large C A H E (by omega) u
  · exact pair_large B C G H (by omega) (by omega)

/-- A three-cloud partition containing more than 5 times a power of two. -/
theorem upper_half {S : Finset Point} {a b c : Point} (A : Corner S a b c) (B : Corner S b c a)
    (C : Corner S c a b) {k : ℕ} {η : ℝ} (E : ConeBound A η) (G : ConeBound B η)
    (H : ConeBound C η) (total : 5*2^k < A.points.card+B.points.card+C.points.card) :
    ((k:ℝ)+3)*defect S≤π+4*η := by
  by_cases x : 2*2^k<A.points.card
  · exact single_large A E x
  by_cases y : 2*2^k<B.points.card
  · exact single_large B G y
  by_cases z : 2*2^k<C.points.card
  · exact single_large C H z
  exact balanced A B C E G H (by omega) (by omega) (by omega)

end R52.TwoAnchor
#print axioms R52.TwoAnchor.balanced
#print axioms R52.TwoAnchor.lower_half
#print axioms R52.TwoAnchor.upper_half
