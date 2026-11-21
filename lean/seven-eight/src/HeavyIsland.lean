import Reciprocal
noncomputable section
namespace R53.Islands
open Real JSP404 R51.Anchored R52.TwoAnchor

theorem capacity {h : ℕ} {F : Finset Point} (big : 2^h<F.card) :
    2≤F.card ∧ (h:ℝ)+1≤bits F := by
  have one : 0<(2:ℕ)^h := by positivity
  have dim : h<Nat.clog 2 F.card :=
    lt_of_not_ge (fun z=>(Nat.not_lt_of_ge ((Nat.clog_le_iff_le_pow (by decide : 1<2)).mp z)) big)
  exact ⟨by omega, by exact_mod_cast Nat.succ_le_of_lt dim⟩

theorem oversize {S F : Finset Point} {a : Point} {η : ℝ} (I : Island S F a η)
    (out : (S\F).Nonempty) {k : ℕ} (big : 2*2^k<F.card) :
    ((k:ℝ)+3)*defect S≤π+2*η := by
  obtain ⟨p,hp⟩:=out
  have pow : 2^(k+1)<F.card := by simpa [pow_succ,Nat.mul_comm] using big
  obtain ⟨two,dim⟩:=capacity pow
  push_cast at dim
  have dl : 0≤defect S := sub_nonneg.mpr (maxAngle_le_pi S)
  nlinarith [I.one two hp,mul_nonneg (sub_nonneg.mpr dim) dl]

/-- For a low staircase step only one large cluster needs to be isolated. The rest of
the configuration may be distributed arbitrarily, including on comparable scales. -/
theorem heavy {S F : Finset Point} {a : Point} {η : ℝ} (I : Island S F a η)
    (out : (S\F).Nonempty) {k : ℕ} (large : 4*2^k<S.card) (big : 2^k<F.card) :
    ((k:ℝ)+3)*defect S≤π+4*η ∨ (2*(k:ℝ)+5)*defect S≤2*π+2*η := by
  by_cases huge : 2*2^k<F.card
  · left;linarith [oversize I out huge,I.pos]
  have complement : (S\F).card+F.card=S.card := Finset.card_sdiff_add_card_eq_card I.sub
  have pow : 2^(k+1)<(S\F).card := by rw [pow_succ];omega
  obtain ⟨two,dim⟩:=capacity big
  obtain ⟨other,dim'⟩:=capacity pow
  push_cast at dim'
  have dl : 0≤defect S := sub_nonneg.mpr (maxAngle_le_pi S)
  have c:=mul_nonneg (sub_nonneg.mpr dim) dl
  have d:=mul_nonneg (sub_nonneg.mpr dim') dl
  rcases reciprocal I two other with x|y
  · left;nlinarith
  · right;nlinarith

/-- A deficit ε below the proposed low step forces a positive aperture for *every*
proper subcloud of more than 2^k points. Equivalently, such a cloud cannot collapse. -/
theorem low_stability {S F : Finset Point} {a : Point} {η : ℝ} (I : Island S F a η)
    (out : (S\F).Nonempty) {k : ℕ} (large : 4*2^k<S.card) (big : 2^k<F.card)
    {ε : ℝ} (ep : 0≤ε) (ang : maxAngle S≤π-2*π/(2*(k:ℝ)+5)-ε) :
    ((k:ℝ)+3)*ε≤4*η := by
  let A:=2*(k:ℝ)+5
  let B:=(k:ℝ)+3
  have ap : 0<A := by dsimp [A];positivity
  have bp : 0<B := by dsimp [B];positivity
  have h : 2*π/A+ε≤defect S := by dsimp [A,defect];linarith
  have t : A*(2*π/A)=2*π := by field_simp
  have u : B*(2*π/A)=π+π/A := by dsimp [A,B];field_simp;ring
  rcases heavy I out large big with x|y
  · change B*defect S≤_ at x
    change B*ε≤_
    have h' := mul_le_mul_of_nonneg_left h bp.le
    rw [mul_add,u] at h'
    linarith [div_pos pi_pos ap]
  · change A*defect S≤_ at y
    have h' := mul_le_mul_of_nonneg_left h ap.le
    rw [mul_add,t] at h'
    have diff : B*ε≤A*ε := by apply mul_le_mul_of_nonneg_right _ ep; dsimp [A,B];linarith [(Nat.cast_nonneg k : 0≤(k:ℝ))]
    change B*ε≤_
    linarith [I.pos]

end R53.Islands
#print axioms R53.Islands.oversize
#print axioms R53.Islands.heavy
#print axioms R53.Islands.low_stability
