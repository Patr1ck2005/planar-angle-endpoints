import FourSeparated
noncomputable section
namespace R52.FourSeparated
open Real JSP404 R52.TwoAnchor

def lowPhi (k : ℕ) := π/(2*(2*(k:ℝ)+5))
def lowEta (k : ℕ) (ε : ℝ) := min (π/4) ((2*(k:ℝ)+5)*ε/8)
def highPhi (k : ℕ) (ε : ℝ) := min (π/4) (((k:ℝ)+3)*ε/2)
def highEta (k : ℕ) (ε : ℝ) := min (π/4) (((k:ℝ)+3)*ε/8)

private theorem clip {x : ℝ} (xp : 0<x) : 0<min (π/4) x ∧ min (π/4) x<π/2 :=
  ⟨lt_min (by positivity) xp, lt_of_le_of_lt (min_le_left _ _) (by linarith [pi_pos])⟩

theorem lower_separation (k : ℕ) {ε : ℝ} (ep : 0<ε) :
    0<lowPhi k ∧ lowPhi k<π ∧ 0<lowEta k ε ∧ lowEta k ε<π/2 := by
  have den : 0<2*(k:ℝ)+5 := by positivity
  refine ⟨div_pos pi_pos (by positivity),?_,clip (by positivity : 0<(2*(k:ℝ)+5)*ε/8)⟩
  apply (div_lt_iff₀ (by positivity : 0<2*(2*(k:ℝ)+5))).mpr
  nlinarith [pi_pos,mul_nonneg (Nat.cast_nonneg k) pi_pos.le]

theorem upper_separation (k : ℕ) {ε : ℝ} (ep : 0<ε) :
    0<highPhi k ε ∧ highPhi k ε<π ∧ 0<highEta k ε ∧ highEta k ε<π/2 := by
  have p:=clip (by positivity : 0<((k:ℝ)+3)*ε/2)
  exact ⟨p.1,p.2.trans (by linarith [pi_pos]),clip (by positivity : 0<((k:ℝ)+3)*ε/8)⟩

private theorem sin_ok {y : ℝ} (lo : 0<y) (hi : y<π/2) :
    0<sin y ∧ sin y<1 ∧ arcsin (sin y)=y := by
  refine ⟨sin_pos_of_pos_of_lt_pi lo (hi.trans (by linarith [pi_pos])),?_,arcsin_sin (by linarith [pi_pos]) hi.le⟩
  simpa using Real.sin_lt_sin_of_lt_of_le_pi_div_two (show -(π/2)≤y by linarith [pi_pos]) (le_refl (π/2)) hi

theorem low_margin {S : Finset Point} {p q : Point} (hp : p∈S) (hq : q∈S) (pq : p≠q)
    {k : ℕ} (big : 4*2^k<S.card) {ε : ℝ} (ep : 0<ε)
    (ang : maxAngle S≤π-2*π/(2*(k:ℝ)+5)-ε) :
    Four S p q (sin (lowPhi k)*dist p q) (sin (lowEta k ε)*(sin (lowPhi k)*dist p q)) := by
  obtain ⟨p0,p1,e0,e1⟩:=lower_separation k ep
  obtain ⟨s0,s1,eq⟩:=sin_ok e0 e1
  let a:=2*(k:ℝ)+5
  let b:=(k:ℝ)+3
  have ap : 0<a := by dsimp [a];positivity
  have bp : 0<b := by dsimp [b];positivity
  have h : 2*π/a+ε≤defect S := by dsimp [a,defect];linarith
  have base : a*(2*π/a)=2*π := by field_simp
  have split : b*(2*π/a)=π+π/a := by dsimp [a,b];field_simp;ring
  have strong : 2*π+a*ε≤a*defect S := by nlinarith [mul_le_mul_of_nonneg_left h ap.le]
  have weak : π+π/a+b*ε≤b*defect S := by nlinarith [mul_le_mul_of_nonneg_left h bp.le]
  have pval : 2*lowPhi k=π/a := by dsimp [lowPhi,a];field_simp
  have cap : lowEta k ε≤a*ε/8 := min_le_right _ _
  have rel : a*ε≤2*b*ε := by dsimp [a,b];nlinarith
  apply lower_half_four hp hq pq big p0 p1 s0.le s1
  · change _≤b*defect S
    linarith [mul_pos bp ep]
  · rw [eq]
    change _<b*defect S
    linarith [div_pos pi_pos ap]
  · rw [eq]
    change _<a*defect S
    linarith [mul_pos ap ep]

theorem high_margin {S : Finset Point} {p q : Point} (hp : p∈S) (hq : q∈S) (pq : p≠q)
    {k : ℕ} (big : 5*2^k<S.card) {ε : ℝ} (ep : 0<ε)
    (ang : maxAngle S≤π-π/((k:ℝ)+3)-ε) :
    Four S p q (sin (highPhi k ε)*dist p q) (sin (highEta k ε)*(sin (highPhi k ε)*dist p q)) := by
  obtain ⟨p0,p1,e0,e1⟩:=upper_separation k ep
  obtain ⟨s0,s1,eq⟩:=sin_ok e0 e1
  let b:=(k:ℝ)+3
  have bp : 0<b := by dsimp [b];positivity
  have h : π/b+ε≤defect S := by dsimp [b,defect];linarith
  have base : b*(π/b)=π := by field_simp
  have weak : π+b*ε≤b*defect S := by nlinarith [mul_le_mul_of_nonneg_left h bp.le]
  have pc : highPhi k ε≤b*ε/2 := min_le_right _ _
  have ec : highEta k ε≤b*ε/8 := min_le_right _ _
  apply upper_half_four hp hq pq big p0 p1 s0.le s1
  · change _≤b*defect S;linarith
  · rw [eq];change _<b*defect S;linarith [mul_pos bp ep]

end R52.FourSeparated
#print axioms R52.FourSeparated.low_margin
#print axioms R52.FourSeparated.high_margin
