import DistinctPhysicalAxes

noncomputable section
namespace R95.Heavy
open JSP404 Real Finset InnerProductGeometry R54.GapTest R92.Tight R87.Diameter

/-- One axis at 120 degrees restricts every compatible projective line to
the same closed 60-degree window. -/
theorem window {x y : Point} {t : ℝ} (X : Bearing x t) (nz : y≠0)
    (cap : ∀s : ℝ,(s= -1 ∨ s=1)→angle (s • x) y≤2*π/3) :
    ∃a : ℝ,t+π/3≤a ∧ a≤t+2*π/3 ∧ Bearing y a := by
  obtain ⟨a,lo,hi,Y⟩:=lifted_polar y nz t
  have legal : ∀s : ℝ,(s= -1 ∨ s=1)→angle (s • x) y≤π-π/3:=by
    intro s hs;linarith only [cap s hs]
  have l:=apart X Y (abs_le.mpr ⟨by linarith,by linarith [pi_pos]⟩) legal
  have r:=apart (bearing_closes X) Y (abs_le.mpr ⟨by linarith [pi_pos],by linarith⟩) legal
  rw [abs_of_nonpos (by linarith)] at l
  rw [abs_of_nonneg (by linarith)] at r
  exact ⟨a,by linarith,by linarith,Y⟩

/-- Three distinct projective lines in a closed real window force a genuine
interior witness. The two boundary headings can accommodate at most two labels. -/
theorem interior_label {J : Type*} [Fintype J] (many : 3≤Fintype.card J)
    (a : J→ℝ) (inj : Function.Injective a) {l h : ℝ}
    (lo : ∀j,l≤a j) (hi : ∀j,a j≤h) : ∃j,l<a j ∧ a j<h := by
  classical
  by_contra! none
  have cover : univ.image a⊆({l,h}:Finset ℝ):=by
    intro x hx
    obtain ⟨j,_,rfl⟩:=mem_image.mp hx
    rcases eq_or_lt_of_le (lo j) with e|lt
    · simp [e]
    · simp [(hi j).antisymm (none j lt)]
  have count:=card_le_card cover
  rw [card_image_of_injective _ inj,card_univ] at count
  have small : ({l,h}:Finset ℝ).card≤2:= (card_insert_le ..).trans (by simp)
  omega

/-- A legal family of signed chords on distinct lines in the one-axis
window shares an orientation. An interior witness prevents either antipodal
choice from occurring, even at exact threshold. -/
theorem narrow_fan {J : Type*} [Fintype J] {u : J→Point} {a : J→ℝ} {t : ℝ}
    (lo : ∀j,t+π/3≤a j) (hi : ∀j,a j≤t+2*π/3)
    (lines : ∀j,Bearing (u j) (a j)) (p : J) (pl : t+π/3<a p) (pr : a p<t+2*π/3)
    (legal : ∀j,j≠p→angle (u j) (u p)≤2*π/3) :
    ∃v : Point,v≠0 ∧ ∀j,angle v (u j)≤π/6 := by
  choose r rp e sign eq using lines
  have ang (j : J) : angle (circleDirection (a j)) (circleDirection (a p))=|a j-a p| :=by
    apply head_angle (U:=⟨1,by norm_num,by simp⟩) (V:=⟨1,by norm_num,by simp⟩)
    apply abs_le.mpr
    constructor <;> linarith [lo j,hi j,pi_pos]
  have common (j : J) : e j=e p :=by
    by_contra diff
    have ne : j≠p:=by intro h;exact diff (congrArg e h)
    have cap:=legal j ne
    rw [eq j,eq p,angle_smul_left_of_pos _ _ (rp j),angle_smul_right_of_pos _ _ (rp p)] at cap
    have small : |a j-a p|<π/3:=abs_lt.mpr ⟨by linarith [lo j],by linarith [hi j]⟩
    rcases sign j with hj|hj <;> rcases sign p with hp|hp <;>
      simp only [hj,hp,one_smul,neg_one_smul,angle_neg_left,angle_neg_right,ang] at diff cap <;>
      first | exact diff trivial | linarith
  let m:=t+π/2
  let v:=circleDirection m
  have nz : v≠0:=by intro z;have h:=norm_circleDirection m;change ‖v‖=1 at h;simp [z] at h
  refine ⟨e p • v,by rcases sign p with h|h <;> simp [h,nz],?_⟩
  intro j
  have absbd : |m-a j|≤π/6:=abs_le.mpr ⟨by dsimp [m];linarith [hi j],by dsimp [m];linarith [lo j]⟩
  have angle_eq : angle v (circleDirection (a j))=|m-a j|:=head_angle
    (show Head v m from ⟨1,by norm_num,by simp [v]⟩)
    (show Head (circleDirection (a j)) (a j) from ⟨1,by norm_num,by simp⟩)
    (absbd.trans (by linarith [pi_pos]))
  rw [eq j,angle_smul_right_of_pos _ _ (rp j),common j]
  rcases sign p with hj|hj <;> simp only [hj,one_smul,neg_one_smul,angle_neg_left,angle_neg_right,angle_eq] <;> linarith

end R95.Heavy
#print axioms R95.Heavy.window
#print axioms R95.Heavy.interior_label
#print axioms R95.Heavy.narrow_fan
