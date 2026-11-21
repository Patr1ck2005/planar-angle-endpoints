import ExtremeCount

noncomputable section
namespace R90.Aperture
open JSP404 Real InnerProductGeometry R87.Diameter
open Finset

/-- Disjoint angular intervals of integral widths wᵢδ carry ∑wᵢ points
separated by δ on the full circle. Here the inputs are their center directions
and distances, so no ordering of the sites is required. -/
theorem weighted_circle {I : Type*} [Fintype I] (w : I→ℕ)
    (two : 2≤∑i,w i) {δ : ℝ} (dp : 0<δ) (room : ∀i,(w i:ℝ)*δ≤π)
    (u : I→Point) (nz : ∀i,u i≠0) (packing : ∀i j,i≠j→
      ((w i:ℝ)+(w j:ℝ))*δ/2≤angle (u i) (u j)) :
    ((∑i,w i:ℕ):ℝ)*δ≤2*π := by
  classical
  let J:=(i:I) × Fin (w i)
  choose t direction using fun i=>head_exists (nz i)
  let offset (p : J):=((p.2.val:ℝ)-((w p.1:ℝ)-1)/2)*δ
  let φ (p : J):=t p.1+offset p
  let v (p : J):=circleDirection (φ p)
  have V (p : J) : Head (v p) (φ p):=⟨1,by norm_num,by simp [v]⟩
  have O (p : J) : |offset p|≤((w p.1:ℝ)-1)*δ/2 := by
    have lower : (0:ℝ)≤p.2.val:=Nat.cast_nonneg _
    have upper : (p.2.val:ℝ)+1≤w p.1 := by exact_mod_cast p.2.isLt
    have l:=mul_le_mul_of_nonneg_right lower dp.le
    have h:=mul_le_mul_of_nonneg_right upper dp.le
    dsimp [offset];apply abs_le.mpr;constructor <;> nlinarith only [l,h]
  have dist (p : J) : angle (v p) (u p.1)≤((w p.1:ℝ)-1)*δ/2 := by
    have bound:=O p
    have span : |φ p-t p.1|≤π:=by
      dsimp [φ];rw [add_sub_cancel_left]
      nlinarith only [bound,room p.1,dp,pi_pos]
    rw [head_angle (V p) (direction p.1) span];simpa [φ] using bound
  have pair (p q : J) (ne : p≠q) : δ≤angle (v p) (v q) := by
    obtain ⟨i,a⟩:=p
    obtain ⟨j,b⟩:=q
    by_cases same : i=j
    · subst j
      have ab : a.val≠b.val:=by intro h;exact ne (congrArg (Sigma.mk i) (Fin.ext h))
      have val : φ ⟨i,a⟩-φ ⟨i,b⟩=((a.val:ℝ)-(b.val:ℝ))*δ:=by dsimp [φ,offset];ring
      have au : (a.val:ℝ)≤w i:=by exact_mod_cast a.isLt.le
      have bu : (b.val:ℝ)≤w i:=by exact_mod_cast b.isLt.le
      have lim : |φ ⟨i,a⟩-φ ⟨i,b⟩|≤π:=by
        rw [val,abs_mul,abs_of_pos dp]
        have abnd : |(a.val:ℝ)-(b.val:ℝ)|≤w i:=abs_le.mpr ⟨by linarith [Nat.cast_nonneg a.val (α:=ℝ)],by linarith [Nat.cast_nonneg b.val (α:=ℝ)]⟩
        exact (mul_le_mul_of_nonneg_right abnd dp.le).trans (room i)
      rw [head_angle (V _) (V _) lim,val,abs_mul,abs_of_pos dp]
      have one : 1≤|(a.val:ℝ)-(b.val:ℝ)|:=by
        rcases lt_or_gt_of_ne ab with h|h
        · have x : (a.val:ℝ)+1≤b.val:=by exact_mod_cast h
          exact (neg_le_abs _).trans' (by linarith)
        · have x : (b.val:ℝ)+1≤a.val:=by exact_mod_cast h
          exact (le_abs_self _).trans' (by linarith)
      simpa using mul_le_mul_of_nonneg_right one dp.le
    · have h:=packing i j same
      have a1:=dist ⟨i,a⟩;have b1:=dist ⟨j,b⟩
      change angle (v ⟨i,a⟩) (u i)≤_ at a1
      change angle (v ⟨j,b⟩) (u j)≤_ at b1
      rw [angle_comm (v ⟨i,a⟩) (u i)] at a1
      have one:=angle_le_angle_add_angle (u i) (v ⟨i,a⟩) (u j)
      have two:=angle_le_angle_add_angle (v ⟨i,a⟩) (v ⟨j,b⟩) (u j)
      change angle (u i) (v ⟨i,a⟩)≤((w i:ℝ)-1)*δ/2 at a1
      change angle (v ⟨j,b⟩) (u j)≤((w j:ℝ)-1)*δ/2 at b1
      nlinarith only [h,a1,b1,one,two]
  have sz : Fintype.card J=∑i,w i:=by simp [J,Fintype.card_sigma]
  let e:Fin (∑i,w i)≃J:=(Fintype.equivFinOfCardEq sz).symm
  apply Jsp404.circle_separation_bound (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation two (v ∘ e)
  · intro j zero
    change v (e j)=0 at zero
    have h:=norm_circleDirection (φ (e j))
    change ‖v (e j)‖=1 at h
    simp [zero] at h
  · intro i j ne;exact pair _ _ (e.injective.ne ne)

/-- A cone at each site containing all outgoing actual rays transfers the
per-site angular budgets to one ordinary inequality for the total weight. -/
theorem weighted_fans {I : Type*} [Fintype I] (c : I→Point) (w : I→ℕ)
    (two : 2≤∑i,w i) {δ : ℝ} (dp : 0<δ)
    (room : ∀i,(w i:ℝ)*δ≤π) (fans : ∀i,∃u:Point,u≠0 ∧
      ∀j,j≠i→angle u (c j-c i)≤(π-(w i:ℝ)*δ)/2) : ((∑i,w i:ℕ):ℝ)*δ≤2*π := by
  choose u nz rays using fans
  apply weighted_circle w two dp room u nz
  intro i j ne
  have l:=rays i j ne.symm
  have r:=rays j i ne
  have eq : angle (u j) (c j-c i)=π-angle (u j) (c i-c j) := by
    rw [show c j-c i= -(c i-c j) by abel,angle_neg_right]
  have h:=angle_le_angle_add_angle (u j) (u i) (c j-c i)
  rw [eq,angle_comm (u j) (u i)] at h
  nlinarith only [h,l,r]
end R90.Aperture
#print axioms R90.Aperture.weighted_circle
#print axioms R90.Aperture.weighted_fans
