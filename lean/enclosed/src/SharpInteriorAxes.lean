import WeightedSpectrum

noncomputable section
namespace R89.Sharp
open JSP404 Real InnerProductGeometry R55.WeightedCollision

def weights (W : ℕ) (i : Fin 4) : ℕ := if i=0 then W else 1

theorem weights_pos {W : ℕ} (wp : 0<W) : ∀i,0<weights W i := by
  intro i;unfold weights;split <;> omega

/-- Only the distinguished interior site carries microscopic axes. -/
theorem interior_axes {W : ℕ} (wp : 0<W) {δ : ℝ} (dp : 0<δ)
    (per : ((Nat.clog 2 W:ℝ)+3)*δ=π)
    {c : Fin 4→Point} (c0 : c 0=0) (c1 : c 1=circleDirection (-δ))
    (c2 : c 2= -circleDirection 0) (c3 : c 3=circleDirection δ)
    (ci : Function.Injective c) (mac : Macro c (π-δ)) :
    π-δ∈attainable (weights W) c := by
  let n:=Nat.clog 2 W
  change ((n:ℝ)+3)*δ=π at per
  have total : 3*δ≤π := by nlinarith [mul_nonneg (Nat.cast_nonneg n : (0:ℝ)≤n) dp.le]
  let a (j : ℕ) := ((j:ℝ)+2)*δ
  let v (i : Fin 4) (j : Fin (dim (weights W) i)):=circleDirection (a j.val)
  have site {i : Fin 4} (j : Fin (dim (weights W) i)) : i=0 := by
    by_contra ne
    have b:=j.isLt
    simp [dim,weights,ne] at b
  have index {i : Fin 4} (j : Fin (dim (weights W) i)) : j.val<n := by
    obtain rfl:=site j
    simpa [n,dim,weights] using j.isLt
  have range {j : ℕ} (small : j<n) : 2*δ≤a j ∧ a j≤π-2*δ := by
    have h : (j:ℝ)+1≤n:=by exact_mod_cast small
    have z:=mul_le_mul_of_nonneg_right h dp.le
    have l:=mul_nonneg (Nat.cast_nonneg j : (0:ℝ)≤j) dp.le
    dsimp [a];constructor <;> nlinarith only [per,z,l]
  have diff {j k : ℕ} (small : j<n) (also : k<n) (ne : j≠k) :
      δ≤|a j-a k| ∧ |a j-a k|≤π-δ := by
    obtain ⟨jl,jh⟩:=range small
    obtain ⟨kl,kh⟩:=range also
    refine ⟨?_,abs_le.mpr ⟨by linarith,by linarith⟩⟩
    rcases lt_or_gt_of_ne ne with lt|gt
    · have h : (j:ℝ)+1≤k:=by exact_mod_cast lt
      have p:=mul_le_mul_of_nonneg_right h dp.le
      apply (neg_le_abs _).trans';dsimp [a];linarith only [p]
    · have h : (k:ℝ)+1≤j:=by exact_mod_cast gt
      have p:=mul_le_mul_of_nonneg_right h dp.le
      apply (le_abs_self _).trans';dsimp [a];linarith only [p]
  apply admissible_mem (weights_pos wp) ci
  refine ⟨by linarith,mac,v,(fun _ _=>norm_circleDirection _),?_,?_⟩
  · intro i j k ne r s hr hs
    have d:=diff (index j) (index k) (Fin.val_ne_of_ne ne)
    exact signed_circleDirection_angle_le_of_separation dp.le d.1 d.2 _ _ hr hs
  · intro i j ne u r hr
    obtain rfl:=site u
    change angle (r • circleDirection (a u.val)) (c j-c 0)≤π-δ
    rw [c0,sub_zero]
    obtain ⟨lo,hi⟩:=range (index u)
    have cap {t : ℝ} (lb : -δ≤t) (ub : t≤δ) (s : ℝ) (hs : s= -1 ∨ s=1) :
        angle (r • circleDirection (a u.val)) (s • circleDirection t)≤π-δ := by
      apply signed_circleDirection_angle_le_of_separation dp.le _ _ _ _ hr hs
      · exact (le_abs_self _).trans' (by linarith)
      · exact abs_le.mpr ⟨by linarith,by linarith⟩
    fin_cases j
    · exact (ne rfl).elim
    · change angle _ (c 1)≤π-δ
      rw [c1];simpa using cap (t:= -δ) le_rfl (by linarith) 1 (Or.inr rfl)
    · change angle _ (c 2)≤π-δ
      rw [c2];simpa using cap (t:=0) (by linarith) dp.le (-1) (Or.inl rfl)
    · change angle _ (c 3)≤π-δ
      rw [c3];simpa using cap (t:=δ) (by linarith) le_rfl 1 (Or.inr rfl)
end R89.Sharp
#print axioms R89.Sharp.interior_axes
