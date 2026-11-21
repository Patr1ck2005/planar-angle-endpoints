import FiveAperture
import FiveCoordinates
noncomputable section
namespace R64.Five
open Real

def defect (n : ℕ) : ℝ := π / ((n:ℝ)+3/4)

theorem defect_pos (n : ℕ) : 0 < defect n := div_pos pi_pos (by positivity)

theorem period (n : ℕ) : π=((n:ℝ)+3/4)*defect n := by
  unfold defect
  field_simp

theorem defect_small {n : ℕ} (hn : 16≤n) : defect n≤1/4 := by
  have rc : (16:ℝ)≤n := by exact_mod_cast hn
  apply (div_le_iff₀ (by positivity : 0 < (n:ℝ)+3/4)).mpr
  linarith [pi_le_four]

def wall (l : ℝ) (i : Fin 5) (j : Fin 4) := heading l i (seq i j)
def span (l : ℝ) (i : Fin 5) := wall l i 3-wall l i 0

private theorem liftq {x y : ℚ} (h : x≤y) : (x:ℝ)≤(y:ℝ) := by exact_mod_cast h

theorem real_extremes (i : Fin 5) :
    -(17/16:ℝ)≤(low i:ℝ) ∧ (low i:ℝ)≤0 ∧ 0≤(high i:ℝ) ∧ (high i:ℝ)≤17/16 ∧
    17/16≤(high i:ℝ)-(low i:ℝ) ∧ (high i:ℝ)-(low i:ℝ)≤7/4 := by
  obtain ⟨a,b,c,d,e,f⟩:=extremes i
  exact ⟨by simpa using liftq a,by simpa using liftq b,by simpa using liftq c,
    by simpa using liftq d,by simpa using liftq e,by simpa using liftq f⟩

theorem wall_mono {l : ℝ} (lp : 0≤l) (i : Fin 5) {j k : Fin 4} (h : j≤k) :
    wall l i j≤wall l i k := by
  apply arctan_le_arctan_iff.mpr
  apply mul_le_mul_of_nonneg_left _ lp
  exact_mod_cast seq_mono i j k h

theorem span_bounds {l : ℝ} (lp : 0 < l) (sm : l≤1/4) (i : Fin 5) :
    l < span l i ∧ span l i≤(7/4)*l := by
  obtain ⟨lo,az,bz,hi,spread,cap⟩:=real_extremes i
  change l < arctan (l*(high i:ℝ))-arctan (l*(low i:ℝ)) ∧ _ ≤ _
  refine ⟨separated lp sm lo az bz hi spread,?_⟩
  change arctan (l*(high i:ℝ))-arctan (l*(low i:ℝ))≤_
  have up:=atan_upper (mul_nonneg lp.le bz)
    (by nlinarith only [mul_le_mul_of_nonneg_left hi lp.le,sm])
  have lower : -(l*(low i:ℝ))≤1 := by nlinarith only [mul_le_mul_of_nonneg_left lo lp.le,sm]
  have down:=atan_upper (u:= -(l*(low i:ℝ))) (neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos lp.le az)) lower
  rw [arctan_neg] at down
  nlinarith only [up,down,mul_le_mul_of_nonneg_left cap lp.le]

theorem head_bounds {l : ℝ} (lp : 0≤l) {i j : Fin 5} (ne : i≠j) :
    wall l i 0≤heading l i j ∧ heading l i j≤wall l i 3 := by
  obtain ⟨k,rfl⟩:=seq_cover i j ne
  exact ⟨wall_mono lp i (Fin.zero_le k),wall_mono lp i (show k≤3 by omega)⟩

theorem head_apart {l : ℝ} (lp : 0 < l) (sm : l≤1/4) {i j k : Fin 5} (opp : opposed i j k) :
    l < |heading l i j-heading l i k| := by
  obtain ⟨lo,_,_,hi,_,_⟩:=real_extremes i
  have bound (a : Fin 5) (ne : i≠a) : -(17/16:ℝ)≤(slope i a:ℝ) ∧ (slope i a:ℝ)≤17/16 := by
    have cc : (low i:ℝ)≤(slope i a:ℝ) ∧ (slope i a:ℝ)≤(high i:ℝ) := by exact_mod_cast slope_bound i a ne
    exact ⟨lo.trans cc.1,cc.2.trans hi⟩
  have ij : i≠j := by rcases opp with h|h <;> omega
  have ik : i≠k := by rcases opp with h|h <;> omega
  rcases opposite_slopes i j k opp with ⟨a,b,c⟩|⟨a,b,c⟩
  · have d:=separated lp sm (bound j ij).1 (by exact_mod_cast a) (by exact_mod_cast b)
      (bound k ik).2 (by simpa using liftq c)
    change l < |arctan _-arctan _|
    exact d.trans_le (by rw [abs_sub_comm];exact le_abs_self _)
  · have d:=separated lp sm (bound k ik).1 (by exact_mod_cast a) (by exact_mod_cast b)
      (bound j ij).2 (by simpa using liftq c)
    exact d.trans_le (le_abs_self _)

#print axioms span_bounds
#print axioms head_apart
end R64.Five