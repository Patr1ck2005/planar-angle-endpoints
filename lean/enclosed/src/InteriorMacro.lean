import WeightedConstruction
import JSP404.EquallySpacedDirections
import Mathlib.Analysis.Convex.Hull

noncomputable section
open Real JSP404 InnerProductGeometry
namespace R90.Interior
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

/-- O, the lower ray A, the negative horizontal ray B, and the upper ray C. -/
def c (δ : ℝ) : Fin 4 → Point :=
  ![0, circleDirection (-δ), -circleDirection 0, circleDirection δ]

private theorem sin_cos {δ : ℝ} (pos : 0 < δ) (small : δ ≤ π/3) :
    0 < sin δ ∧ 0 < cos δ := by
  exact ⟨sin_pos_of_pos_of_lt_pi pos (by linarith [pi_pos]),
    cos_pos_of_mem_Ioo ⟨by linarith [pi_pos],by linarith [pi_pos]⟩⟩

theorem c_injective {δ : ℝ} (pos : 0 < δ) (small : δ ≤ π/3) :
    Function.Injective (c δ) := by
  obtain ⟨hs,hc⟩:=sin_cos pos small
  intro i j eq
  have x:=congrArg (fun p : Point => p 0) eq
  have y:=congrArg (fun p : Point => p 1) eq
  fin_cases i <;> fin_cases j <;> first | rfl | (simp [c,circleDirection] at x y <;> linarith)

theorem direction_sum (δ : ℝ) :
    c δ 1 + c δ 3 = (2*cos δ) • circleDirection 0 := by
  ext i
  fin_cases i <;> simp [c,circleDirection,PiLp.add_apply,PiLp.smul_apply] <;> ring

theorem origin_mem_hull {δ : ℝ} (pos : 0 < δ) (small : δ ≤ π/3) :
    c δ 0 ∈ convexHull ℝ ({c δ 1,c δ 2,c δ 3} : Set Point) := by
  let S : Set Point := {c δ 1,c δ 2,c δ 3}
  have H:=convex_convexHull ℝ S
  have hA : c δ 1 ∈ convexHull ℝ S := subset_convexHull ℝ S (by simp [S])
  have hB : c δ 2 ∈ convexHull ℝ S := subset_convexHull ℝ S (by simp [S])
  have hC : c δ 3 ∈ convexHull ℝ S := subset_convexHull ℝ S (by simp [S])
  have hmid := H hA hC (show 0 ≤ (1/2:ℝ) by norm_num) (show 0 ≤ (1/2:ℝ) by norm_num)
    (show (1/2:ℝ)+1/2=1 by norm_num)
  have hc := (sin_cos pos small).2
  have den : 0 < 1+cos δ := by linarith
  have hmix := H hmid hB (div_nonneg (by norm_num : (0:ℝ) ≤ 1) den.le)
    (div_nonneg hc.le den.le) (show 1/(1+cos δ)+cos δ/(1+cos δ)=1 by field_simp)
  convert hmix using 1
  ext i
  fin_cases i <;> simp [c,circleDirection,PiLp.add_apply,PiLp.smul_apply] <;> field_simp <;> ring

private theorem nonobtuse {p q r : Point} (dot : 0 ≤ inner ℝ (p-q) (r-q)) :
    EuclideanGeometry.angle p q r ≤ π/2 := by
  change arccos (inner ℝ (p-q) (r-q)/(‖p-q‖*‖r-q‖)) ≤ π/2
  exact arccos_le_pi_div_two.mpr (div_nonneg dot (mul_nonneg (norm_nonneg _) (norm_nonneg _)))

private theorem outer_dot {δ : ℝ} (pos : 0 < δ) (small : δ ≤ π/3) {i j k : Fin 4}
    (out : j ≠ 0) (ij : i ≠ j) (ik : i ≠ k) (jk : j ≠ k) :
    0 ≤ inner ℝ (c δ i-c δ j) (c δ k-c δ j) := by
  obtain ⟨hs,hc⟩:=sin_cos pos small
  have iden:=sin_sq_add_cos_sq δ
  have cos_sq := sq_nonneg (cos δ)
  have sin_sq := sq_nonneg (sin δ)
  fin_cases j <;> fin_cases i <;> fin_cases k <;> try contradiction
  all_goals simp [c,circleDirection,PiLp.inner_apply,Fin.sum_univ_two,PiLp.sub_apply] <;> nlinarith
private theorem from_origin {δ : ℝ} (pos : 0 < δ) (small : δ ≤ π/3) {i k : Fin 4}
    (iz : i ≠ 0) (kz : k ≠ 0) (ik : i ≠ k) :
    EuclideanGeometry.angle (c δ i) (c δ 0) (c δ k) ≤ π-δ := by
  have circ (t u : ℝ) (bd : |t-u| ≤ π) :
      angle (circleDirection t) (circleDirection u) = |t-u| := by
    rw [angle_circleDirection,←cos_abs (t-u),arccos_cos (abs_nonneg _) bd]
  have am : angle (circleDirection (-δ)) (-circleDirection 0) = π-δ := by
    rw [angle_neg_right,circ] <;> simp [abs_of_pos pos] <;> linarith [pi_pos]
  have bc : angle (-circleDirection 0) (circleDirection δ) = π-δ := by
    rw [angle_neg_left,circ] <;> simp [abs_of_pos pos] <;> linarith [pi_pos]
  have bound : |-δ-δ| = 2*δ := by rw [abs_of_nonpos (by linarith)]; ring
  have ac : angle (circleDirection (-δ)) (circleDirection δ) = 2*δ := by
    rw [circ,bound]
    rw [bound]; linarith [pi_pos]
  have ma := (angle_comm (-circleDirection 0) (circleDirection (-δ))).trans am
  have cb := (angle_comm (circleDirection δ) (-circleDirection 0)).trans bc
  have ca := (angle_comm (circleDirection δ) (circleDirection (-δ))).trans ac
  fin_cases i <;> fin_cases k <;> try contradiction
  all_goals simp [c,EuclideanGeometry.angle,am,bc,ac,ma,cb,ca] <;> linarith [pi_pos]
theorem «macro» {δ : ℝ} (pos : 0 < δ) (small : δ ≤ π/3) :
    R55.WeightedCollision.Macro (c δ) (π-δ) := by
  intro i j k ij ik jk
  by_cases z : j=0
  · subst j
    exact from_origin pos small ij (Ne.symm jk) ik
  · exact (nonobtuse (outer_dot pos small z ij ik jk)).trans (by linarith [pi_pos])

theorem configuration {δ : ℝ} (pos : 0 < δ) (small : δ ≤ π/3) :
    Function.Injective (c δ) ∧
    c δ 0 ∈ convexHull ℝ ({c δ 1,c δ 2,c δ 3} : Set Point) ∧
    R55.WeightedCollision.Macro (c δ) (π-δ) :=
  ⟨c_injective pos small,origin_mem_hull pos small,«macro» pos small⟩

end R90.Interior

#print axioms R90.Interior.direction_sum
#print axioms R90.Interior.configuration
