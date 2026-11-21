import ThreeFreeDirections
import InteriorThreeChords

noncomputable section
namespace R93.Interior
open JSP404 Real InnerProductGeometry R55.WeightedCollision R92.Tight

/-- Different external labels give different projective axes at a fixed
center: three distinct collinear points would have a straight middle angle. -/
theorem different_axes {I : Type*} {c : I→Point} (ci : Function.Injective c)
    {θ : ℝ} (below : θ<π) (mac : Macro c θ) {i j k : I}
    (ji : j≠i) (ki : k≠i) (jk : j≠k) : ¬SameAxis (c j-c i) (c k-c i) := by
  rintro ⟨s,sn,eq⟩
  let v:=c k-c i
  have vn : v≠0:=sub_ne_zero.mpr (ci.ne ki)
  change c j-c i=s • v at eq
  have flip {r t : ℝ} (rn : r<0) (tp : 0<t) : angle (r • v) (t • v)=π := by
    rw [angle_smul_left_of_neg _ _ rn,angle_smul_right_of_pos _ _ tp,angle_neg_left,angle_self vn,sub_zero]
  rcases lt_or_gt_of_ne sn with neg|pos
  · have bd:=mac j i k ji jk ki.symm
    change angle (c j-c i) v≤θ at bd
    rw [eq,angle_smul_left_of_neg _ _ neg,angle_neg_left,angle_self vn,sub_zero] at bd
    linarith
  have one : s≠1:=by
    rintro rfl
    rw [one_smul] at eq
    exact jk (ci (sub_left_inj.mp eq))
  have diff : c j-c k=(s-1) • v:=by rw [sub_smul,one_smul,←eq];dsimp [v];abel
  rcases lt_or_gt_of_ne one with lo|hi
  · have bd:=mac i j k ji.symm ki.symm jk
    have first : c i-c j=(-s) • v:=by rw [neg_smul,←eq,neg_sub]
    have last : c k-c j=(1-s) • v:=by rw [←neg_sub (c j) (c k),diff,←neg_smul,neg_sub]
    change angle (c i-c j) (c k-c j)≤θ at bd
    rw [first,last,flip (by linarith) (by linarith)] at bd
    linarith
  · have bd:=mac i k j ki.symm ji.symm jk.symm
    have first : c i-c k=(-(1:ℝ)) • v:=by simp [v]
    change angle (c i-c k) (c j-c k)≤θ at bd
    rw [first,diff,flip (by norm_num) (by linarith)] at bd
    linarith

/-- The V91 surrounding triple with its prescribed first label retained in
an explicit embedding, in the form used by a three-axis completion. -/
theorem anchored_embedding {I : Type*} [Fintype I] {c : I→Point} (ci : Function.Injective c)
    {i j : I} (ji : j≠i) (inside : c i∈convexHull ℝ (c '' {a | a≠i}))
    {δ : ℝ} (dp : 0<δ) (mac : Macro c (π-δ)) :
    ∃h : Fin 3↪I,h 0=j ∧ (∀a,h a≠i) ∧ ∀a b,a≠b →
      δ≤EuclideanGeometry.angle (c (h a)) (c i) (c (h b)) ∧
      EuclideanGeometry.angle (c (h a)) (c i) (c (h b))≤π-δ := by
  obtain ⟨k,l,ki,li,jk,jl,kl,_,A,B,C⟩:=R91.Interior.anchored_three ci ji inside dp mac
  let h : Fin 3↪I := ⟨![j,k,l],by intro a b eq;fin_cases a <;> fin_cases b <;> simp_all⟩
  have ext (a : Fin 3) : h a≠i:=by fin_cases a <;> first | exact ji | exact ki | exact li
  refine ⟨h,rfl,ext,?_⟩
  intro a b ab
  refine ⟨(show δ≤2*δ by linarith).trans ?_,mac _ _ _ (ext a) (h.injective.ne ab) (ext b).symm⟩
  have A' : 2*δ≤EuclideanGeometry.angle (c k) (c i) (c j):=by rwa [EuclideanGeometry.angle_comm]
  have B' : 2*δ≤EuclideanGeometry.angle (c l) (c i) (c k):=by rwa [EuclideanGeometry.angle_comm]
  have C' : 2*δ≤EuclideanGeometry.angle (c j) (c i) (c l):=by rwa [EuclideanGeometry.angle_comm]
  fin_cases a <;> fin_cases b <;> first | exact (ab rfl).elim | exact A | exact B | exact C | exact A' | exact B' | exact C'

end R93.Interior
#print axioms R93.Interior.different_axes
#print axioms R93.Interior.anchored_embedding
