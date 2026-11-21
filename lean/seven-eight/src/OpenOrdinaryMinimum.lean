import ExtremeCount
import EnclosedRigidity
import Jsp000404.SmallAngleLower
import FullProblem

noncomputable section
namespace R89.Ordinary
open JSP404 Real R55.WeightedCollision

/-- At most six distinct ordinary planar sites can keep every angle at
most 120 degrees. This includes the boundary case of the angle inequality. -/
theorem at_most_six {I : Type*} [Fintype I] [Nontrivial I] {c : I→Point}
    (ci : Function.Injective c) (mac : Macro c (2*π/3)) : Fintype.card I≤6 := by
  classical
  by_contra! big
  by_cases all : ∀i,c i∉convexHull ℝ (c '' {j | j≠i})
  · let e:Fin (Fintype.card I)↪I:=(Fintype.equivFin I).symm.toEmbedding
    have count:=R89.Hull.vertex_count ci (by positivity) mac (by omega) e (fun j=>all (e j))
    have seven : (7:ℝ)≤Fintype.card I:=by exact_mod_cast big
    have scaled:=mul_le_mul_of_nonneg_right seven pi_pos.le
    nlinarith only [count,scaled,pi_pos]
  · push Not at all
    obtain ⟨i,inside⟩:=all
    have four:=R91.Rigid.four_sites ci inside mac
    omega

/-- Every set of at least seven distinct ordinary planar points has an angle
strictly greater than 120 degrees. -/
theorem strict_angles (S : Finset Point) (many : 7≤S.card) : 2*π/3<maxAngle S := by
  by_contra! cap
  have count : 7≤Fintype.card (↥S):=by simpa using many
  let _ : Nontrivial (↥S):=Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have mac : Macro (fun u:S=>u.val) (2*π/3) := by
    intro i j k ij ik jk
    exact (angle_le_maxAngle i.property j.property k.property
      (fun e=>ij (Subtype.ext e)) (fun e=>ik (Subtype.ext e)) (fun e=>jk (Subtype.ext e))).trans cap
  have few:=at_most_six Subtype.val_injective mac
  omega

/-- The ordinary seven- and eight-point infima both equal 120 degrees and
neither is attained by a finite configuration of distinct points. -/
theorem seven_eight (N : ℕ) (size : N=7 ∨ N=8) :
    alpha N=2*π/3 ∧ ∀S : Finset Point,S.card=N→alpha N<maxAngle S := by
  have ge : 3≤N:=by omega
  have val:=(R52.ThreeCover.full_staircase ge).unique
    (R52.ThreeCover.high_band (k:=0) (by norm_num;omega) (by norm_num;omega))
  have eq:=Jsp404.sendov_alpha_eq_le_eight N ge (by omega)
  rw [val] at eq
  have exactValue : alpha N=2*π/3:=by
    convert eq using 1
    norm_num
    ring
  refine ⟨exactValue,fun S sz=>?_⟩
  rw [exactValue]
  exact strict_angles S (by omega)
end R89.Ordinary
#print axioms R89.Ordinary.at_most_six
#print axioms R89.Ordinary.strict_angles
#print axioms R89.Ordinary.seven_eight
