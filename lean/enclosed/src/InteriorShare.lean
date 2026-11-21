import EnclosedRigidity
import WitnessReserve

noncomputable section
namespace R89.Share
open JSP404 Real Finset R55.WeightedCollision

/-- A cluster of dyadic size 2^d controls the entire Sendov staircase up to
a total of 8·2^d whenever it is enclosed. -/
theorem target_le {N W : ℕ} (ge : 3≤N) (share : N≤8*2^(Nat.clog 2 W)) :
    Jsp404.alphaN N≤R89.Sharp.criticalAngle W := by
  let d:=Nat.clog 2 W
  have h : Nat.clog 2 N≤d+3:=Nat.clog_le_of_le_pow (by
    change N≤2^(Nat.clog 2 W+3)
    simpa [pow_add,Nat.mul_comm] using share)
  have p : 0<(Nat.clog 2 N:ℝ):=by exact_mod_cast Nat.clog_pos (by decide : 1<2) (by omega : 1<N)
  have bound : (Nat.clog 2 N:ℝ)≤(d:ℝ)+3:=by exact_mod_cast h
  have dyadic:=R59.Mesh.sendov_of_dyadic ge
  exact dyadic.trans (sub_le_sub_left (div_le_div_of_nonneg_left pi_pos.le p bound) π)

theorem enclosed_share {I : Type*} [Fintype I] [Nontrivial I] {c : I→Point}
    (ci : Function.Injective c) {w : I→ℕ} (wp : ∀j,0<w j) (i : I)
    (inside : c i∈convexHull ℝ (c '' {j | j≠i})) {θ : ℝ} (hit : θ∈attainable w c)
    (ge : 3≤∑j,w j) (share : (∑j,w j)≤8*2^(Nat.clog 2 (w i))) :
    Jsp404.alphaN (∑j,w j)≤θ :=
  (target_le ge share).trans (R89.Interior.enclosed_angle ci wp hit i inside)

/-- The full target is strictly beaten for all positive weights on five to
eight sites when one of the largest assigned weights sits inside the other sites. -/
theorem largest_at_enclosed {I : Type*} [Fintype I] [Nontrivial I] {c : I→Point}
    (ci : Function.Injective c) (five : 5≤Fintype.card I) (eight : Fintype.card I≤8)
    {w : I→ℕ} (wp : ∀j,0<w j) (i : I) (largest : ∀j,w j≤w i)
    (inside : c i∈convexHull ℝ (c '' {j | j≠i})) {θ : ℝ} (hit : θ∈attainable w c) :
    Jsp404.alphaN (∑j,w j)<θ := by
  have ge : Fintype.card I≤∑j,w j:=by
    simpa using (sum_le_sum (s:=univ) (fun j _=>show 1≤w j from wp j))
  have size : (∑j,w j)≤Fintype.card I*w i:=by
    simpa using sum_le_sum (s:=univ) (fun j _=>largest j)
  have share:=(size.trans (Nat.mul_le_mul_right _ eight)).trans
    (Nat.mul_le_mul_left 8 (Nat.le_pow_clog (by decide : 1<2) (w i)))
  exact (target_le (by omega) share).trans_lt (R89.Sharp.strict_enclosed ci wp i inside five hit)
end R89.Share
#print axioms R89.Share.target_le
#print axioms R89.Share.enclosed_share
#print axioms R89.Share.largest_at_enclosed
