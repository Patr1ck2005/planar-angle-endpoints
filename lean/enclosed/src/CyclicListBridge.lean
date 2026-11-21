import CyclicSpectrumBound
import CycleList

noncomputable section
namespace R58.CircleModel
open Real SendovCycle R53.Surgery

def window {A : Type*} (f : ℕ→A) (n : ℕ) : ℕ→List A
  | 0 => []
  | k+1 => f n :: window f (n+1) k

theorem window_sum {A : Type} (f : ℕ→A) (g : A→ℕ) (n k : ℕ) :
    ((window f n k).map g).sum=seg (fun i=>g (f i)) n k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp only [window,List.map_cons,List.sum_cons,seg,ih]

theorem window_path (f : ℕ→ℝ) (n k : ℕ) :
    arcPath (f n) (window f (n+1) k) (f (n+k+1)) =
      seg (fun i=>2^bump (f i) (f (i+1))) n (k+1) := by
  induction k generalizing n with
  | zero => simp [window,arcPath,seg]
  | succ k ih =>
    conv_rhs => rw [seg]
    simp only [window,arcPath]
    rw [show n+(k+1)+1=(n+1)+k+1 by omega,ih]

theorem cycle_window (f : ℕ→ℝ) {t : ℕ} (tp : 0<t) (period : ∀n,f (n+t)=f n) (n : ℕ) :
    cycleCapacity (window f n t)=2^(seg (fun i=>slot (f i)) n t) *
      seg (fun i=>2^bump (f i) (f (i+1))) n t := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero tp.ne'
  change 2^((window f n (k+1)).map slot).sum * arcPath (f n) (window f (n+1) k) (f n)=_
  rw [window_sum]
  have per : f (n+k+1)=f n := by simpa only [Nat.add_assoc] using period n
  rw [←window_path,per]

namespace Lift
variable {t : ℕ} (C : CircleModel.Lift t)
def mass (lam : ℝ) := ∑i : Fin t, 2^(C.budget lam i.val)

/-- The list surgery functional is the actual maximum achievable total weight
of a legal fixed circle shape. Its value is independent of the cut. -/
theorem cycle_mass (ht : 3≤t) {lam : ℝ} (lp : 0<lam) (n : ℕ) :
    cycleCapacity (window (C.arc lam) n t)=C.mass lam := by
  have tp : 0<t := by omega
  let A := C.arc lam
  let b (j : ℕ) := slot (A j)
  let bonus (j : ℕ) := bump (A j) (A (j+1))
  let B := seg b 0 t
  have perB (j : ℕ) : b (j+t)=b j := by simp [b,A,C.arc_period]
  have perBonus (j : ℕ) : 2^bonus (j+t)=2^bonus j := by
    simp [bonus,A,C.arc_period,show j+t+1=j+1+t by omega]
  have pair (j : ℕ) : b j+b (j+1)≤B := by
    have h := seg_rotate perB j
    have expand : seg b j t = b j+(b (j+1)+seg b (j+2) (t-2)) := by
      calc seg b j t = seg b j ((t-2)+1+1) := congrArg (seg b j) (by omega)
           _ = _ := rfl
    change _≤seg b 0 t
    omega
  have exponent (j : ℕ) : C.budget lam (j+1)=B+bonus j := by
    have h := C.budget_formula ht lam j
    have abs := slot_sum (C.arc_nonneg lp j) (C.arc_nonneg lp (j+1))
    change b j+b (j+1)≤slot (A j+A (j+1)) at abs
    change C.budget lam (j+1)=B-b j-b (j+1)+slot (A j+A (j+1)) at h
    change _=B+(slot (A j+A (j+1))-b j-b (j+1))
    have jb := pair j
    omega
  rw [cycle_window A tp (C.arc_period lam)]
  change 2^(seg b n t)*seg (fun i=>2^bonus i) n t=C.mass lam
  rw [seg_rotate perB n,seg_rotate perBonus n]
  unfold mass
  rw [←shifted_sum tp (fun i=>2^(C.budget lam i.val))]
  change 2^B*seg (fun i=>2^bonus i) 0 t = seg (fun k=>2^C.budget lam (index tp (k+1)).val) 0 t
  rw [seg_fin (fun i=>2^bonus i),seg_fin (fun k=>2^C.budget lam (index tp (k+1)).val),Finset.mul_sum]
  apply Finset.sum_congr rfl;intro j _
  simp only [Nat.zero_add,index,(C.budget_period lam).map_mod_nat,exponent,pow_add]

#print axioms cycle_mass
end Lift
end R58.CircleModel
