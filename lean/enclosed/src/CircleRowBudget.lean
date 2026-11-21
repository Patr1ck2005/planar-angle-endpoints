import CircleWalls
import CyclicReal

noncomputable section
namespace R58.CircleModel
open Real SendovCycle R51.Anchored R56.Windows R54.GapTest

theorem seg_fin {A : Type} [AddCommMonoid A] (f : ℕ→A) (n k : ℕ) :
    seg f n k=∑j : Fin k,f (n+j.val) := by
  induction k generalizing n with
  | zero => simp [seg]
  | succ k ih =>
    rw [seg,Fin.sum_univ_succ,ih]
    simp only [Fin.val_zero,Nat.add_zero,Fin.val_succ]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [show n+1+i.val=n+(i.val+1) by omega]

theorem seg_snoc {A : Type} [AddCommMonoid A] (f : ℕ→A) (n k : ℕ) :
    seg f n (k+1)=seg f n k+f (n+k) := by
  simp only [seg_fin,Fin.sum_univ_castSucc,Fin.val_castSucc,Fin.val_last]

theorem seg_rotate {f : ℕ→ℕ} {t : ℕ} (per : ∀k,f (k+t)=f k) (n : ℕ) :
    seg f n t=seg f 0 t := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h := seg_snoc f n t
    rw [seg,per] at h
    omega

namespace Lift
variable {t : ℕ} (C : CircleModel.Lift t)

theorem arc_sum (lam : ℝ) (n k : ℕ) : seg (C.arc lam) n k=(C.u (n+k)-C.u n)/lam := by
  induction k generalizing n with
  | zero => simp [seg]
  | succ k ih =>
    rw [seg,ih]
    unfold arc
    rw [show n+1+k=n+(k+1) by omega]
    ring

def charge (lam : ℝ) (n : ℕ) : ℕ := ⌊C.arc lam n⌋₊-1

def budget (lam : ℝ) (n : ℕ) : ℕ := gapScore (t-1) (C.W n) lam

theorem budget_period (lam : ℝ) : Function.Periodic (C.budget lam) t := by
  intro n
  have gap (k : ℕ) : C.W (n+t) k=C.W n k+2*π := by
    unfold W
    rw [C.nextPeriod,show n+t+offset t k=n+offset t k+t by omega,C.nextPeriod];ring
  unfold budget gapScore
  simp only [gap,add_sub_add_right_eq_sub]

theorem budget_formula (ht : 3≤t) (lam : ℝ) (n : ℕ) :
    C.budget lam (n+1)=seg (C.charge lam) 0 t-C.charge lam n-C.charge lam (n+1)+
      (⌊C.arc lam n+C.arc lam (n+1)⌋₊-1) := by
  let f (k : ℕ) := ⌊(C.W (n+1) (k+1)-C.W (n+1) k)/lam⌋₊-1
  have normal (k : ℕ) (hk : k<t-2) : f k=C.charge lam (n+2+k) := by
    unfold f charge arc W offset
    rw [if_pos (show k+1<t-1 by omega),if_pos (show k<t-1 by omega),
      show n+1+(k+1+1)=n+2+k+1 by omega,show n+1+(k+1)=n+2+k by omega]
    congr 3
    ring
  have seam : f (t-2)=⌊C.arc lam n+C.arc lam (n+1)⌋₊-1 := by
    unfold f arc W offset
    rw [if_neg (show ¬t-2+1<t-1 by omega),if_pos (show t-2<t-1 by omega),
      show n+1+(t+1)=n+2+t by omega,show n+1+(t-2+1)=n+t by omega,C.nextPeriod,C.nextPeriod]
    congr 2
    rw [←add_div]
    congr 1
    ring
  have B : C.budget lam (n+1)=seg f 0 (t-1) := by simp [budget,gapScore,seg_fin,f]
  have shifted : seg f 0 (t-2)=seg (C.charge lam) (n+2) (t-2) := by
    rw [seg_fin,seg_fin]
    exact Finset.sum_congr rfl (fun j _=>by simpa using normal j.val j.isLt)
  have total := seg_rotate (f:=C.charge lam) (t:=t)
    (fun k=>by simp only [charge,C.arc_period]) n
  have full : seg (C.charge lam) n t=C.charge lam n+C.charge lam (n+1)+seg (C.charge lam) (n+2) (t-2) := by
    calc seg (C.charge lam) n t = seg (C.charge lam) n ((t-2)+1+1) :=
           congrArg (seg (C.charge lam) n) (by omega)
         _ = _ := by simp only [seg,show n+1+1=n+2 by omega];omega
  rw [B,show t-1=t-2+1 by omega,seg_snoc,Nat.zero_add,seam,shifted]
  omega

#print axioms budget_formula
end Lift
end R58.CircleModel
