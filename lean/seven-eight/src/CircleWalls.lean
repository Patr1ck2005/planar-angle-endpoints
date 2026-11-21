import CircleLift

noncomputable section
namespace R58.CircleModel.Lift
open Real JSP404 R56.Windows R54.GapTest R55.WeightedCollision

variable {t : ℕ} (C : R58.CircleModel.Lift t)

def offset (t k : ℕ) := if k<t-1 then k+1 else t+1
def W (n k : ℕ) := C.u n+C.u (n+offset t k)+π/2

def row (ht : 3≤t) (n : ℕ) : Row (t-1) where
  w := C.W n
  ordered := by
    intro a b ab bm
    have h : offset t a≤offset t b := by unfold offset;split_ifs <;> omega
    unfold W
    linarith [C.increasing.monotone (Nat.add_le_add_left h n)]
  period := by
    simp only [W,offset,lt_irrefl,ite_false,if_pos (show 0<t-1 by omega)]
    rw [show n+(t+1)=(n+1)+t by omega,C.nextPeriod]
    ring

theorem row_wall (ht : 3≤t) (n k : ℕ) (hk : k<t-1) :
    Bearing (C.P (n+1+k)-C.P n) ((C.row ht n).w k) := by
  have b := C.wall (n:=n) (k:=n+1+k) (by omega) (by omega)
  simpa only [row,W,offset,if_pos hk,show n+(k+1)=n+1+k by omega] using b

theorem witnessed (ht : 3≤t) :
    Witnessed (fun i : Fin t=>C.row ht i.val) C.centers := by
  intro i k hk
  change k≤t-1 at hk
  have tp : 0<t := by omega
  by_cases lt : k<t-1
  · let h := index tp (i.val+1+k)
    have e : C.centers h=C.P (i.val+1+k) := C.center_index _ _
    have ne : i≠h := by
      intro eq
      have same := congrArg C.centers eq
      rw [e] at same
      exact C.point_ne (n:=i.val) (k:=i.val+1+k) (by omega) (by omega) same
    exact ⟨h,ne,by rw [e]; exact C.row_wall ht i.val k lt⟩
  · have eq : k=t-1 := by omega
    let h := index tp (i.val+1)
    have e : C.centers h=C.P (i.val+1) := C.center_index _ _
    have ne : i≠h := by
      intro h'
      have same := congrArg C.centers h'
      rw [e] at same
      exact C.point_ne (n:=i.val) (k:=i.val+1) (by omega) (by omega) same
    refine ⟨h,ne,?_⟩
    rw [e,eq,(C.row ht i.val).period]
    apply bearing_closes
    simpa only [centers,Nat.add_zero] using C.row_wall ht i.val 0 (by omega)

theorem represents (ht : 3≤t) :
    Represents (fun i : Fin t=>C.row ht i.val) C.centers := by
  intro i j ne
  have neq : i.val≠j.val := fun e=>ne (Fin.ext e)
  obtain ⟨n,ln,hn,eq⟩ : ∃ n : ℕ, (i.val < n) ∧ (n < i.val+t) ∧ C.P n=C.centers j := by
    rcases lt_or_gt_of_ne neq with h|h
    · exact ⟨j.val,h,by omega,rfl⟩
    · exact ⟨j.val+t,by omega,by omega,C.periodic j.val⟩
  let k := n-i.val-1
  have lk : k<t-1 := by dsimp [k];omega
  have eqn : i.val+1+k=n := by dsimp [k];omega
  obtain ⟨r,rp,e,es,line⟩ := C.row_wall ht i.val k lk
  exact ⟨k,lk.le,r,rp,e,es,by rwa [eqn,eq] at line⟩

def arc (lam : ℝ) (n : ℕ) : ℝ := (C.u (n+1)-C.u n)/lam

theorem arc_period (lam : ℝ) (n : ℕ) : C.arc lam (n+t)=C.arc lam n := by
  rw [arc,arc,show n+t+1=(n+1)+t by omega,C.nextPeriod,C.nextPeriod]
  ring

theorem arc_nonneg {lam : ℝ} (lp : 0<lam) (n : ℕ) : 0≤C.arc lam n :=
  div_nonneg (sub_nonneg.mpr (C.increasing.monotone (by omega))) lp.le

theorem arc_legal (ht : 3≤t) {lam : ℝ} (lp : 0<lam) (legal : Macro C.centers (π-lam)) (n : ℕ) :
    1≤C.arc lam n+C.arc lam (n+1) := by
  have tp : 0<t := by omega
  have ne {a b : ℕ} (ab : a<b) (bt : b<a+t) : index tp a≠index tp b := by
    intro eq
    have h := congrArg C.centers eq
    rw [C.center_index,C.center_index] at h
    exact C.point_ne ab bt h
  have h := legal (index tp n) (index tp (n+1)) (index tp (n+2))
    (ne (by omega) (by omega)) (ne (by omega) (by omega)) (ne (by omega) (by omega))
  rw [C.center_index,C.center_index,C.center_index,C.corner ht] at h
  unfold arc
  rw [←add_div,le_div_iff₀ lp]
  linarith

#print axioms witnessed
#print axioms represents
#print axioms arc_legal
end R58.CircleModel.Lift
