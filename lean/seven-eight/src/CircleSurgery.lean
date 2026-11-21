import CircleErase
import CyclicListBridge

noncomputable section
namespace R58.CircleModel
open Real SendovCycle R53.Surgery R55.WeightedCollision

theorem window_match {X : Type*} (f g : ℕ→X) (a b k : ℕ) (same : ∀j<k,f (a+j)=g (b+j)) :
    window f a k=window g b k := by
  induction k generalizing a b with
  | zero => rfl
  | succ k ih =>
    rw [window,window,show f a=g b by simpa using same 0 (by omega)]
    apply congrArg (List.cons _)
    apply ih
    intro j hj
    simpa only [Nat.add_assoc,Nat.add_comm 1 j] using same (j+1) (by omega)

namespace Lift
variable {t : ℕ} (C : CircleModel.Lift t)

theorem erased_window {T h : ℕ} (sum : T+h=t) (two : 2≤T) (n : ℕ) (lam : ℝ) :
    window ((C.erase T h sum two n).arc lam) 0 T =
      C.arc lam n :: seg (C.arc lam) (n+1) (h+1) :: window (C.arc lam) (n+2+h) (T-2) := by
  let g := (C.erase T h sum two n).arc lam
  have tails : window g 2 (T-2)=window (C.arc lam) (n+2+h) (T-2) := by
    apply window_match
    intro j hj
    have eq := C.untouched_gap sum two n lam (k:=2+j) (by omega) (by omega)
    simpa only [show n+(2+j)+h=n+2+h+j by omega] using eq
  calc window g 0 T = window g 0 ((T-2)+2) := congrArg _ (by omega)
       _ = _ := by
         change g 0 :: g 1 :: window g 2 (T-2)=_
         rw [tails];exact congrArg₂ List.cons (C.first_gap sum two n lam)
           (congrArg (fun z=>z :: window (C.arc lam) (n+2+h) (T-2)) (C.combined_gap sum two n lam))

theorem local_cut {r : ℕ} (C : CircleModel.Lift (r+5)) {lam : ℝ} (lp : 0<lam)
    (legal : Macro C.centers (π-lam)) (n : ℕ)
    (top : ∀k,bump (C.arc lam k) (C.arc lam (k+1))≤bump (C.arc lam (n+1)) (C.arc lam (n+2))) :
    C.mass lam≤(C.erase (r+4) 1 (by omega) (by omega) n).mass lam ∨
    C.mass lam≤(C.erase (r+3) 2 (by omega) (by omega) n).mass lam := by
  let A := C.arc lam
  let S (k : ℕ) := A (n+k)
  let tail := window A (n+5) r
  have base : window A n (r+5)=S 0::S 1::S 2::S 3::S 4::tail := rfl
  have one : window ((C.erase (r+4) 1 (by omega) (by omega) n).arc lam) 0 (r+4)=
      S 0::(S 1+S 2)::S 3::S 4::tail := by
    rw [C.erased_window]
    simp [S,A,tail,seg,window]
  have two : window ((C.erase (r+3) 2 (by omega) (by omega) n).arc lam) 0 (r+3)=
      S 0::(S 1+S 2+S 3)::S 4::tail := by
    rw [C.erased_window]
    simp [S,A,tail,seg,window,add_assoc]
  have pos (k : ℕ) : 0≤S k := C.arc_nonneg lp _
  have law (k : ℕ) : 1≤S k+S (k+1) := C.arc_legal (by omega) lp legal _
  have mx (k : ℕ) : bump (S k) (S (k+1))≤bump (S 1) (S 2) := top _
  have cut := maximal_cut tail (pos 0) (pos 1) (pos 2) (pos 3) (pos 4)
    (law 0) (law 1) (law 2) (law 3) (mx 0) (mx 2) (mx 3)
  rw [←base,←one,←two] at cut
  exact (C.cycle_mass (by omega) lp n) ▸
    ((C.erase (r+4) 1 (by omega) (by omega) n).cycle_mass (by omega) lp 0 ▸
    ((C.erase (r+3) 2 (by omega) (by omega) n).cycle_mass (by omega) lp 0 ▸ cut))

theorem best_cut {r : ℕ} (C : CircleModel.Lift (r+5)) {lam : ℝ} (lp : 0<lam)
    (legal : Macro C.centers (π-lam)) :
    ∃ n, C.mass lam≤(C.erase (r+4) 1 (by omega) (by omega) n).mass lam ∨
       C.mass lam≤(C.erase (r+3) 2 (by omega) (by omega) n).mass lam := by
  classical
  let f (k : ℕ) := bump (C.arc lam k) (C.arc lam (k+1))
  have per : Function.Periodic f (r+5) := by
    intro k
    simp only [f,C.arc_period,show k+(r+5)+1=(k+1)+(r+5) by omega]
  obtain ⟨j,_,largest⟩ := Finset.exists_max_image Finset.univ (fun i : Fin (r+5)=>f i.val)
    Finset.univ_nonempty
  let n := j.val+(r+4)
  refine ⟨n,C.local_cut lp legal n ?_⟩
  intro k
  have a := largest (index (show 0<r+5 by omega) k) (Finset.mem_univ _)
  change f (k%(r+5))≤f j.val at a
  change f k≤f (n+1)
  rw [show n+1=j.val+(r+5) by dsimp [n]; omega,per j.val]
  rwa [per.map_mod_nat] at a

#print axioms local_cut
#print axioms best_cut
end Lift
end R58.CircleModel
