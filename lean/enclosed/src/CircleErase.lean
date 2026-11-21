import CircleRowBudget

noncomputable section
namespace R58.CircleModel
open Real JSP404 SendovCycle
namespace Lift
variable {t : ℕ} (C : CircleModel.Lift t)

private def jump (h k : ℕ) := if k<2 then k else k+h
private def address (T h k : ℕ) := (k/T)*(T+h)+jump h (k%T)

private theorem address_period {T h : ℕ} (tp : 0<T) (k : ℕ) :
    address T h (k+T)=address T h k+(T+h) := by
  simp only [address,Nat.add_div_right _ tp,Nat.add_mod_right,add_mul,one_mul]
  omega

private theorem address_inc {T h : ℕ} (two : 2≤T) : StrictMono (address T h) := by
  intro i j ij
  have tp : 0<T := by omega
  have il := Nat.mod_lt i tp
  have jl := Nat.mod_lt j tp
  by_cases eq : i/T=j/T
  · have a := Nat.mod_add_div i T
    have b := Nat.mod_add_div j T
    rw [eq] at a
    have r : i%T<j%T := by omega
    unfold address jump
    rw [eq]
    split_ifs <;> omega
  · have q : i/T<j/T := lt_of_le_of_ne (Nat.div_le_div_right ij.le) eq
    have group := Nat.mul_le_mul_right (T+h) (show i/T+1≤j/T by omega)
    rw [Nat.add_mul,one_mul] at group
    unfold address jump
    split_ifs <;> omega

private theorem address_first {T h : ℕ} (two : 2≤T) {k : ℕ} (b : k≤T) :
    address T h k=jump h k := by
  rcases lt_or_eq_of_le b with lt|rfl
  · simp [address,Nat.mod_eq_of_lt lt,Nat.div_eq_of_lt lt]
  · simp [address,jump,Nat.div_self (show 0<k by omega),not_lt.mpr two]

/-- Erase h consecutive old vertices beginning at n+2, where the first two
indices of the new ordering are n and n+1. -/
def erase (T h : ℕ) (sum : T+h=t) (two : 2≤T) (n : ℕ) : CircleModel.Lift T where
  center := C.center
  radius := C.radius
  pos := C.pos
  u k := C.u (n+address T h k)
  increasing := fun _ _ lt=>C.increasing (Nat.add_lt_add_left (address_inc two lt) n)
  nextPeriod := by
    intro k
    rw [address_period (by omega),←Nat.add_assoc,sum,C.nextPeriod]

theorem survivors {T h : ℕ} (sum : T+h=t) (two : 2≤T) (n : ℕ) :
    ∃ e : Fin T ↪ Fin t, ∀i,(C.erase T h sum two n).centers i=C.centers (e i) := by
  let F (i : Fin T) := index (show 0<t by omega) (n+address T h i.val)
  have eq (i : Fin T) : (C.erase T h sum two n).centers i=C.centers (F i) := by
    rw [show C.centers (F i)=C.P (n+address T h i.val) from C.center_index _ _]
    rfl
  refine ⟨⟨F,?_⟩,eq⟩
  intro i j e
  exact (C.erase T h sum two n).centers_injective ((eq i).trans ((congrArg C.centers e).trans (eq j).symm))

theorem first_gap {T h : ℕ} (sum : T+h=t) (two : 2≤T) (n : ℕ) (lam : ℝ) :
    (C.erase T h sum two n).arc lam 0=C.arc lam n := by
  change (C.u (n+address T h 1)-C.u (n+address T h 0))/lam=_
  simp [address_first two (show 1≤T by omega),address_first two (show 0≤T by omega),jump,arc]

theorem combined_gap {T h : ℕ} (sum : T+h=t) (two : 2≤T) (n : ℕ) (lam : ℝ) :
    (C.erase T h sum two n).arc lam 1=seg (C.arc lam) (n+1) (h+1) := by
  change (C.u (n+address T h 2)-C.u (n+address T h 1))/lam=_
  rw [C.arc_sum,address_first two two,address_first two (show 1≤T by omega)]
  simp only [jump,show ¬(2:ℕ)<2 by decide,show (1:ℕ)<2 by decide,ite_false,ite_true]
  rw [show n+(2+h)=n+1+(h+1) by omega]

theorem untouched_gap {T h : ℕ} (sum : T+h=t) (two : 2≤T) (n : ℕ) (lam : ℝ)
    {k : ℕ} (lo : 2≤k) (hi : k<T) :
    (C.erase T h sum two n).arc lam k=C.arc lam (n+k+h) := by
  change (C.u (n+address T h (k+1))-C.u (n+address T h k))/lam=_
  rw [address_first two (show k+1≤T by omega),address_first two hi.le]
  simp only [jump,if_neg (show ¬k+1<2 by omega),if_neg (not_lt.mpr lo),arc]
  rw [show n+(k+1+h)=n+k+h+1 by omega,show n+(k+h)=n+k+h by omega]

#print axioms survivors
#print axioms combined_gap
end Lift
end R58.CircleModel
