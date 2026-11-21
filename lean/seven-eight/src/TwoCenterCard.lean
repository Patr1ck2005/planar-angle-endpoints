import SharpTwoCenters

noncomputable section
namespace R51.TwoCenters
open JSP404 Real

/-- Minimize also over the macrocluster sizes. The larger cluster is named first. -/
def byCard (N : ℕ) : Set ℝ := {u | ∃ r s : ℕ, N=r+s ∧ 2≤r ∧ 0<s ∧ s≤r ∧ u∈attainable r s}

private theorem round_lower {N r s : ℕ} (sz : N=r+s) (sr : s≤r) :
    Nat.clog 2 N≤Nat.clog 2 r+1 := by
  apply Nat.clog_le_of_le_pow
  rw [pow_succ]
  have up:=Nat.le_pow_clog (by decide : 1<2) r
  omega

/-- For every total N≥3, the two-center boundary has exactly the dyadic value. -/
theorem sharp_by_card {N : ℕ} (three : 3≤N) :
    IsLeast (byCard N) (π-π/(Nat.clog 2 N:ℝ)) := by
  classical
  let s:=N/2
  let r:=N-s
  have sz : N=r+s := by dsimp [r,s];omega
  have two : 2≤r := by dsimp [r,s];omega
  have sp : 0<s := by dsimp [s];omega
  have sr : s≤r := by dsimp [r,s];omega
  have pos : 0<Nat.clog 2 N := Nat.clog_pos (by decide) (by omega)
  have up:=Nat.le_pow_clog (by decide : 1<2) N
  have replace : Nat.clog 2 N=(Nat.clog 2 N-1)+1 := by omega
  conv at up => rhs;arg 2;rw [replace]
  rw [pow_succ] at up
  have fit : r≤2^(Nat.clog 2 N-1) := by dsimp [r,s];omega
  have enough:=Nat.clog_le_of_le_pow fit
  have exactK : Nat.clog 2 N=Nat.clog 2 r+1 := by have := round_lower sz sr;omega
  constructor
  · refine ⟨r,s,sz,two,sp,sr,?_⟩
    rw [exactK,Nat.cast_add,Nat.cast_one]
    exact (sharp_two_centers two sp sr).1
  · rintro u ⟨a,b,eq,atwo,bp,ba,hu⟩
    have h:=least_lower atwo bp hu
    have k : (Nat.clog 2 N:ℝ)≤(Nat.clog 2 a:ℝ)+1 := by exact_mod_cast round_lower eq ba
    have positive : 0<(Nat.clog 2 N:ℝ) := by exact_mod_cast pos
    have div := div_le_div_of_nonneg_left pi_pos.le positive k
    linarith

theorem nine_two_center : IsLeast (byCard 9) (3*π/4) := by
  have h:=sharp_by_card (N:=9) (by decide)
  have c : Nat.clog 2 9=4 := by decide
  rw [c] at h
  convert h using 1
  ring

end R51.TwoCenters
#print axioms R51.TwoCenters.sharp_by_card
#print axioms R51.TwoCenters.nine_two_center
