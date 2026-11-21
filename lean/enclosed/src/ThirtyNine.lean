import CompressedAverage
import FortyExact

noncomputable section
namespace R43.FiniteStrata
open Real JSP404 R37.SignedFan R40.EvenTail R42.Average R42.CompressedAverage

/-- A rational period for any selected subfamily of k rows. -/
theorem cap {S : Finset Point} {lam : ℝ} (hl : 0<lam) (F : S → Row)
    (profile : IsProfile S lam F) (m s k p q : ℕ) (hm : 0<m) (hq : 0<q) (mpq : m*p≤q)
    (rounding : ∀ A B : ℕ, A≤k*s → (A:ℝ)≤(B:ℝ)*(π/lam) → (p:ℤ)*A-(q:ℤ)*B≤0)
    (excess : 2*(m.choose s:ℝ)<k*(1-(s:ℝ)*(1-(m:ℝ)*p/q))) : census F s<k := by
  classical
  by_contra! many
  let P := Finset.univ.filter (fun v : S => (F v).switches=s)
  have avail : k≤Fintype.card P := by rw [Fintype.card_coe];exact many
  let select (i : Fin k) : P := (Fintype.equivFin P).symm ⟨i.val,by omega⟩
  let f : Fin k ↪ S := ⟨fun i => (select i).val,by
    intro i j eq
    have h:=congrArg (Fintype.equivFin P) (Subtype.ext eq : select i=select j)
    dsimp [select] at h
    simpa [Fin.ext_iff] using h⟩
  have bound:=finite_mark_average f hl F profile m s p q hm hq mpq
    (fun i => (Finset.mem_filter.mp (select i).property).2)
    (fun A B small real => rounding A B (by simpa using small) real)
  simp only [Fintype.card_fin] at bound
  linarith

theorem middle {S : Finset Point} {lam : ℝ} (margin : 2*π/11<lam)
    (F : S → Row) (profile : IsProfile S lam F) : census F 3≤26 := by
  have hl : 0<lam := by linarith [pi_pos]
  have period : π/lam<(11:ℝ)/2 := (div_lt_iff₀ hl).mpr (by linarith)
  apply Nat.le_of_lt_succ
  apply cap hl F profile 5 3 27 13 71 (by decide) (by decide) (by decide) _ (by norm_num [Nat.choose])
  intro A B marks cover
  by_cases zero : B=0
  · subst B
    simp at cover
    omega
  · have bp : (0:ℝ)<B := by exact_mod_cast (show 0<B by omega)
    have l:=mul_lt_mul_of_pos_left period bp
    have strict : (2:ℝ)*A<11*B := by linarith
    have h : 2*A<11*B := by exact_mod_cast strict
    omega

theorem capacity (S : Finset Point) (hs : 2≤S.card) {lam : ℝ}
    (margin : 2*π/11<lam) (hp : lam≤π)
    (legal : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a≠b → a≠c → b≠c →
      EuclideanGeometry.angle a b c≤π-lam) : S.card≤38 := by
  have hl : 0<lam := by linarith [pi_pos]
  obtain ⟨F,profile,budget,_,top⟩ := planar_switch_profile S hs hl hp legal
  let r := min 1 (lam/(π/5))
  have wp : 0<π/5 := by positivity
  have high : 10/11<r := lt_min (by norm_num) ((lt_div_iff₀ wp).mpr (by linarith))
  have r₀ : 0≤r := by linarith
  have r₁ : r≤1 := min_le_left _ _
  have gap : r*(π/5)≤lam := (le_div_iff₀ wp).mp (min_le_right _ _)
  have avg (s : ℕ) := stratum_average (by decide : 0<5) r₀ r₁ gap S F profile s
  have hull : census F 1≤10 := by
    have h := avg 1
    norm_num [Nat.choose] at h
    by_contra! bad
    have many : (11:ℝ)≤census F 1 := by exact_mod_cast bad
    nlinarith [mul_nonneg (sub_nonneg.mpr many) r₀]
  have width : π/lam-(5:ℝ)<1/2 := by
    have h : π/lam<(11:ℝ)/2 := (div_lt_iff₀ hl).mpr (by linarith)
    linarith
  have highest : census F 5≤2 := top 5 (by decide) width
  have mid := middle margin F profile
  have bound : census F 1+census F 3+census F 5≤38 := by omega
  have small (v : S) : (F v).switches<6 := by
    have b := (budget v).2
    have g : π<(6:ℝ)*lam := by linarith [pi_pos]
    exact_mod_cast lt_of_mul_lt_mul_right (lt_of_le_of_lt b g) hl.le
  have empty (s : ℕ) (even : s%2=0) : census F s=0 := by
    unfold census
    simp only [Finset.card_eq_zero,Finset.filter_eq_empty_iff]
    intro v _ eq
    have odd := (budget v).1
    omega
  have total := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset S))
    (t := Finset.range 6) (f := fun v => (F v).switches)
    (fun v _ => Finset.mem_range.mpr (small v))
  have sum : S.card=∑ s ∈ Finset.range 6, census F s := by simpa [census] using total
  rw [sum]
  simpa [Finset.sum_range_succ,empty 0 (by decide),empty 2 (by decide),empty 4 (by decide)] using bound

theorem guaranteed_thirty_nine {N : ℕ} (hn : 39≤N) : Guaranteed N (9*π/11) := by
  intro S sn
  apply (hasLargeAngle_iff_le_maxAngle (by omega : 3≤S.card)).mpr
  by_contra! strict
  let lam := π-maxAngle S
  have margin : 2*π/11<lam := by dsimp [lam]; linarith
  have hp : lam≤π := by dsimp [lam]; linarith [maxAngle_nonneg S]
  have cap := capacity S (by omega) margin hp (by
    intro a ha b hb c hc ab ac bc
    simpa [lam] using angle_le_maxAngle ha hb hc ab ac bc)
  omega

/-- Equality in the original minimax problem, using the imported ordinary
three-cluster Szekeres--Sendov upper construction at n=5. -/
theorem alpha_thirty_nine : JSP404.alpha 39=9*π/11 := by
  apply le_antisymm _ (le_alpha (guaranteed_thirty_nine le_rfl))
  have upper := alpha_le_sendov_intermediate_upper (n:=5) (N:=39) (by decide) (by decide) (by decide)
  convert upper using 1 <;> norm_num <;> ring

end R43.FiniteStrata
#print axioms R43.FiniteStrata.cap
#print axioms R43.FiniteStrata.middle
#print axioms R43.FiniteStrata.alpha_thirty_nine
