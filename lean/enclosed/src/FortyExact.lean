import AverageStrata
import JSP404.ThreeClusterGeometry

noncomputable section
namespace R42.Forty
open Real JSP404 R37.SignedFan R40.EvenTail R42.Average

/-- The five-bin capacity is an ordinary planar theorem, including all hull and
interior cases, for any positive defect strictly above 2pi/11. -/
theorem capacity (S : Finset Point) (hs : 2≤S.card) {lam : ℝ}
    (margin : 2*π/11<lam) (hp : lam≤π)
    (legal : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a≠b → a≠c → b≠c →
      EuclideanGeometry.angle a b c≤π-lam) : S.card≤39 := by
  have hl : 0<lam := by linarith [pi_pos]
  obtain ⟨F,profile,budget,_,top⟩ := planar_switch_profile S hs hl hp legal
  let r := min 1 (lam/(π/5))
  have wp : 0<π/5 := by positivity
  have high : 10/11<r := lt_min (by norm_num) ((lt_div_iff₀ wp).mpr (by linarith))
  have r₀ : 0≤r := by linarith
  have r₁ : r≤1 := min_le_left _ _
  have gap : r*(π/5)≤lam := (le_div_iff₀ wp).mp (min_le_right _ _)
  have avg (s : ℕ) := stratum_average (by decide : 0<5) r₀ r₁ gap S F profile s
  have middle : (census F 3:ℝ)*(3*r-2)≤20 := by
    have h := avg 3
    norm_num [Nat.choose] at h
    linarith
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
  have bound := FullSwitchTriangle.five_bin_count high hull middle highest
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

theorem guaranteed_forty {N : ℕ} (hn : 40≤N) : Guaranteed N (9*π/11) := by
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
theorem alpha_forty : JSP404.alpha 40=9*π/11 := by
  apply le_antisymm _ (le_alpha (guaranteed_forty le_rfl))
  have upper := alpha_le_sendov_intermediate_upper (n:=5) (N:=40) (by decide) (by decide) (by decide)
  convert upper using 1 <;> norm_num <;> ring

end R42.Forty
#print axioms JSP404.alpha_le_sendov_intermediate_upper
#print axioms R42.Forty.capacity
#print axioms R42.Forty.guaranteed_forty
#print axioms R42.Forty.alpha_forty
