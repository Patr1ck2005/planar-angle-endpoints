import AverageStrata
import JSP404.ThreeClusterGeometry

noncomputable section
namespace R42.HalfStep
open Real JSP404 R37.SignedFan R40.EvenTail R42.Average

def lowerLayer (m s : ℕ) := (2*m.choose s*(2*m+1)-1)/(2*m+1-s)
def halfCap (m : ℕ) := ∑ s ∈ Finset.range (m+1),
  if s%2=1 then (if s=m then 2 else lowerLayer m s) else 0

private theorem layer {m s : ℕ} (hm : 0<m) (hs : 0<s) (sl : s≤m) {lam : ℝ}
    (margin : 2*π/(2*(m:ℝ)+1)<lam) (S : Finset Point) (F : S → Row)
    (profile : IsProfile S lam F) : census F s≤lowerLayer m s := by
  by_cases z : census F s=0
  · simp [z]
  have cp : (0:ℝ)<census F s := by exact_mod_cast (show 0<census F s by omega)
  have mp : (0:ℝ)<m := by exact_mod_cast hm
  have sp : (0:ℝ)<s := by exact_mod_cast hs
  let w := π/(m:ℝ)
  let d := 2*(m:ℝ)+1
  have dp : 0<d := by dsimp [d]; positivity
  have wp : 0<w := div_pos pi_pos mp
  let b := 2*(m:ℝ)/d
  let r := min 1 (lam/w)
  have identity : b*w=2*π/d := by dsimp [b,w]; field_simp
  have lt : b<r := lt_min ((div_lt_one dp).mpr (by dsimp [d]; linarith))
    ((lt_div_iff₀ wp).mpr (identity ▸ margin))
  have nonneg : 0≤b := div_nonneg (by positivity) dp.le
  have ratio : r*w≤lam := (le_div_iff₀ wp).mp (min_le_right _ _)
  have avg := stratum_average hm (nonneg.trans lt.le) (min_le_left _ _ : r≤1) ratio S F profile s
  have stricter : (census F s:ℝ)*(1-(s:ℝ)*(1-b))<2*(m.choose s:ℝ) := by
    nlinarith [mul_pos cp (mul_pos sp (sub_pos.mpr lt))]
  have dd : d*(1-b)=1 := by
    dsimp [b]
    field_simp
    dsimp [d]
    ring
  have clear := (mul_lt_mul_of_pos_right stricter dp)
  have eq : (census F s:ℝ)*(1-(s:ℝ)*(1-b))*d=(census F s:ℝ)*(d-s) := by
    linear_combination -(census F s:ℝ)*(s:ℝ)*dd
  rw [eq] at clear
  have num : census F s*(2*m+1-s)<2*m.choose s*(2*m+1) := by
    have real : (census F s:ℝ)*((2*m+1-s:ℕ):ℝ)<2*(m.choose s:ℝ)*(2*(m:ℝ)+1) := by
      rw [Nat.cast_sub (by omega : s≤2*m+1)]
      push_cast
      exact clear
    exact_mod_cast real
  unfold lowerLayer
  exact (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)

theorem ordinary_cap (m : ℕ) (hm : 2≤m) (S : Finset Point) (hs : 2≤S.card) {lam : ℝ}
    (margin : 2*π/(2*(m:ℝ)+1)<lam) (hp : lam≤π)
    (legal : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a≠b → a≠c → b≠c →
      EuclideanGeometry.angle a b c≤π-lam) : S.card≤halfCap m := by
  have mp : 0<(m:ℝ) := by exact_mod_cast (show 0<m by omega)
  have dp : 0<2*(m:ℝ)+1 := by positivity
  have ml := (div_lt_iff₀ dp).mp margin
  have hl : 0<lam := lt_trans (div_pos (by positivity) dp) margin
  obtain ⟨F,profile,budget,_,top⟩ := planar_switch_profile S hs hl hp legal
  have width : π/lam-(m:ℝ)<1/2 := by
    have eq : π/lam<(m:ℝ)+1/2 := (div_lt_iff₀ hl).mpr (by linarith)
    linarith
  have small (v : S) : (F v).switches<m+1 := by
    have b := (budget v).2
    have pn : π<((m:ℝ)+1)*lam := by nlinarith
    exact_mod_cast lt_of_mul_lt_mul_right (lt_of_le_of_lt b pn) hl.le
  have eq := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset S))
    (t := Finset.range (m+1)) (f := fun v => (F v).switches)
    (fun v _ => Finset.mem_range.mpr (small v))
  have sum : S.card=∑ s ∈ Finset.range (m+1), census F s := by simpa [census] using eq
  rw [sum]
  apply Finset.sum_le_sum
  intro s mem
  have sl := Finset.mem_range.mp mem
  by_cases odd : s%2=1
  · by_cases isTop : s=m
    · subst s; simpa [odd,census] using top m odd width
    · simpa [odd,isTop] using layer (by omega : 0<m) (by omega : 0<s) (by omega : s≤m) margin S F profile
  · have empty : census F s=0 := by
      unfold census
      simp only [Finset.card_eq_zero,Finset.filter_eq_empty_iff]
      intro v _ eq
      exact odd (eq ▸ (budget v).1)
    simp [odd,empty]

theorem alpha_when_capacity_crossed (m N : ℕ) (hm : 2≤m) (hN : 3≤N)
    (lo : halfCap m<N) (hi : N≤5*2^(m-2)) :
    JSP404.alpha N=(1-2/(2*(m:ℝ)+1))*π := by
  apply le_antisymm (alpha_le_sendov_intermediate_upper hm hN hi)
  apply le_alpha
  intro S sn
  apply (hasLargeAngle_iff_le_maxAngle (by omega : 3≤S.card)).mpr
  by_contra! strict
  let lam := π-maxAngle S
  have margin : 2*π/(2*(m:ℝ)+1)<lam := by
    have eq : (1-2/(2*(m:ℝ)+1))*π=π-2*π/(2*(m:ℝ)+1) := by ring
    rw [eq] at strict
    dsimp [lam]
    linarith
  have cap := ordinary_cap m hm S (by omega) margin
    (by dsimp [lam]; linarith [maxAngle_nonneg S]) (by
      intro a ha b hb c hc ab ac bc
      simpa [lam] using angle_le_maxAngle ha hb hc ab ac bc)
  omega

example : halfCap 3=8 ∧ halfCap 4=19 ∧ halfCap 5=39 ∧ halfCap 6=82 ∧ halfCap 7=165 := by decide

end R42.HalfStep
#print axioms R42.HalfStep.ordinary_cap
#print axioms R42.HalfStep.alpha_when_capacity_crossed
