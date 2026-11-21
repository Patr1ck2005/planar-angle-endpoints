import TopStratum
import TwistedCapacity
import JSP404.ClassicalBounds

noncomputable section
namespace R40.EvenTail
open Real JSP404 R37.SignedFan

/-- The one-vacancy parity gain of R36 on a particular non-top stratum. -/
def extra (m s : ℕ) := if s%2=1 ∧ (m-1).choose (s-1)%2=0 then 1 else 0

def extraSum (m : ℕ) := ∑ s ∈ Finset.range m, extra m s

def cap (m : ℕ) := 2^m-(m/2+extraSum m+(2*m-4))

def census {S : Finset Point} (F : S → Row) (s : ℕ) : ℕ :=
  (Finset.univ.filter (fun v : S => (F v).switches=s)).card

/-- The one geometric input isolated from the R36 rotation proof.
It is required only on the odd strata strictly below the top stratum. -/
def LowerRotations (m : ℕ) : Prop :=
  ∀ (S : Finset Point) (lam : ℝ) (F : S → Row), π/(m:ℝ)<lam →
    IsProfile S lam F → ∀ s, s<m-1 → s%2=1 →
    census F s+1+extra m s≤2*m.choose s

private theorem total {S : Finset Point} (F : S → Row) {m : ℕ}
    (h : ∀ v, (F v).switches<m) :
    (∑ s ∈ Finset.range m, census F s)=S.card := by
  have hh := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset S))
    (t := Finset.range m) (f := fun v => (F v).switches)
    (fun v _ => Finset.mem_range.mpr (h v))
  simpa [census] using hh.symm

theorem census_cap (m : ℕ) (hm : 4≤m) (even : m%2=0) {S : Finset Point}
    (F : S → Row) (hsmall : ∀ v, (F v).switches<m) (htop : census F (m-1)≤3)
    (low : ∀ s, s<m-1 → s%2=1 → census F s+1+extra m s≤2*m.choose s) :
    S.card≤cap m := by
  classical
  let count (s : ℕ) := census F s+extra m s+(if s=m-1 then 2*m-4 else 0)
  have last : m-1+1=m := by omega
  have odd : (m-1)%2=1 := by omega
  have cm : m.choose (m-1)=m := by
    rw [Nat.choose_symm (show 1≤m by omega)]
    simp
  have co : (m-1).choose ((m-1)-1)=m-1 := by
    rw [Nat.choose_symm (show 1≤m-1 by omega)]
    simp
  have top0 : extra m (m-1)=0 := by simp [extra,odd,co]
  have empty (s : ℕ) (hs : s<m) (ne : s%2≠1) : count s=0 := by
    have ee : census F s=0 := by
      unfold census
      simp only [Finset.card_eq_zero,Finset.filter_eq_empty_iff]
      intro v _ h
      exact ne (h ▸ (F v).switches_odd)
    have ne' : s≠m-1 := by omega
    simp [count,ee,extra,ne,ne']
  have loss (s : ℕ) (hs : s<m) (ho : s%2=1) : count s+1≤2*m.choose s := by
    by_cases ht : s=m-1
    · subst s
      simp only [count,top0,add_zero,ite_true,cm]
      omega
    · have h := low s (by omega) ho
      simp [count,ht]
      omega
  have bound := TwistedCapacity.all_strata_cap (by omega : 0<m) count empty loss
  have one : (∑ s ∈ Finset.range m, if s=m-1 then 2*m-4 else 0)=2*m-4 := by
    simp [Finset.mem_range,show m-1<m by omega]
  simp only [count,Finset.sum_add_distrib,one,total F hsmall] at bound
  change S.card+extraSum m+(2*m-4)+m/2+(if m%2=1 then 2 else 0)≤2^m at bound
  unfold cap
  omega

/-- Complete reduction to the original minimax threshold. The upper bound
is the unconditional Szekeres construction. Only LowerRotations is a premise. -/
theorem alpha_even_tail (m N : ℕ) (hm : 4≤m) (even : m%2=0)
    (rot : LowerRotations m) (hN : 3≤N) (lo : cap m<N) (hi : N≤2^m) :
    JSP404.alpha N=(1-1/(m:ℝ))*π := by
  apply le_antisymm (alpha_le_szekeres_upper hN (by omega) hi)
  apply le_alpha
  intro S hcard
  apply (hasLargeAngle_iff_le_maxAngle (by omega : 3≤S.card)).mpr
  by_contra! strict
  let lam := π-maxAngle S
  have mp : 0<(m:ℝ) := by exact_mod_cast (show 0<m by omega)
  have hh : (1-1/(m:ℝ))*π=π-π/m := by ring
  rw [hh] at strict
  have hgap : π/(m:ℝ)<lam := by dsimp [lam]; linarith
  have hl : 0<lam := lt_trans (div_pos pi_pos mp) hgap
  have hp : lam≤π := by dsimp [lam]; linarith [maxAngle_nonneg S]
  have legal : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a≠b → a≠c → b≠c →
      EuclideanGeometry.angle a b c≤π-lam := by
    intro a ha b hb c hc ab ac bc
    simpa [lam] using angle_le_maxAngle ha hb hc ab ac bc
  obtain ⟨F,h,budget,_⟩ := planar_switch_profile S (by omega) hl hp legal
  have g : π<(m:ℝ)*lam := by
    have hh := (div_lt_iff₀ mp).mp hgap
    linarith [mul_comm (m:ℝ) lam]
  have small (v : S) : (F v).switches<m := by
    have e := (budget v).2
    exact_mod_cast (lt_of_mul_lt_mul_right (lt_of_le_of_lt e g) hl.le)
  have cast_sub : ((m-1:ℕ):ℝ)=(m:ℝ)-1 := by rw [Nat.cast_sub (by omega)]; norm_num
  have width : π/lam-((m-1:ℕ):ℝ)<1 := by
    rw [cast_sub]
    linarith [(div_lt_iff₀ hl).mpr g]
  have top := R40.TopStratum.at_most_three_top S hl F h (m-1) (by omega) width
  have cap' := census_cap m hm even F small top (rot S lam F hgap h)
  omega

example : cap 4=10 ∧ cap 6=52 ∧ cap 8=240 ∧ cap 10=1000 := by decide

end R40.EvenTail
#print axioms R40.EvenTail.census_cap
#print axioms R40.EvenTail.alpha_even_tail
