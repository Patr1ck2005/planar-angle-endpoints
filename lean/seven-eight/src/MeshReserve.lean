import FiberFan
noncomputable section
namespace R59.Mesh
open Real JSP404 R58.Plane R56.ProfileMass

theorem gap_sum (F : Fan) : (∑ j,gap F j)=π := by
  rw [Fin.sum_univ_castSucc]
  have inside : ∑ j : Fin F.n,gap F j.castSucc = F.u F.n-F.u 0 := by
    calc _=∑ j : Fin F.n,(F.u (j.val+1)-F.u j.val) := by
           apply Finset.sum_congr rfl;intro j _;simp [gap,j.isLt]
         _=_ := by exact (Fin.sum_univ_eq_sum_range (fun n => F.u (n+1)-F.u n) F.n).trans (Finset.sum_range_sub ..)
  rw [inside]
  simp [gap]

theorem gap_nonneg (F : Fan) (j : Fin (F.n+1)) : 0≤gap F j := by
  rw [←centered_gap]
  exact sub_nonneg.mpr ((chart F).ordered (Nat.le_succ _) j.isLt)

private theorem slot {g l : ℝ} {h : ℕ} (gn : 0≤g) (lp : 0<l)
    (small : (h:ℝ)*g≤π) (range : (h:ℝ)*l≤π) :
    ((⌊g/l⌋₊-1:ℕ):ℝ)*l*π ≤ g*(π-h*l) := by
  by_cases zero : ⌊g/l⌋₊=0
  · simp [zero];exact mul_nonneg gn (sub_nonneg.mpr range)
  · have cast : ((⌊g/l⌋₊-1:ℕ):ℝ)=(⌊g/l⌋₊:ℝ)-1 := by rw [Nat.cast_sub (by omega)];simp
    have bound:=(le_div_iff₀ lp).mp (Nat.floor_le (div_nonneg gn lp.le))
    rw [cast]
    nlinarith only [mul_le_mul_of_nonneg_right bound pi_pos.le,mul_le_mul_of_nonneg_right small lp.le]

/-- In an actual legal signed row with every gap at most π/h, h angular
units of the binary budget are unavailable, at every positive defect. -/
theorem reserve (F : Fan) {l : ℝ} (lp : 0<l) (legal : F.Legal l)
    (h : ℕ) (mesh : ∀j,(h:ℝ)*gap F j≤π) : digits F l+h≤⌊π/l⌋₊ := by
  obtain ⟨j,big⟩:=long_gap F legal
  have range : (h:ℝ)*l≤π := (mul_le_mul_of_nonneg_left big (Nat.cast_nonneg _)).trans (mesh j)
  have total := Finset.sum_le_sum (s:=(Finset.univ : Finset (Fin (F.n+1))))
    (fun j _ => slot (gap_nonneg F j) lp (mesh j) range)
  simp only [←Finset.sum_mul,gap_sum,←Nat.cast_sum] at total
  change (digits F l:ℝ)*l*π≤π*(π-h*l) at total
  apply Nat.le_floor
  rw [Nat.cast_add]
  apply (le_div_iff₀ lp).mpr
  apply le_of_mul_le_mul_right (a:=π)
  · nlinarith only [total]
  · exact pi_pos

/-- A scale-independent dyadic budget for a family of rows with potentially
different angular resolutions. -/
theorem kraft {I : Type*} [Fintype I] (w h : I→ℕ) (H n : ℕ) (range : ∀i,h i≤H)
    (tax : (∑i,2^(H-h i))≤2^H) (fit : ∀i,Nat.clog 2 (w i)+h i≤n) :
    (∑ i,w i)≤2^n := by
  have cost (i : I) : 2^H*w i≤2^n*2^(H-h i) := by
    calc _≤2^H*2^(Nat.clog 2 (w i)) := Nat.mul_le_mul_left _ (Nat.le_pow_clog (by decide) _)
         _=2^(H+Nat.clog 2 (w i)) := (pow_add _ _ _).symm
         _≤2^(n+(H-h i)) := Nat.pow_le_pow_right (by decide) (by have := range i;have := fit i;omega)
         _=_ := pow_add _ _ _
  have all:=Finset.sum_le_sum (s:=(Finset.univ : Finset I)) (fun i _=>cost i)
  simp only [←Finset.mul_sum] at all
  have final:=le_trans all (Nat.mul_le_mul_left _ tax)
  rw [Nat.mul_comm (2^n)] at final
  exact Nat.le_of_mul_le_mul_left final (by positivity)
#print axioms reserve
#print axioms kraft
end R59.Mesh
