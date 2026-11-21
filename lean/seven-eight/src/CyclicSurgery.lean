import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

namespace R53.Surgery

noncomputable def slot (x : ℝ) : ℕ := ⌊x⌋₊-1
noncomputable def bump (x y : ℝ) : ℕ := slot (x+y)-slot x-slot y

private theorem floor_sum {x y : ℝ} (hx : 0≤x) (hy : 0≤y) :
    ⌊x⌋₊+⌊y⌋₊≤⌊x+y⌋₊ := by
  apply Nat.le_floor
  push_cast
  linarith [Nat.floor_le hx,Nat.floor_le hy]

theorem slot_sum {x y : ℝ} (hx : 0≤x) (hy : 0≤y) :
    slot x + slot y ≤ slot (x+y) := by have h:=floor_sum hx hy;unfold slot;omega

private theorem account {x y : ℝ} (hx : 0≤x) (hy : 0≤y) :
    slot (x+y)=slot x+slot y+bump x y := by
  have h:=slot_sum hx hy
  unfold bump; omega

private theorem join {x y z : ℝ} (hx : 0≤x) (hy : 0≤y) (hz : 0≤z) :
    bump x y + bump (x+y) z = bump y z + bump x (y+z) := by
  have a := account hx hy
  have b := account (add_nonneg hx hy) hz
  have c := account hy hz
  have d := account hx (add_nonneg hy hz)
  rw [add_assoc] at b
  omega

private theorem large {x y : ℝ} (hx : 1≤x) (hy : 1≤y) : 1≤bump x y := by
  have a := (Nat.one_le_floor_iff _).mpr hx
  have b := (Nat.one_le_floor_iff _).mpr hy
  have h := floor_sum (by linarith : 0≤x) (by linarith : 0≤y)
  unfold bump slot
  omega

private theorem pow_mono {x y : ℕ} (h : x≤y) : (2:ℕ)^x≤2^y :=
  Nat.pow_le_pow_right (by decide) h

/-- The common path consists of all row factors from c through d to u.
The lower bound two uses the two unaffected rows in a five-edge cycle. -/
theorem remove_one {u a b c : ℝ} (hu : 0≤u) (ha : 0≤a) (hb : 0≤b) (hc : 0≤c)
    {P : ℕ} (two : 2≤P) (heavy : 1≤bump a b) :
    2^bump u a+2^bump a b+2^bump b c+P ≤
      (2^bump a b)*(2^bump u (a+b)+2^bump (a+b) c+P) := by
  have h := join hu ha hb
  have k := join ha hb hc
  have l := pow_mono (show bump u a ≤ bump a b+bump u (a+b) by omega)
  have r := pow_mono (show bump b c ≤ bump a b+bump (a+b) c by omega)
  rw [pow_add] at l r
  have mag : 2 ≤ (2:ℕ)^bump a b := by simpa using pow_mono heavy
  obtain ⟨i,hi⟩ := Nat.exists_eq_add_of_le two
  obtain ⟨j,hj⟩ := Nat.exists_eq_add_of_le mag
  have pay : 2^bump a b+P≤2^bump a b*P := by rw [hi,hj];nlinarith
  nlinarith

/-- When four successive rows have their baseline weight, removing the
middle two leaves both neighboring rows with at least two such weights.
P may contain arbitrary weights on the other path. -/
theorem remove_two {u a b c d : ℝ} (hu : 0≤u) (ha : 0≤a) (hb : 0≤b) (hc : 0≤c)
    (hd : 0≤d) (ua : 1≤u+a) (ab : 1≤a+b) (bc : 1≤b+c) (cd : 1≤c+d)
    (light₁ : bump u a=0) (light₂ : bump a b=0) (light₃ : bump b c=0)
    (light₄ : bump c d=0) (P : ℕ) :
    2^bump u a+2^bump a b+2^bump b c+2^bump c d+P ≤
      2^(bump a b+bump (a+b) c)*(2^bump u (a+b+c)+2^bump (a+b+c) d+P) := by
  let Q := bump a b+bump (a+b) c
  have h1 := join hu ha hb
  have h2 := join hu (add_nonneg ha hb) hc
  have h3 := join (add_nonneg hu ha) hb hc
  rw [←add_assoc u a b] at h2
  have h4 := join (add_nonneg ha hb) hc hd
  have el : 1≤Q+bump u (a+b+c) := by have h:=large ua bc;dsimp [Q];omega
  have er : 1≤Q+bump (a+b+c) d := by have h:=large ab cd;dsimp [Q];omega
  have l := pow_mono el
  have r := pow_mono er
  rw [pow_add] at l r
  have base : 1≤(2:ℕ)^Q := Nat.succ_le_of_lt (by positivity)
  have pay := Nat.mul_le_mul_right P base
  change _ ≤ 2^Q*_
  simp [light₁,light₂,light₃,light₄] at *
  nlinarith

end R53.Surgery
#print axioms R53.Surgery.remove_one
#print axioms R53.Surgery.remove_two
