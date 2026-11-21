import IndexedStatistic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.Floor.Ring

noncomputable section
namespace R56.Clearance

variable {J : Type*} [Fintype J]

def rowCapacity (g : J→ℝ) (lam : ℝ) : ℕ := ∑ j, (⌊g j/lam⌋₊ - 1)

def slot (g : J→ℝ) (d : ℕ) (x : J×Fin d) : ℝ := g x.1 / ((x.2.val : ℝ)+2)

/-- The explicit order statistic in the d values gⱼ/2 through gⱼ/(d+1)
from every gap, with labeled repetitions. -/
def rowLimit (g : J→ℝ) (d : ℕ) : ℝ := kth (slot g d) d

private theorem slot_test {g lam : ℝ} (gn : 0≤g) (hl : 0<lam) (k : ℕ) :
    lam≤g/((k:ℝ)+2) ↔ k<⌊g/lam⌋₊-1 := by
  have div : 0≤g/lam := div_nonneg gn hl.le
  have floor : k+2≤⌊g/lam⌋₊ ↔ ((k:ℝ)+2)≤g/lam := by
    simpa using (Nat.le_floor_iff div (n:=k+2))
  have denom : (0:ℝ)<k+2 := by positivity
  rw [le_div_iff₀ denom,show k<⌊g/lam⌋₊-1 ↔ k+2≤⌊g/lam⌋₊ by omega,floor,le_div_iff₀ hl,mul_comm]

/-- Count the labeled slots using the exactly truncated contribution of each gap. -/
theorem slot_count (g : J→ℝ) (gn : ∀ j, 0≤g j) (d : ℕ) {lam : ℝ} (hl : 0<lam) :
    atLeast (slot g d) lam=∑ j, min d (⌊g j/lam⌋₊-1) := by
  classical
  let n (j : J) := ⌊g j/lam⌋₊-1
  let A := {x : J×Fin d // lam≤slot g d x}
  let B := (j : J) × Fin (min d (n j))
  have test (x : J×Fin d) : lam≤slot g d x ↔ x.2.val<n x.1 := slot_test (gn _) hl _
  let e : A≃B := {
    toFun := fun x => ⟨x.val.1,⟨x.val.2.val,lt_min x.val.2.isLt ((test _).mp x.property)⟩⟩
    invFun := fun y =>
      ⟨(y.1,⟨y.2.val,lt_of_lt_of_le y.2.isLt (min_le_left _ _)⟩),
        (test _).mpr (lt_of_lt_of_le y.2.isLt (min_le_right _ _))⟩
    left_inv := by rintro ⟨⟨j,k⟩,h⟩; rfl
    right_inv := by rintro ⟨j,k⟩; rfl
  }
  calc atLeast (slot g d) lam = Fintype.card A := (Fintype.card_subtype _).symm
       _ = Fintype.card B := Fintype.card_congr e
       _ = _ := by simp [B,n,Fintype.card_sigma]

/-- Capping each nonnegative summand at the target d cannot change whether
the sum reaches that target. -/
theorem clip_sum (a : J→ℕ) (d : ℕ) : d≤∑ j,min d (a j) ↔ d≤∑ j,a j := by
  classical
  constructor
  · intro h
    exact h.trans (Finset.sum_le_sum (fun j _=>min_le_right _ _))
  · intro h
    by_cases one : ∃ j, d≤a j
    · obtain ⟨j,hj⟩ := one
      calc d = min d (a j) := (min_eq_left hj).symm
           _ ≤ ∑ i,min d (a i) := Finset.single_le_sum (fun i _=>Nat.zero_le (min d (a i))) (Finset.mem_univ j)
    · have cap : ∀ j, min d (a j)=a j := fun j=>min_eq_right (le_of_not_ge (fun e=>one ⟨j,e⟩))
      simpa only [cap] using h

/-- Exact weak endpoint and arbitrary positive clearance. -/
theorem capacity_iff (g : J→ℝ) (gn : ∀ j, 0≤g j) {d : ℕ} (hd : 0<d) {lam : ℝ} (hl : 0<lam) :
    d≤rowCapacity g lam ↔ lam≤rowLimit g d := by
  rw [rowLimit,le_kth_iff _ hd hl,slot_count g gn d hl,clip_sum,rowCapacity]

theorem rowLimit_zero {g : J→ℝ} (hz : ∀ j, g j=0) {d : ℕ} (hd : 0<d) :
    rowLimit g d=0 := by
  have hn := kth_nonneg (slot g d) d
  change 0≤rowLimit g d at hn
  apply le_antisymm _ hn
  by_contra! pos
  have H := (capacity_iff g (fun j=>le_of_eq (hz j).symm) hd pos).mpr le_rfl
  simp [rowCapacity,hz] at H
  omega

#print axioms slot_count
#print axioms capacity_iff
#print axioms rowLimit_zero
end R56.Clearance
