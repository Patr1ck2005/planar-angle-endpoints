import CyclicCapacity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

namespace SendovCycle
open scoped Nat

/-- Real-valued version with the actual natural floor at every unmerged
and merged half-arc. n is the floor of the one-period total. -/
theorem sharp_real_arc_capacity (a : Nat → ℝ) (t : Nat) (ht : 5 ≤ t)
    (hp : ∀ i, a (i+t)=a i) (ha : ∀ i, 0 ≤ a i)
    (hlegal : ∀ i, 1 ≤ a i + a (i+1))
    (hn : 3 ≤ ⌊seg a 0 t⌋₊) (low : Bool)
    (hL : low=true → 2*seg a 0 t < 2*(⌊seg a 0 t⌋₊:ℝ)+1) :
    let n := ⌊seg a 0 t⌋₊
    let b := fun j => ⌊a j⌋₊-1
    let B := seg b 0 t
    seg (fun j => 2^(B - b j - b (j+1) + (⌊a j+a (j+1)⌋₊-1))) 0 t ≤
      (if low then 6 else 7) * 2^(n-3) := by
  have slot (x : ℝ) (hx : 0 ≤ x) : floorSlot x ⌊x⌋₊ :=
    ⟨Nat.floor_le hx, Nat.lt_floor_add_one _⟩
  have hnneg (i k : Nat) : 0 ≤ seg a i k := by
    induction k generalizing i with
    | zero => simp [seg]
    | succ k ih => exact add_nonneg (ha _) (ih _)
  exact sharp_arc_capacity a (fun i => ⌊a i⌋₊) (fun i => ⌊a i+a (i+1)⌋₊)
    t ⌊seg a 0 t⌋₊ low ht hn hp (fun i => slot _ (ha i))
    (fun i => slot _ (add_nonneg (ha _) (ha _))) hlegal
    (slot _ (hnneg 0 t)) hL

#print axioms sharp_real_arc_capacity
end SendovCycle
