import FiveBoardBound
namespace R67.Five

noncomputable def digit (s : ℝ) : ℕ := ⌊s⌋₊-1

theorem positive_digit {s : ℝ} (hs : 0≤s) (pos : 0<digit s) : (digit s:ℝ)+1≤s := by
  have one : 1≤⌊s⌋₊ := by unfold digit at pos;omega
  have bound:=Nat.floor_le hs
  simp [digit,Nat.cast_sub one] at *
  linarith

/-- The lower bound on circumference directly from the actual four floor-digits on each marked row. -/
theorem bound_digits {w : Word} {u h k : ℕ} (cert : Proved w u h) (hu : u<5) (hk : k≤30)
    (g : ℕ→ℝ) (lower : ∀j,j<10 → 0≤g j) (upper : ∀j,j<10 → g j≤2)
    (tri : ∀ a∈triComplements w,1≤total g a)
    (scores : ∀ v,v<5 → v≠u → k+weight v h≤rowSum (fun i a=>digit (total g (rowArc w i a))) v) :
    (k:ℝ)+(goal h:ℝ)/2≤total g (List.range 10) := by
  have pos (v a : ℕ) : 0≤total g (rowArc w v a) := by
    apply List.sum_nonneg
    intro _ hh
    obtain ⟨j,hj,rfl⟩:=List.mem_map.mp hh
    exact lower j (mem_arc hj)
  have est:=bound cert hu hk g _ lower upper tri (fun v _ _ a _ hp=>positive_digit (pos v a) hp) scores
  linarith

end R67.Five
#print axioms R67.Five.bound_digits
