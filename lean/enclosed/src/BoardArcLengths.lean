import FiveBoardSlots
noncomputable section
namespace R67.Circle
open Finset
abbrev Slot := Fin 10
def ext (x : Slot→ℝ) (T : ℝ) (a : ℕ) := if h:a<10 then x ⟨a,h⟩ else x 0+T
def gaps (x : Slot→ℝ) (T : ℝ) (a : Slot) := ext x T (a.val+1)-ext x T a.val
def pre (a : ℕ) := univ.filter (fun t : Slot=>t.val<a)
def interval (a b : Slot) := pre b.val \ pre a.val
def arc (a b : Slot) := if a≤b then interval a b else univ \ interval b a
def length (g : Slot→ℝ) (s : Finset Slot) := ∑ j∈s,g j

private theorem prefix_sum (x : Slot→ℝ) (T : ℝ) (a : ℕ) (ha : a≤10) :
    length (gaps x T) (pre a)=ext x T a-x 0 := by
  unfold length
  calc _=∑ i∈range a,(ext x T (i+1)-ext x T i) := by
            apply sum_bij (fun (j : Slot) _=>j.val)
            · intro j h;exact mem_range.mpr (mem_filter.mp h).2
            · intro j _ k _ e;exact Fin.ext e
            · intro j hj;have hj':j<a:=mem_range.mp hj
              exact ⟨⟨j,by omega⟩,mem_filter.mpr ⟨mem_univ _,hj'⟩,rfl⟩
            · intro j h;rfl
       _=ext x T a-ext x T 0:=sum_range_sub ..
       _=_:=by simp [ext]
theorem total (x : Slot→ℝ) (T : ℝ) : length (gaps x T) univ=T := by
  have p:=prefix_sum x T 10 le_rfl
  have eq : pre 10=univ := by ext i;simp [pre,i.isLt]
  simpa [eq,ext] using p

private theorem interval_sum (x : Slot→ℝ) (T : ℝ) {a b : Slot} (ab : a≤b) :
    length (gaps x T) (interval a b)=x b-x a := by
  have sub : pre a.val⊆pre b.val := by
    intro j hj;exact mem_filter.mpr ⟨mem_univ _,lt_of_lt_of_le (mem_filter.mp hj).2 ab⟩
  have u:=sum_sdiff sub (f:=gaps x T)
  change length (gaps x T) (interval a b)+length (gaps x T) (pre a.val)=length (gaps x T) (pre b.val) at u
  rw [prefix_sum _ _ _ a.isLt.le,prefix_sum _ _ _ b.isLt.le] at u
  simp only [ext,dite_eq_left a.isLt,dite_eq_left b.isLt] at u
  linarith

theorem arc_sum (x : Slot→ℝ) (T : ℝ) (a b : Slot) :
    length (gaps x T) (arc a b)=(if a≤b then x b-x a else x b+T-x a) := by
  by_cases h:a≤b
  · simpa [arc,h] using interval_sum x T h
  · have p:=sum_sdiff (subset_univ (interval b a)) (f:=gaps x T)
    change length (gaps x T) (univ \ interval b a)+length (gaps x T) (interval b a)=length (gaps x T) univ at p
    rw [interval_sum _ _ (le_of_not_ge h),total] at p
    simp only [arc,if_neg h]
    linarith

theorem gap_nonneg (x : Slot→ℝ) (T : ℝ) (mono : Monotone x) (bd : ∀i,0≤x i ∧ x i<T) :
    ∀j,0≤gaps x T j := by
  intro j
  by_cases h:j.val+1<10
  · simp only [gaps,ext,dite_eq_left h,dite_eq_left j.isLt]
    exact sub_nonneg.mpr (mono (show j≤⟨j.val+1,h⟩ from Nat.le_succ _))
  · simp only [gaps,ext,dite_eq_right h,dite_eq_left j.isLt]
    linarith [(bd 0).1,(bd j).2]

theorem arc_complement (x : Slot→ℝ) (T : ℝ) (a b : Slot) :
    length (gaps x T) (univ \ arc a b)=T-(if a≤b then x b-x a else x b+T-x a) := by
  have p:=sum_sdiff (subset_univ (arc a b)) (f:=gaps x T)
  change length (gaps x T) (univ \ arc a b)+length (gaps x T) (arc a b)=length (gaps x T) univ at p
  rw [arc_sum,total] at p
  linarith
#print axioms arc_sum
#print axioms gap_nonneg
end R67.Circle
