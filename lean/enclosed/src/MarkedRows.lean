import NineRows
import DirectionCompression

noncomputable section
namespace R37.Seventeen
open Real R37.SignedFan
open scoped BigOperators

def localMarks (F : Row) : Finset ℕ :=
  let inner := (Finset.range F.n).filter (fun j => F.step j = 1)
  if F.seam = 1 then insert F.n inner else inner

theorem card_localMarks (F : Row) : (localMarks F).card = F.switches := by
  classical
  let inner := (Finset.range F.n).filter (fun j => F.step j=1)
  have hinner : inner.card = F.prefixCount F.n := by
    dsimp [inner, Row.prefixCount]
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : F.b j = F.b (j+1) <;> simp [Row.step,h]
  have hn : F.n ∉ inner := by simp [inner]
  by_cases h : F.seam=1
  · rw [localMarks,if_pos h]
    change (insert F.n inner).card = F.prefixCount F.n + F.seam
    rw [Finset.card_insert_of_notMem hn,hinner,h]
  · have z : F.seam=0 := by
      dsimp [Row.seam] at h ⊢
      split <;> simp_all
    rw [localMarks,if_neg h]
    change inner.card = F.prefixCount F.n + F.seam
    rw [hinner,z,add_zero]

private theorem mark_cases {F : Row} {j : ℕ} (h : j∈localMarks F) :
    (j<F.n ∧ F.step j=1) ∨ (j=F.n ∧ F.seam=1) := by
  by_cases e : F.seam=1 <;> simp [localMarks,e] at h <;> grind

private theorem mark_step {F : Row} {j : ℕ} (hj : j<F.n) (h : F.step j=1) :
    j ∈ localMarks F := by
  by_cases e : F.seam=1 <;> simp [localMarks,e,h,hj]

private theorem mark_seam {F : Row} (h : F.seam=1) : F.n ∈ localMarks F := by
  simp [localMarks,h]

abbrev Bearing := {x : ℝ // 0≤x ∧ x<π}

def direction (F : Row) (j : ℕ) : Bearing := ⟨F.u j,F.bounds (F.idx j)⟩

/-- One shared, order-preserving integer chart for all nine rows. Equal
bearings from different rows use exactly the same integer, including at
the duplicated endpoint of the fundamental interval. -/
theorem compressed_rows {s : ℕ} (G : Fin 9 → Row) (hs : s≤3) {lam : ℝ}
    (margin : 2*π/9 < lam)
    (rows : ∀ v, (G v).switches=s ∧ (G v).Legal lam) :
    ∃ c : Fin 9 → ℕ → ℤ,
      (∀ v j, 0 ≤ c v j ∧ c v j ≤ 22) ∧
      (∀ v, Monotone (c v)) ∧
      (∀ v j, j < (G v).n → 5*((G v).step j : ℤ) ≤ c v (j+1)-c v j) ∧
      (∀ v, 5*((G v).seam : ℤ) ≤ 22-c v (G v).n+c v 0) ∧
      (∀ v w i j, (G v).u i = (G w).u j → c v i=c w j) := by
  classical
  have hl : 0 < lam := by linarith [pi_pos]
  let I := (v : Fin 9) × ↥(localMarks (G v))
  let src (a : I) := direction (G a.1) a.2.val
  let dst (a : I) := if a.2.val < (G a.1).n then direction (G a.1) (a.2.val+1)
    else direction (G a.1) 0
  let wrap (a : I) : ℕ := if a.2.val < (G a.1).n then 0 else 1
  let x (u : Bearing) := u.val/lam
  have nmarks : Fintype.card I ≤ 30 := by
    have elem (v : Fin 9) : Fintype.card ↥(localMarks (G v)) = s := by
      rw [Fintype.card_coe,card_localMarks,(rows v).1]
    dsimp [I]
    rw [Fintype.card_sigma]
    simp [elem] <;> omega
  have original (a : I) : 1-(wrap a : ℝ)*(π/lam) ≤ x (dst a)-x (src a) := by
    rcases mark_cases a.2.property with ⟨lt,st⟩ | ⟨eq,se⟩
    · have h := (G a.1).step_budget (rows a.1).2 a.2.val
      rw [st] at h
      simp only [Nat.cast_one,one_mul] at h
      simp [wrap,dst,src,x,direction,lt,←sub_div]
      exact (le_div_iff₀ hl).2 (by simpa using h)
    · have h := (G a.1).seam_budget (rows a.1).2
      rw [se] at h
      simp only [Nat.cast_one,one_mul] at h
      simp [wrap,dst,src,x,direction,eq]
      rw [←sub_div, ←add_div]
      apply (le_div_iff₀ hl).2
      linarith
  obtain ⟨z,range,mono,marks⟩ := R37.DirectionCompression.bearings22 src dst wrap
    (π/lam) x nmarks (by positivity) (by apply (div_lt_iff₀ hl).2; linarith)
    (fun u => ⟨div_nonneg u.property.1 hl.le, div_le_div_of_nonneg_right u.property.2.le hl.le⟩)
    original
  let c (v : Fin 9) (j : ℕ) := z (direction (G v) j)
  have mon (v : Fin 9) : Monotone (c v) := by
    intro i j le
    apply mono
    apply div_le_div_of_nonneg_right _ hl.le
    apply (G v).sorted.monotone
    exact min_le_min_right _ le
  refine ⟨c,fun v j => range _,mon,?_,?_,?_⟩
  · intro v j hj
    by_cases st : (G v).step j=1
    · let a : I := ⟨v,⟨j,mark_step hj st⟩⟩
      have h := marks a
      simpa [a,src,dst,wrap,hj,st,c] using h
    · have zz : (G v).step j=0 := by
        dsimp [Row.step] at st ⊢
        split <;> simp_all
      rw [zz]; simp
      exact mon v (Nat.le_succ _)
  · intro v
    by_cases se : (G v).seam=1
    · let a : I := ⟨v,⟨(G v).n,mark_seam se⟩⟩
      have h := marks a
      simp [a,src,dst,wrap] at h
      change 5*((G v).seam : ℤ) ≤ 22-z _+z _
      rw [se]; push_cast; omega
    · have zz : (G v).seam=0 := by
        dsimp [Row.seam] at se ⊢
        split <;> simp_all
      have l := (range (direction (G v) 0)).1
      have u := (range (direction (G v) (G v).n)).2
      dsimp [c]
      rw [zz]; push_cast; omega
  · intro v w i j he
    exact congrArg z (Subtype.ext he)

#print axioms card_localMarks
#print axioms compressed_rows
end R37.Seventeen
