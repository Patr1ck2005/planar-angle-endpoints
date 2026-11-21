import MarkedRows

noncomputable section
namespace R37.RowCompression
open Real R37.SignedFan R37.Seventeen
open scoped BigOperators

private theorem mark_cases {F : Row} {j : ℕ} (h : j∈localMarks F) :
    (j<F.n ∧ F.step j=1) ∨ (j=F.n ∧ F.seam=1) := by
  by_cases e : F.seam=1 <;> simp [localMarks,e] at h <;> grind

private theorem mark_step {F : Row} {j : ℕ} (hj : j<F.n) (h : F.step j=1) :
    j ∈ localMarks F := by
  by_cases e : F.seam=1 <;> simp [localMarks,e,h,hj]

private theorem mark_seam {F : Row} (h : F.seam=1) : F.n ∈ localMarks F := by
  simp [localMarks,h]

/-- A common integer chart for finitely many signed rows; all marked gaps use
the same integral lower bound, and coincident directions retain one coordinate. -/
theorem positions_global {K : Type*} [Fintype K] (G : K → Row) (unit period : ℕ)
    {lam : ℝ} (hl : 0<lam) (rows : ∀ v, (G v).Legal lam)
    (rounding : ∀ A B : ℕ, A ≤ ∑ v, (G v).switches →
      (A:ℝ) ≤ (B:ℝ)*(π/lam) → (unit:ℤ)*A-(period:ℤ)*B≤0) :
    ∃ c : K → ℕ → ℤ,
      (∀ v j, 0 ≤ c v j ∧ c v j ≤ period) ∧
      (∀ v, Monotone (c v)) ∧
      (∀ v j, j < (G v).n → (unit:ℤ)*((G v).step j : ℤ) ≤ c v (j+1)-c v j) ∧
      (∀ v, (unit:ℤ)*((G v).seam : ℤ) ≤ period-c v (G v).n+c v 0) ∧
      (∀ v w i j, (G v).u i = (G w).u j → c v i=c w j) ∧
      ∃ z : Bearing → ℤ, Monotone z ∧ (∀ u, 0≤z u ∧ z u≤period) ∧
        (∀ v j, c v j=z (direction (G v) j)) := by
  classical
  let I := (v : K) × ↥(localMarks (G v))
  let src (a : I) := direction (G a.1) a.2.val
  let dst (a : I) := if a.2.val < (G a.1).n then direction (G a.1) (a.2.val+1)
    else direction (G a.1) 0
  let wrap (a : I) : ℕ := if a.2.val < (G a.1).n then 0 else 1
  let x (u : Bearing) := u.val/lam
  have nmarks : Fintype.card I = ∑ v, (G v).switches := by
    dsimp [I]
    rw [Fintype.card_sigma]
    simp only [Fintype.card_coe, card_localMarks]
  have original (a : I) : 1-(wrap a : ℝ)*(π/lam) ≤ x (dst a)-x (src a) := by
    rcases mark_cases a.2.property with ⟨lt,st⟩ | ⟨eq,se⟩
    · have h := (G a.1).step_budget (rows a.1) a.2.val
      rw [st] at h
      simp only [Nat.cast_one,one_mul] at h
      simp [wrap,dst,src,x,direction,lt,←sub_div]
      exact (le_div_iff₀ hl).2 (by simpa using h)
    · have h := (G a.1).seam_budget (rows a.1)
      rw [se] at h
      simp only [Nat.cast_one,one_mul] at h
      simp [wrap,dst,src,x,direction,eq]
      rw [←sub_div, ←add_div]
      apply (le_div_iff₀ hl).2
      linarith
  obtain ⟨z,range,mono,marks⟩ := R37.DirectionCompression.bearingPositions src dst wrap
    unit period (π/lam) x (by positivity)
    (fun u => ⟨div_nonneg u.property.1 hl.le, div_le_div_of_nonneg_right u.property.2.le hl.le⟩)
    original (fun A B ha hb => rounding A B (by rwa [←nmarks]) hb)
  let c (v : K) (j : ℕ) := z (direction (G v) j)
  have mon (v : K) : Monotone (c v) := by
    intro i j le
    apply mono
    apply div_le_div_of_nonneg_right _ hl.le
    apply (G v).sorted.monotone
    exact min_le_min_right _ le
  refine ⟨c,fun v j => range _,mon,?_,?_,?_,z,?_,range,fun _ _ => rfl⟩
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
      change (unit:ℤ)*((G v).seam : ℤ) ≤ period-z _+z _
      rw [se]; push_cast; simpa [mul_one] using (show (unit:ℤ) ≤ period-z _+z _ by omega)
    · have zz : (G v).seam=0 := by
        dsimp [Row.seam] at se ⊢
        split <;> simp_all
      have l := (range (direction (G v) 0)).1
      have u := (range (direction (G v) (G v).n)).2
      dsimp [c]
      rw [zz]; simp; omega
  · intro v w i j he
    exact congrArg z (Subtype.ext he)

  · intro a b le
    exact mono _ _ (div_le_div_of_nonneg_right le hl.le)

theorem positions {K : Type*} [Fintype K] (G : K → Row) (unit period : ℕ)
    {lam : ℝ} (hl : 0<lam) (rows : ∀ v, (G v).Legal lam)
    (rounding : ∀ A B : ℕ, A ≤ ∑ v, (G v).switches →
      (A:ℝ) ≤ (B:ℝ)*(π/lam) → (unit:ℤ)*A-(period:ℤ)*B≤0) :
    ∃ c : K → ℕ → ℤ,
      (∀ v j, 0 ≤ c v j ∧ c v j ≤ period) ∧
      (∀ v, Monotone (c v)) ∧
      (∀ v j, j < (G v).n → (unit:ℤ)*((G v).step j : ℤ) ≤ c v (j+1)-c v j) ∧
      (∀ v, (unit:ℤ)*((G v).seam : ℤ) ≤ period-c v (G v).n+c v 0) ∧
      (∀ v w i j, (G v).u i = (G w).u j → c v i=c w j) := by
  obtain ⟨c,bd,mo,gap,wrap,shared,_⟩ := positions_global G unit period hl rows rounding
  exact ⟨c,bd,mo,gap,wrap,shared⟩

#print axioms positions_global
#print axioms positions
end R37.RowCompression
