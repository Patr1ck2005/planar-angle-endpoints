import PlanarProfile

noncomputable section
namespace R37.Seventeen
open Real InnerProductGeometry JSP404 R37.SignedFan

/-- The two outward rays of a shared chord have the same projective
bearing and opposite signs, independently of how each row was built. -/
theorem shared_chord {S : Finset Point} {lam : ℝ} {F : S → Row}
    (profile : IsProfile S lam F) (a b : S) (ab : a ≠ b) :
    ∃ i : Fin ((F a).n+1), ∃ j : Fin ((F b).n+1),
      (F a).bearing i = (F b).bearing j ∧ (F a).sign i ≠ (F b).sign j := by
  have h₁ : b.val ∈ S.erase a.val :=
    Finset.mem_erase.mpr ⟨fun e => ab (Subtype.ext e.symm),b.property⟩
  have h₂ : a.val ∈ S.erase b.val :=
    Finset.mem_erase.mpr ⟨fun e => ab (Subtype.ext e),a.property⟩
  obtain ⟨i,r,hr,hi⟩ := (profile a).1.1 ⟨b.val,h₁⟩
  obtain ⟨j,s,hs,hj⟩ := (profile b).1.1 ⟨a.val,h₂⟩
  change b.val-a.val = _ at hi
  change a.val-b.val = _ at hj
  have nonzero : b.val-a.val ≠ 0 := sub_ne_zero.mpr (fun e => ab (Subtype.ext e.symm))
  have eq : angle (b.val-a.val) (a.val-b.val) = π := by
    rw [← neg_sub b.val a.val,angle_neg_right,angle_self nonzero,sub_zero]
  rw [hi,hj,angle_smul_left_of_pos _ _ hr,angle_smul_right_of_pos _ _ hs,
      angle_oriented ((F a).bounds _) ((F b).bounds _)] at eq
  have ba := (F a).bounds i
  have bb := (F b).bounds j
  have small : |(F a).bearing i - (F b).bearing j| < π := abs_lt.mpr ⟨by linarith,by linarith⟩
  by_cases same : (F a).sign i = (F b).sign j
  · rw [if_pos same] at eq
    linarith
  · rw [if_neg same] at eq
    have z : |(F a).bearing i - (F b).bearing j| = 0 := by linarith
    exact ⟨i,j,sub_eq_zero.mp (abs_eq_zero.mp z),same⟩

/-- Any at least seventeen-point avoiding configuration yields nine
distinct rows of one switch type, with a shared projective constraint
and opposite bits at both ends of every chord between them. -/
theorem nine_rows (S : Finset Point) (card : 17 ≤ S.card) {lam : ℝ}
    (margin : 2*π/9 < lam) (hπ : lam ≤ π)
    (legal : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a≠b → a≠c → b≠c →
      EuclideanGeometry.angle a b c ≤ π-lam) :
    ∃ (s : ℕ) (G : Fin 9 → Row),
      (s=1 ∨ s=3) ∧ (∀ v, (G v).switches=s ∧ (G v).Legal lam) ∧
      (∀ v w, v≠w → ∃ i : Fin ((G v).n+1), ∃ j : Fin ((G w).n+1),
        (G v).bearing i=(G w).bearing j ∧ (G v).sign i ≠ (G w).sign j) := by
  classical
  have hl : 0<lam := by linarith [pi_pos]
  obtain ⟨F,profile,budget,_,_⟩ := planar_switch_profile S (by omega) hl hπ legal
  have one_or_three (a : S) : (F a).switches=1 ∨ (F a).switches=3 := by
    obtain ⟨odd, bound⟩ := budget a
    have small : (F a).switches < 5 := by
      by_contra! many
      have hm : (5:ℝ) ≤ ((F a).switches:ℝ) := by exact_mod_cast many
      nlinarith [mul_nonneg (sub_nonneg.mpr hm) hl.le]
    omega
  let ones := Finset.univ.filter (fun p : S => (F p).switches=1)
  let threes := Finset.univ.filter (fun p : S => (F p).switches=3)
  have all : ones ∪ threes = Finset.univ := by
    ext p
    simpa [ones,threes] using one_or_three p
  have sum : S.card ≤ ones.card+threes.card := by
    have h := Finset.card_union_le ones threes
    rw [all, Finset.card_univ] at h
    simpa using h
  have pick : ∃ s : ℕ, (s=1 ∨ s=3) ∧ 9 ≤ (Finset.univ.filter (fun p : S => (F p).switches=s)).card := by
    by_cases h : 9 ≤ ones.card
    · exact ⟨1,Or.inl rfl,h⟩
    · exact ⟨3,Or.inr rfl,show 9≤threes.card by omega⟩
  obtain ⟨s,hs,hcnt⟩ := pick
  let pool := Finset.univ.filter (fun p : S => (F p).switches=s)
  let emb (i : Fin 9) : pool := (Fintype.equivFin pool).symm
    ⟨i.val,by have h : 9 ≤ Fintype.card pool := by rw [Fintype.card_coe]; exact hcnt
              omega⟩
  have inj : Function.Injective emb := by
    intro a b e
    have hh := congrArg (Fintype.equivFin pool) e
    simp [emb] at hh
    exact Fin.ext hh
  refine ⟨s,fun i => F (emb i).val,hs,fun i =>
    ⟨(Finset.mem_filter.mp (emb i).property).2,(profile _).2⟩,?_⟩
  intro v w ne
  exact shared_chord profile _ _ (fun eq => ne (inj (Subtype.ext eq)))

#print axioms shared_chord
#print axioms nine_rows
end R37.Seventeen
