import GapPacking
import WeightedSpectrum

noncomputable section
namespace R89.Interior
open JSP404 Real InnerProductGeometry R54.GapTest R56.Windows R55.WeightedCollision

/-- Pairwise separated projective lines occupy at least one defect-width each,
including the wrap across the chosen first line. -/
theorem projective_count {J : Type*} [Fintype J] {δ : ℝ} (dp : 0<δ) (room : δ≤π)
    (v : J→Point) (nz : ∀i,v i≠0)
    (cap : ∀i j,i≠j→∀r:ℝ,(r= -1 ∨ r=1)→ angle (r • v i) (v j)≤π-δ) :
    Fintype.card J≤⌊π/δ⌋₊ := by
  classical
  generalize size : Fintype.card J = n
  cases n with
  | zero => omega
  | succ n =>
    let e := (Fintype.equivFinOfCardEq size).symm
    let x:=v (e 0)
    obtain ⟨t,_,_,line⟩:=polar x (nz _)
    choose a lo hi wall using fun j : Fin n=>lifted_polar (v (e j.succ)) (nz _) t
    let Q : Row 1 := {
      w:=fun j=>if j=0 then t else t+π
      ordered:=by intro j k jk h;interval_cases k <;> interval_cases j <;> simp_all [pi_pos.le]
      period:=by simp }
    have span {a b : ℝ} (al : t≤a) (ah : a≤t+π) (bl : t≤b) (bh : b≤t+π) :
        |a-b|≤π := abs_le.mpr ⟨by linarith,by linarith⟩
    have bound:=packing Q dp a (fun j=>by simpa [Q] using And.intro (lo j) (hi j))
      (fun j k ne=>apart (wall j) (wall k) (span (lo j) (hi j) (lo k) (hi k))
        (cap _ _ (e.injective.ne (Fin.succ_injective n |>.ne ne)))) (by
          intro j k hk
          have sides:=cap (e j.succ) (e 0) (e.injective.ne j.succ_ne_zero)
          interval_cases k
          · change δ≤|a j-t|
            exact apart (wall j) line (span (lo j) (hi j) le_rfl (by linarith [pi_pos])) sides
          · change δ≤|a j-(t+π)|
            exact apart (wall j) (bearing_closes line) (span (lo j) (hi j) (by linarith [pi_pos]) le_rfl) sides)
    have floorp : 1≤⌊π/δ⌋₊ := Nat.le_floor (by simpa only [Nat.cast_one,le_div_iff₀ dp,one_mul] using room)
    have b : n≤⌊π/δ⌋₊-1 := by simpa [R51.Anchored.gapScore,Q] using bound
    omega

/-- Every set of actual rays at a site whose mutual angles lie between δ and
π−δ occupies that many distinct directions in addition to all microscopic axes. -/
theorem chord_reserve {I J : Type*} [Fintype I] [Fintype J] {c : I→Point}
    (ci : Function.Injective c) {δ : ℝ} (dp : 0<δ) (room : δ≤π) {D : I→ℕ}
    (A : R56.Decorated.Axes c D (π-δ)) (i : I) (h : J→I) (off : ∀j,h j≠i)
    (legal : ∀j k,j≠k→δ≤EuclideanGeometry.angle (c (h j)) (c i) (c (h k)) ∧
       EuclideanGeometry.angle (c (h j)) (c i) (c (h k))≤π-δ) :
    D i+Fintype.card J≤⌊π/δ⌋₊ := by
  let v : Fin (D i) ⊕ J → Point := Sum.elim (A.v i) (fun j=>c (h j)-c i)
  have nz : ∀j,v j≠0 := by
    intro j
    cases j with
    | inl a => exact A.nonzero i a
    | inr a => exact sub_ne_zero.mpr (ci.ne (off a))
  have cap : ∀p q,p≠q→∀r:ℝ,(r= -1 ∨ r=1)→angle (r • v p) (v q)≤π-δ := by
    intro p q ne r sign
    cases p with
    | inl a =>
      cases q with
      | inl b => simpa [v] using A.internal i a b (fun e=>ne (congrArg Sum.inl e)) r 1 sign (Or.inr rfl)
      | inr b => exact A.outside i (h b) (off b).symm a r sign
    | inr a =>
      cases q with
      | inl b =>
        have plus:=A.outside i (h a) (off a).symm b r sign
        rcases sign with rfl|rfl
        · change angle ((-1:ℝ) • (c (h a)-c i)) (A.v i b)≤π-δ
          simp only [neg_one_smul,angle_neg_left] at plus ⊢
          rwa [angle_comm]
        · change angle ((1:ℝ) • (c (h a)-c i)) (A.v i b)≤π-δ
          simp only [one_smul] at plus ⊢
          rwa [angle_comm]
      | inr b =>
        obtain ⟨lo,hi⟩:=legal a b (fun e=>ne (congrArg Sum.inr e))
        change δ≤angle (c (h a)-c i) (c (h b)-c i) at lo
        rcases sign with rfl|rfl
        · simp only [neg_one_smul,angle_neg_left];change π-angle (c (h a)-c i) (c (h b)-c i)≤π-δ;linarith
        · simp only [one_smul];exact hi
  simpa using projective_count dp room v nz cap
end R89.Interior
#print axioms R89.Interior.projective_count
#print axioms R89.Interior.chord_reserve
