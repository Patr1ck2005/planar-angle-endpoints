import MultipleAnchors

noncomputable section
namespace R51.Anchored
open JSP404 Real

/-- Each gap of length d receives max(floor(d/δ)-1,0) binary digits. -/
def gapScore (m : ℕ) (w : ℕ→ℝ) (δ : ℝ) : ℕ :=
  ∑ i : Fin m, (⌊(w (i.val+1)-w i)/δ⌋₊-1)

private theorem floor_fit (d : ℝ) {δ : ℝ} (dp : 0<δ) :
    d<(((⌊d/δ⌋₊-1 : ℕ):ℝ)+2)*δ := by
  let b:=⌊d/δ⌋₊
  have h:= (div_lt_iff₀ dp).mp (Nat.lt_floor_add_one (d/δ))
  have le : b+1≤(b-1)+2 := by omega
  have cast : (b:ℝ)+1≤((b-1:ℕ):ℝ)+2 := by exact_mod_cast le
  exact h.trans_le (mul_le_mul_of_nonneg_right cast dp.le)

/-- Actual finite clouds obey the usual zero-diameter gap score at the slightly smaller
defect δ = π-M(S)-η, even when each wall comes from a different external observer. -/
theorem finite_gap_score {S F : Finset Point} (sub : F⊆S) (two : 2≤F.card)
    {m : ℕ} (mp : 0<m) (t : ℝ) (ht : 0≤t ∧ t<π) (w : ℕ→ℝ)
    (first : w 0=t) (last : w m=t+π) {η : ℝ} (ep : 0≤η) (lp : 0<π-maxAngle S-η)
    (wall : ∀ j≤m, Wall S F t (w j) η) :
    F.card≤2^gapScore m w (π-maxAngle S-η) := by
  let δ:=π-maxAngle S-η
  let B (j : Fin m) := ⌊(w (j.val+1)-w j)/δ⌋₊-1
  have fit (i : Fin m) : w (i.val+1)-w i+η+η<((B i:ℝ)+2)*(π-maxAngle S) := by
    have h:=floor_fit (w (i.val+1)-w i) lp
    change w (i.val+1)-w i<((B i:ℝ)+2)*(π-maxAngle S-η) at h
    have z : 0≤(B i:ℝ) := Nat.cast_nonneg _
    nlinarith [mul_nonneg z ep]
  exact (Nat.clog_le_iff_le_pow (by decide : 1<2)).mp
    (multiple_anchor_capacity sub two mp t ht w (fun _=>η) B first last wall (by linarith) fit)

/-- Sum the cardinal bounds of the actual clouds. Overlap is harmless. Clouds of size 0 or 1
are allowed without external directions. -/
theorem cover_cardinality {I : Type*} [Fintype I] {S : Finset Point} (F : I→Finset Point)
    (sub : ∀ i,F i⊆S) (cover : S⊆Finset.univ.biUnion F) (m : I→ℕ)
    (t η : I→ℝ) (w : I→ℕ→ℝ)
    (data : ∀ i, 2≤(F i).card →
      0<m i ∧ (0≤t i ∧ t i<π) ∧ w i 0=t i ∧ w i (m i)=t i+π ∧
      0≤η i ∧ 0<π-maxAngle S-η i ∧ (∀ j≤m i,Wall S (F i) (t i) (w i j) (η i))) :
    S.card≤∑ i, 2^gapScore (m i) (w i) (π-maxAngle S-η i) := by
  have each (i : I) : (F i).card≤2^gapScore (m i) (w i) (π-maxAngle S-η i) := by
    by_cases two : 2≤(F i).card
    · obtain ⟨mp,ht,first,last,ep,lp,wall⟩:=data i two
      exact finite_gap_score (sub i) two mp (t i) ht (w i) first last ep lp wall
    · exact le_trans (by omega : (F i).card≤1) (Nat.one_le_pow _ _ (by decide))
  exact (Finset.card_le_card cover).trans (Finset.card_biUnion_le.trans (Finset.sum_le_sum (fun i _=>each i)))

end R51.Anchored
#print axioms R51.Anchored.finite_gap_score
#print axioms R51.Anchored.cover_cardinality
