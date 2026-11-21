import TwoAnchorGeometry

/-! Finite planar direction-bin encoding. Every occupied bin at a vertex
has just one incidence type. Bin indices use the floor, so a closed
upper endpoint is allowed even when it lies on an internal boundary. -/

namespace TwoAnchorCount
open Real TwoAnchorGeometry

private theorem bin_lt {u L H lam : ℝ} {m : ℕ}
    (hl : 0 < lam) (hlower : L ≤ u) (hu : u ≤ H) (hspan : H - L < (m : ℝ) * lam) :
    ⌊(u-L)/lam⌋₊ < m := by
  exact (Nat.floor_lt (div_nonneg (sub_nonneg.mpr hlower) hl.le)).2
    ((div_lt_iff₀ hl).2 (by linarith))

private theorem bin_separation {u v L lam : ℝ} (hl : 0 < lam)
    (hu : L ≤ u) (hv : L ≤ v)
    (he : ⌊(u-L)/lam⌋₊ = ⌊(v-L)/lam⌋₊) : |u-v| < lam := by
  have h₁ := Nat.floor_le (div_nonneg (sub_nonneg.mpr hu) hl.le)
  have h₂ := Nat.floor_le (div_nonneg (sub_nonneg.mpr hv) hl.le)
  have h₃ := Nat.lt_floor_add_one ((u-L)/lam)
  have h₄ := Nat.lt_floor_add_one ((v-L)/lam)
  rw [he] at h₁ h₃
  have huv : (u-L)/lam < (v-L)/lam + 1 := by linarith
  have hvu : (v-L)/lam < (u-L)/lam + 1 := by linarith
  rw [← div_self hl.ne', ← add_div] at huv hvu
  exact abs_lt.mpr ⟨by linarith [(div_lt_div_iff_of_pos_right hl).mp hvu],
    by linarith [(div_lt_div_iff_of_pos_right hl).mp huv]⟩

/-- A complete orientation of a finite point family whose forward chords
have bearings in one interval of width strictly below mλ admits a
binary code of length m, provided each incoming/outgoing turn obeys
the ordinary Euclidean angle cap. No absence-of-forbidden-path or
pre-existing separation code is assumed. -/
theorem interval_count {I : Type*} [Fintype I]
    (P : I → Plane) (R : I → I → Prop) (u : I → I → ℝ)
    {L H lam : ℝ} {m : ℕ} (hl : 0 < lam)
    (hcomplete : ∀ i j, i ≠ j → R i j ∨ R j i)
    (hspan : H-L < (m:ℝ)*lam)
    (hrange : ∀ i j, R i j → L ≤ u i j ∧ u i j ≤ H)
    (hupper : ∀ i j, R i j → 0 ≤ u i j ∧ u i j ≤ π)
    (hchord : ∀ i j, R i j → ∃ r : ℝ, 0 < r ∧ P j-P i = r • ray (u i j))
    (hlegal : ∀ i j k, R i j → R j k →
      InnerProductGeometry.angle (P i-P j) (P k-P j) ≤ π-lam) :
    Fintype.card I ≤ 2^m := by
  classical
  let bin (i j : I) := ⌊(u i j-L)/lam⌋₊
  let code (j : I) (b : Fin m) : Bool := decide (∃ i, R i j ∧ bin i j = b.val)
  have noMix {i j k : I} (hij : R i j) (hjk : R j k) (he : bin i j = bin j k) : False := by
    have hd := bin_separation hl (hrange i j hij).1 (hrange j k hjk).1 he
    obtain ⟨r,hr,he₁⟩ := hchord i j hij
    obtain ⟨s,hs,he₂⟩ := hchord j k hjk
    have h := hlegal i j k hij hjk
    rw [show P i-P j = -(P j-P i) by abel,he₁,he₂,
      InnerProductGeometry.angle_neg_left, InnerProductGeometry.angle_smul_left_of_pos _ _ hr,
      InnerProductGeometry.angle_smul_right_of_pos _ _ hs,
      angle_rays (hupper i j hij) (hupper j k hjk)] at h
    linarith
  have distinguishes {i j : I} (hij : R i j) : code i ≠ code j := by
    let b : Fin m := ⟨bin i j,bin_lt hl (hrange i j hij).1 (hrange i j hij).2 hspan⟩
    intro he
    have hj : code j b = true := by
      change decide (∃ a, R a j ∧ bin a j = b.val) = true
      exact decide_eq_true ⟨i,hij,rfl⟩
    rw [← he] at hj
    obtain ⟨a,hai,hb⟩ := of_decide_eq_true hj
    exact noMix hai hij hb
  have hi : Function.Injective code := by
    intro i j he
    by_contra hn
    rcases hcomplete i j hn with h | h
    · exact distinguishes h he
    · exact distinguishes h he.symm
  simpa using Fintype.card_le_of_injective code hi

#print axioms interval_count
end TwoAnchorCount
