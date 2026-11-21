import InteriorChordReserve
import CollisionSpectrum

noncomputable section
namespace R89.Interior
open Real JSP404 R55.WeightedCollision R54.GapTest R56.Windows

/-- Three different δ-separated actual rays at a center give the angular lower
bound associated with that center's cluster size. -/
theorem three_angle {I : Type*} [Fintype I] [Nontrivial I] {c : I→Point}
    (ci : Function.Injective c) {w : I→ℕ} (wp : ∀j,0<w j) {θ : ℝ}
    (hit : θ∈attainable w c) (i : I)
    (rays : ∀δ : ℝ,0<δ → θ=π-δ → Macro c θ →
      ∃h : Fin 3 ↪ I,(∀j,h j≠i) ∧ ∀j k,j≠k→δ≤EuclideanGeometry.angle (c (h j)) (c i) (c (h k))) :
    π-π/((dim w i:ℝ)+3)≤θ := by
  have den : 0<(dim w i:ℝ)+3:=by positivity
  by_cases below : θ<π
  · let δ:=π-θ
    have dp : 0<δ:=sub_pos.mpr below
    have eq : θ=π-δ:=by dsimp [δ];ring
    obtain ⟨pos,mac,v,unit,ins,out⟩:=(R54.Profile.fixed_profile wp (fun j=>exists_ne j) ci).mp hit
    obtain ⟨h,off,apart⟩:=rays δ dp eq mac
    have A : R56.Decorated.Axes c (dim w) θ :=
      ⟨v,fun j a zero=>by simpa [zero] using unit j a,ins,out⟩
    have legal (j k : Fin 3) (ne : j≠k) :
        δ≤EuclideanGeometry.angle (c (h j)) (c i) (c (h k)) ∧
        EuclideanGeometry.angle (c (h j)) (c i) (c (h k))≤π-δ :=
      ⟨apart j k ne,(mac _ _ _ (off j) (h.injective.ne ne) (off k).symm).trans_eq eq⟩
    have cap:=chord_reserve ci dp (by dsimp [δ];linarith) (eq ▸ A) i h off legal
    simp only [Fintype.card_fin] at cap
    have real := (Nat.le_floor_iff (div_nonneg pi_pos.le dp.le)).mp cap
    push_cast at real
    have m:=(le_div_iff₀ dp).mp real
    have t : δ≤π/((dim w i:ℝ)+3):=(le_div_iff₀ den).mpr (by linarith only [m])
    dsimp [δ] at t; linarith
  · linarith [div_nonneg pi_pos.le den.le]

/-- The same reserve applies to the actual maximum row capacity, whether or not
the assigned fiber fills it. -/
theorem three_score {I : Type*} [Fintype I] {c : I→Point} (ci : Function.Injective c)
    {δ : ℝ} (dp : 0<δ) (room : δ≤π) (mac : Macro c (π-δ)) {p : I→ℕ}
    (R : ∀j,Row (p j)) (front : Represents R c) (i : I) (h : Fin 3 ↪ I)
    (off : ∀j,h j≠i) (apart : ∀j k,j≠k→δ≤EuclideanGeometry.angle (c (h j)) (c i) (c (h k))) :
    score R i δ+3≤⌊π/δ⌋₊ := by
  simpa only [Fintype.card_fin] using chord_reserve ci dp room (full_axes R dp front) i h off
    (fun j k ne=>⟨apart j k ne,mac _ _ _ (off j) (h.injective.ne ne) (off k).symm⟩)

end R89.Interior
#print axioms R89.Interior.three_angle
#print axioms R89.Interior.three_score
