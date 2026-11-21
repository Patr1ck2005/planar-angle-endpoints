import InteriorThree
import InteriorThreeChords

noncomputable section
namespace R89.Interior
open Real JSP404 R55.WeightedCollision R54.GapTest R56.Windows

/-- A prescribed positive cluster enclosed by the other actual sites forces
a sharp angular lower bound, independently of their number and weights. -/
theorem enclosed_angle {I : Type*} [Fintype I] [Nontrivial I] {c : I→Point}
    (ci : Function.Injective c) {w : I→ℕ} (wp : ∀j,0<w j) {θ : ℝ}
    (hit : θ∈attainable w c) (i : I) (inside : c i∈convexHull ℝ (c '' {j | j≠i})) :
    π-π/((Nat.clog 2 (w i):ℝ)+3)≤θ := by
  apply three_angle ci wp hit i
  intro δ dp eq mac
  obtain ⟨h,off,sep⟩:=R91.Interior.three_chords ci inside dp (eq ▸ mac)
  exact ⟨h,off,fun j k ne=>(by linarith : δ≤2*δ).trans (sep j k ne).1⟩

theorem enclosed_score {I : Type*} [Fintype I] {c : I→Point} (ci : Function.Injective c)
    {δ : ℝ} (dp : 0<δ) (room : δ≤π) (mac : Macro c (π-δ)) {p : I→ℕ}
    (R : ∀j,Row (p j)) (front : Represents R c) (i : I)
    (inside : c i∈convexHull ℝ (c '' {j | j≠i})) : score R i δ+3≤⌊π/δ⌋₊ := by
  obtain ⟨h,off,sep⟩:=R91.Interior.three_chords ci inside dp mac
  exact three_score ci dp room mac R front i h off
    (fun j k ne=>(by linarith : δ≤2*δ).trans (sep j k ne).1)

/-- In a strict strip counterexample every site above this dyadic level
is a vertex of the convex hull of the whole support. -/
theorem heavy_vertex {I : Type*} [Fintype I] {c : I→Point} (ci : Function.Injective c)
    {θ : ℝ} (nonneg : 0≤θ) (below : θ<π) (mac : Macro c θ) {p : I→ℕ}
    (R : ∀j,Row (p j)) (front : Represents R c) (i : I) {k : ℕ}
    (period : π<((k:ℝ)+3)*(π-θ)) (heavy : k≤score R i (π-θ)) :
    c i∉convexHull ℝ (c '' {j | j≠i}) := by
  intro inside
  have dp : 0<π-θ:=sub_pos.mpr below
  have cap:=enclosed_score ci dp (by linarith) (by simpa using mac : Macro c (π-(π-θ))) R front i inside
  have floor : ⌊π/(π-θ)⌋₊<k+3 := (Nat.floor_lt (div_nonneg pi_pos.le dp.le)).mpr
    (by push_cast;exact (div_lt_iff₀ dp).mpr period)
  omega
end R89.Interior
#print axioms R89.Interior.enclosed_angle
#print axioms R89.Interior.enclosed_score
#print axioms R89.Interior.heavy_vertex
