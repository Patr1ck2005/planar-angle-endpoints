import FourCoverExclusion
import MinimizingSequence
noncomputable section
namespace R53.FourCover
open JSP404 Real R55.FourIslands

def Covered (S : Finset Point) (δ : ℝ) := ∃ p∈S, ∃ q∈S, p≠q ∧ DiskCover S δ (dist p q)
def scores (N : ℕ) : Set ℝ := {u | ∀ δ : ℝ, 0<δ → ∃ S : Finset Point,
  S.card=N ∧ maxAngle S<u+δ ∧ Covered S δ}

/-- Every choice of four trial locations misses a fifth point at the asserted scale. -/
theorem outside_four {S : Finset Point} {δ D : ℝ} (exc : ¬DiskCover S δ D) (c : Fin 4→Point) :
    ∃ y∈S, ∀ i, δ*D<dist y (c i) := by
  by_contra! h
  exact exc ⟨c,h⟩

theorem from_three {N : ℕ} {u : ℝ} (hu : u∈R52.ThreeCover.scores N) : u∈scores N := by
  intro δ dp
  obtain ⟨S,sz,cap,p,hp,q,hq,pq,c,cv⟩:=hu δ dp
  refine ⟨S,sz,cap,p,hp,q,hq,pq,![c 0,c 1,c 2,c 2],?_⟩
  intro x hx
  obtain ⟨i,bound⟩:=cv x hx
  fin_cases i
  · exact ⟨0,bound⟩
  · exact ⟨1,bound⟩
  · exact ⟨2,bound⟩

private theorem bound {N : ℕ} {u θ : ℝ} (hu : u∈scores N)
    (ex : ∀ e : ℝ,0<e → ∃ r : ℝ,0<r ∧ ∀ (S : Finset Point),S.card=N → maxAngle S≤θ-e →
      ∀ p∈S,∀ q∈S,p≠q → ∀ δ,0≤δ → δ≤r → ¬DiskCover S δ (dist p q)) : θ≤u := by
  by_contra! wrong
  let e:=(θ-u)/2
  have ep : 0<e := by dsimp [e];linarith
  obtain ⟨r,rp,excludes⟩:=ex e ep
  let δ:=min r e
  have dp : 0<δ := lt_min rp ep
  obtain ⟨S,sz,upper,p,hp,q,hq,pq,cover⟩:=hu δ dp
  have cap : maxAngle S≤θ-e := by have le:=min_le_right r e;dsimp [δ,e] at *;linarith
  exact excludes S sz cap p hp q hq pq δ dp.le (min_le_left _ _) cover

theorem low_band {N k : ℕ} (lo : 4*2^k<N) (hi : N≤5*2^k) :
    IsLeast (scores N) (π-2*π/(2*(k:ℝ)+5)) := by
  refine ⟨from_three (R52.ThreeCover.low_band lo hi).1,?_⟩
  intro u hu
  apply bound hu
  intro e ep
  refine ⟨_,radius_pos (lowSep_pos k ep) k ep,?_⟩
  intro S size ang p hp q hq pq δ dp sm
  exact low_excludes hp hq pq (size.symm ▸ lo) ep ang dp sm

theorem high_band {N k : ℕ} (lo : 5*2^k<N) (hi : N≤8*2^k) :
    IsLeast (scores N) (π-π/((k:ℝ)+3)) := by
  refine ⟨from_three (R52.ThreeCover.high_band lo hi).1,?_⟩
  intro u hu
  apply bound hu
  intro e ep
  refine ⟨_,radius_pos (highSep_pos k ep) k ep,?_⟩
  intro S size ang p hp q hq pq δ dp sm
  exact high_excludes hp hq pq (size.symm ▸ lo) ep ang dp sm

end R53.FourCover
#print axioms R53.FourCover.low_band
#print axioms R53.FourCover.high_band
