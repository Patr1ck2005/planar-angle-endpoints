import GlobalBoundary
noncomputable section
namespace R54.Profile
open JSP404 R55.WeightedCollision Real

def OrdinaryMinimum (N : ℕ) := ∃ S : Finset Point,S.card=N ∧ maxAngle S=alpha N

/-- If no ordinary configuration attains the infimum then a proper collision
profile with fewer centers does so. At least one fiber has a genuine binary axis. -/
theorem ordinary_or_collision {N : ℕ} (ge : 3≤N) :
    OrdinaryMinimum N ∨ ∃ m : ℕ,2≤m ∧ m<N ∧ ∃ c : Fin m→Point,Function.Injective c ∧ Normalized c ∧
      ∃ w : Fin m→ℕ,(∀ i,0<w i) ∧ (∑ i,w i)=N ∧ (∃ i,2≤w i) ∧
        minimum w c=alpha N ∧ Admissible w c (alpha N) := by
  classical
  obtain ⟨m,mg,le,c,ci,norm,w,hw,sz,eq,axes⟩:=realized_minimum ge
  rcases lt_or_eq_of_le le with proper|full
  · right
    have multi : ∃ i,2≤w i := by
      by_contra! small
      have one (i : Fin m) : w i=1 := by have :=hw i;have :=small i;omega
      simp [one] at sz
      omega
    exact ⟨m,mg,proper,c,ci,norm,w,hw,sz,multi,eq,axes⟩
  · left
    let S:=Finset.univ.image c
    have size : S.card=N := by simp [S,Finset.card_image_of_injective _ ci,full]
    have cap : maxAngle S≤alpha N := by
      apply maxAngle_le axes.1
      intro a ha b hb z hz ab az bz
      obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp ha
      obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hb
      obtain ⟨k,_,rfl⟩:=Finset.mem_image.mp hz
      exact axes.2.1 i j k (fun e=>ab (congrArg c e)) (fun e=>az (congrArg c e)) (fun e=>bz (congrArg c e))
    exact ⟨S,size,le_antisymm cap (alpha_le_maxAngle ge size)⟩

/-- Cardinality gains from all collision fibers add. For any already proved increase at
M, the total binary rounding of every minimizer at N must stay strictly below M. -/
theorem rounding_ceiling {I : Type*} [Fintype I] {w : I→ℕ} {c : I→Point} {N M : ℕ}
    (hw : ∀ i,0<w i) (other : ∀ i : I,∃ j,j≠i) (ci : Function.Injective c)
    (sz : ∑ i,w i=N) (ge : 3≤N) (profile : alpha N∈attainable w c)
    (lo : N≤M) (incr : alpha N<alpha M) : (∑ i,2^(dim w i))<M := by
  by_contra! room
  exact (ne_of_gt incr) (plateau hw other ci sz ge profile lo room)

end R54.Profile
#print axioms R54.Profile.ordinary_or_collision
#print axioms R54.Profile.rounding_ceiling
