import NecessaryAxes
import WeightedSpectrum
noncomputable section
namespace R54.Profile
open JSP404 R55.WeightedCollision Real

/-- Exact collision criterion for every positive multiplicity at each of at least
two distinct macrocenters. No common scale for the internal collisions is assumed. -/
theorem fixed_profile {I : Type*} [Fintype I] {w : I→ℕ} {c : I→Point} {θ : ℝ}
    (hw : ∀ i,0<w i) (other : ∀ i : I,∃ j,j≠i) (ci : Function.Injective c) :
    θ∈attainable w c ↔ Admissible w c θ := by
  constructor
  · intro h
    obtain ⟨zero,centers,A,unit⟩:=necessary hw other ci (show Realizable w c θ from h)
    exact ⟨zero,fun i j k ij _ jk=>centers i j k ij jk.symm,A.v,unit,A.internal,A.outside⟩
  · exact admissible_mem hw ci

/-- Replace each fiber by any positive number of labels up to its binary rounding,
keeping the fixed macrocenters and the same limiting angular score. -/
theorem replace_weights {I : Type*} [Fintype I] {w u : I→ℕ} {c : I→Point}
    (hw : ∀ i,0<w i) (hu : ∀ i,0<u i) (other : ∀ i : I,∃ j,j≠i) (ci : Function.Injective c)
    (fits : ∀ i,u i≤2^(dim w i)) : attainable w c⊆attainable u c :=
  fun _ h=>transfer hu fits ci ((fixed_profile hw other ci).mp h)

theorem same_spectrum {I : Type*} [Fintype I] {w u : I→ℕ} {c : I→Point}
    (hw : ∀ i,0<w i) (hu : ∀ i,0<u i) (other : ∀ i : I,∃ j,j≠i) (ci : Function.Injective c)
    (same : ∀ i,dim w i=dim u i) : attainable w c=attainable u c := by
  apply Set.Subset.antisymm
  · apply replace_weights hw hu other ci
    intro i;rw [same i];exact Nat.le_pow_clog (by decide : 1<2) _
  · apply replace_weights hu hw other ci
    intro i;rw [←same i];exact Nat.le_pow_clog (by decide : 1<2) _

theorem alpha_bound {I : Type*} [Fintype I] {w : I→ℕ} {c : I→Point} {θ : ℝ}
    (sz : 3≤∑ i,w i) (h : θ∈attainable w c) : alpha (∑ i,w i)≤θ := by
  apply le_of_forall_pos_le_add
  intro e ep
  obtain ⟨f,inj,_,small⟩:=h e ep
  exact (alpha_le_maxAngle sz (card inj)).trans small.le

/-- A minimizing collision profile forces a plateau of the ordinary unrestricted
infimum up to the sum of the rounded multiplicities. -/
theorem plateau {I : Type*} [Fintype I] {w : I→ℕ} {c : I→Point} {N m : ℕ}
    (hw : ∀ i,0<w i) (other : ∀ i : I,∃ j,j≠i) (ci : Function.Injective c)
    (_size : ∑ i,w i=N) (ge : 3≤N) (profile : alpha N∈attainable w c)
    (lo : N≤m) (hi : m≤∑ i,2^(dim w i)) : alpha m=alpha N := by
  have axes:=(fixed_profile hw other ci).mp profile
  have upper:=alpha_bound (ge.trans (lo.trans hi)) (binary_roundup ci axes)
  exact le_antisymm ((alpha_mono (ge.trans lo) hi).trans upper) (alpha_mono ge lo)

/-- Immediately before a strict increase, each fiber in every minimizing collision
profile is already an exact power of two. -/
theorem jump {I : Type*} [Fintype I] {w : I→ℕ} {c : I→Point} {N : ℕ}
    (hw : ∀ i,0<w i) (other : ∀ i : I,∃ j,j≠i) (ci : Function.Injective c)
    (size : ∑ i,w i=N) (ge : 3≤N) (profile : alpha N∈attainable w c)
    (strict : alpha N<alpha (N+1)) : ∀ i,w i=2^(dim w i) := by
  classical
  have le (i : I) : w i≤2^(dim w i) := Nat.le_pow_clog (by decide : 1<2) _
  intro i
  by_contra! ne
  have more : (∑ j,w j)<∑ j,2^(dim w j) := Finset.sum_lt_sum
    (fun j _=>le j) ⟨i,Finset.mem_univ _,lt_of_le_of_ne (le i) ne⟩
  have eq:=plateau hw other ci size ge profile (Nat.le_succ N) (by omega)
  linarith

end R54.Profile
#print axioms R54.Profile.fixed_profile
#print axioms R54.Profile.same_spectrum
#print axioms R54.Profile.plateau
#print axioms R54.Profile.jump
