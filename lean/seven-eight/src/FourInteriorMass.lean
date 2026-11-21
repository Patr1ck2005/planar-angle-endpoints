import EndpointWeights

noncomputable section
namespace R96.Endpoint
open JSP404 Real R55.WeightedCollision Finset

/-- For four sites the exact maximum mass with an enclosed site is bounded by
seven. At seven the enclosed site is unique and every remaining site has weight two. -/
theorem four_mass {I : Type*} [Fintype I] {c : I→Point} (ci : Function.Injective c)
    {w : I→ℕ} (wp : ∀j,0<w j) (four : Fintype.card I=4) (hit : 2*π/3∈attainable w c)
    (i : I) (inside : c i∈convexHull ℝ (c '' {a | a≠i})) :
    (∑j,w j)≤7 ∧ w i=1 ∧ ((∑j,w j)=7 → (∀j,j≠i→w j=2) ∧
      ∀j,c j∈convexHull ℝ (c '' {a | a≠j}) ↔ j=i) := by
  classical
  let : Nontrivial I:=Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have A:=(R54.Profile.fixed_profile wp (fun j=>exists_ne j) ci).mp hit
  have cap (j : I): w j≤2:=(weight_le_two ci (by omega) A j).2
  have wi:=enclosed_unit ci wp hit i inside
  let E:=(univ : Finset I).erase i
  have cardE:E.card=3:=by simp [E,four]
  have total : (∑j∈E,w j)+w i=∑j,w j:=sum_erase_add _ _ (mem_univ _)
  have six : (∑j∈E,(2:ℕ))=6:=by simp [cardE]
  have few := sum_le_sum (s:=E) (fun j _=>cap j)
  rw [six] at few
  refine ⟨by omega,wi,?_⟩
  intro seven
  have all (j : I) (ne : j≠i) : w j=2:=by
    by_contra bad
    have strict := sum_lt_sum (s:=E) (fun j _=>cap j)
      ⟨j,mem_erase.mpr ⟨ne,mem_univ _⟩,lt_of_le_of_ne (cap j) bad⟩
    rw [six] at strict
    omega
  refine ⟨all,?_⟩
  intro j
  refine ⟨fun h=>?_,fun eq=>eq ▸ inside⟩
  by_contra ne
  have one:=enclosed_unit ci wp hit j h
  have two:=all j ne
  omega

end R96.Endpoint
#print axioms R96.Endpoint.four_mass
