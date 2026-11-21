import TwoAnchorGeometry
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Fintype.Powerset

namespace TwistedCapacity
open scoped BigOperators

/-- Every open gap longer than a grid spacing has an interior grid
boundary at every phase. -/
theorem one_boundary {L U γ : ℝ} (hg : 0<γ) (h : γ<U-L) (τ : ℝ) :
    ∃ k : ℤ, L < τ + k*γ ∧ τ + k*γ < U := by
  let k := ⌊(L-τ)/γ⌋
  have h₁ := (le_div_iff₀ hg).1 (Int.floor_le ((L-τ)/γ))
  have h₂ := (div_lt_iff₀ hg).1 (Int.lt_floor_add_one ((L-τ)/γ))
  refine ⟨k+1,?_,?_⟩ <;> push_cast <;> dsimp [k] <;> nlinarith

/-- For one designated long gap there is a phase with two distinct
consecutive boundaries strictly inside. Other vertices can use the
same phase because their individual gaps need only one boundary. -/
theorem two_boundaries {L U γ : ℝ} (hg : 0<γ) (h : γ<U-L) :
    ∃ τ : ℝ, 0≤τ ∧ τ<γ ∧ ∃ k : ℤ, L<τ+k*γ ∧ τ+(k+1:ℤ)*γ<U := by
  let x := (L+U-γ)/2
  let k := ⌊x/γ⌋
  have h₁ := (le_div_iff₀ hg).1 (Int.floor_le (x/γ))
  have h₂ := (div_lt_iff₀ hg).1 (Int.lt_floor_add_one (x/γ))
  refine ⟨x-k*γ,by dsimp [k]; linarith,by dsimp [k]; nlinarith,k,?_,?_⟩
  · dsimp [x,k]
    linarith
  · push_cast
    dsimp [x,k]
    nlinarith

/-- Initial sign and switches before a cell determine its bit. The
choice of indexing puts the twisted seam at the final boundary. -/
def bitAt {m : ℕ} (initial : Bool) (switches : Finset (Fin m)) (cell : Fin m) : Bool :=
  if (switches.filter (· < cell)).card % 2 = 1 then !initial else initial

abbrev Choices {m s : ℕ} (pool : Fin s → Finset (Fin m)) :=
  (j : Fin s) → {k : Fin m // k ∈ pool j}

def switchSet {m s : ℕ} {pool : Fin s → Finset (Fin m)} (c : Choices pool) : Finset (Fin m) :=
  Finset.univ.image (fun j => (c j).val)

private theorem index_unique {m s : ℕ} (pool : Fin s → Finset (Fin m))
    (hd : ∀ i j, i ≠ j → Disjoint (pool i) (pool j))
    {i j : Fin s} {k : Fin m} (hi : k∈pool i) (hj : k∈pool j) : i=j := by
  by_contra h
  exact Finset.disjoint_left.mp (hd i j h) hi hj

theorem switchSet_card {m s : ℕ} {pool : Fin s → Finset (Fin m)}
    (hd : ∀ i j, i ≠ j → Disjoint (pool i) (pool j)) (c : Choices pool) :
    (switchSet c).card=s := by
  have hi : Function.Injective (fun j => (c j).val) := by
    intro i j e
    change (c i).val=(c j).val at e
    exact index_unique pool hd (c i).property (e.symm ▸ (c j).property)
  unfold switchSet
  rw [Finset.card_image_of_injective _ hi]
  simp

theorem switchSet_injective {m s : ℕ} {pool : Fin s → Finset (Fin m)}
    (hd : ∀ i j, i ≠ j → Disjoint (pool i) (pool j)) :
    Function.Injective (switchSet (pool:=pool)) := by
  intro c d he
  funext i
  apply Subtype.ext
  have h : (c i).val ∈ switchSet d := he ▸ Finset.mem_image_of_mem _ (Finset.mem_univ i)
  obtain ⟨j,_,hji⟩ := Finset.mem_image.mp h
  have idx := index_unique pool hd (c i).property (hji ▸ (d j).property)
  subst j
  exact hji.symm

/-- Favorable-phase stratum deficit. Each long gap permits a nonempty
pool of boundary choices. A single two-choice gap at one vertex supplies
a spare word. Opposite signs at the shared cell of each edge enforce
cross-vertex disjointness, rather than assuming a cardinal deficit. -/
theorem stratum_loss {V : Type*} [Fintype V] {m s : ℕ}
    (pool : V → Fin s → Finset (Fin m)) (initial : (v : V) → Choices (pool v) → Bool)
    (slot : V → V → Fin m) (sign : V → V → Bool)
    (hd : ∀ v i j, i ≠ j → Disjoint (pool v i) (pool v j))
    (hne : ∀ v j, (pool v j).Nonempty)
    (more : ∃ v j x y, x∈pool v j ∧ y∈pool v j ∧ x≠y)
    (opposite : ∀ v w, v≠w → slot v w=slot w v ∧ sign v w≠sign w v)
    (compatible : ∀ v (c : Choices (pool v)) w, v≠w →
      bitAt (initial v c) (switchSet c) (slot v w) = sign v w) :
    Fintype.card V + 1 ≤ 2*m.choose s := by
  classical
  obtain ⟨v₀,j,x,y,hx,hy,hxy⟩ := more
  let std (v : V) (i : Fin s) : {k // k∈pool v i} :=
    ⟨(hne v i).choose,(hne v i).choose_spec⟩
  let c₁ := Function.update (std v₀) j ⟨x,hx⟩
  let c₂ := Function.update (std v₀) j ⟨y,hy⟩
  have hc : c₁ ≠ c₂ := by
    intro e
    have he := congrArg (fun f : Choices (pool v₀) => (f j).val) e
    exact hxy (by simpa [c₁,c₂] using he)
  let code (v : V) (c : Choices (pool v)) : Bool × {a : Finset (Fin m) // a.card=s} :=
    ⟨initial v c,⟨switchSet c,switchSet_card (hd v) c⟩⟩
  have distinct {v w : V} {a : Choices (pool v)} {b : Choices (pool w)} (he : code v a=code w b) : v=w := by
    by_contra hn
    have eq₁ : initial v a=initial w b := congrArg Prod.fst he
    have eq₂ : switchSet a=switchSet b := congrArg (fun p => p.2.val) he
    have h := compatible v a w hn
    rw [eq₁,eq₂,(opposite v w hn).1,compatible w b v (Ne.symm hn)] at h
    exact (opposite v w hn).2 h.symm
  let normal (v : V) : Choices (pool v) := if e : v=v₀ then e ▸ c₁ else std v
  let enc : Option V → Bool × {a : Finset (Fin m) // a.card=s}
    | none => code v₀ c₂
    | some v => code v (normal v)
  have spare (v : V) : code v₀ c₂ ≠ code v (normal v) := by
    intro e
    obtain rfl := distinct e
    have hs := congrArg (fun p => p.2.val) e
    have hs' : switchSet c₂=switchSet c₁ := by simpa [code,normal] using hs
    exact hc ((switchSet_injective (hd _) hs').symm)
  have hi : Function.Injective enc := by
    intro p q eq
    cases p with
    | none => cases q with
              | none => rfl
              | some w => exact (spare w eq).elim
    | some v => cases q with
                | none => exact (spare v eq.symm).elim
                | some w => exact congrArg some (distinct eq)
  simpa [Fintype.card_finset_len] using Fintype.card_le_of_injective enc hi

private theorem count_odd (m : ℕ) :
    (∑ k ∈ Finset.range m, if k%2=1 then 1 else 0) = m/2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ,ih]
    split_ifs <;> omega

private theorem twice_odd_choose {m : ℕ} (hm : m ≠ 0) :
    (∑ k ∈ Finset.range (m+1), if k%2=1 then 2*m.choose k else 0) = 2^m := by
  have ht : ∑ k ∈ Finset.range (m+1), (m.choose k : ℤ) = (2:ℤ)^m := by
    exact_mod_cast Nat.sum_range_choose m
  have ha := Int.alternating_sum_range_choose_of_ne hm
  have e : (∑ k ∈ Finset.range (m+1), if k%2=1 then (2:ℤ)*m.choose k else 0) =
      ∑ k ∈ Finset.range (m+1), ((m.choose k:ℤ)-(-1:ℤ)^k*m.choose k) := by
    apply Finset.sum_congr rfl
    intro k _
    split_ifs with ho
    · rw [(Nat.odd_iff.mpr ho).neg_one_pow]
      ring
    · have he : Even k := Nat.even_iff.mpr (by omega)
      rw [he.neg_one_pow]
      ring
  rw [Finset.sum_sub_distrib,ht,ha,sub_zero] at e
  exact_mod_cast e

/-- Sum the one-vertex loss in every odd stratum below m. The full
m-switch layer contributes two missing words precisely when m is odd. -/
theorem all_strata_cap {m : ℕ} (hm : 0<m) (count : ℕ → ℕ)
    (empty : ∀ k<m, k%2≠1 → count k=0)
    (loss : ∀ k<m, k%2=1 → count k + 1 ≤ 2*m.choose k) :
    (∑ k ∈ Finset.range m, count k) + m/2 + (if m%2=1 then 2 else 0) ≤ 2^m := by
  have h : (∑ k ∈ Finset.range m, (count k + (if k%2=1 then 1 else 0))) ≤
      ∑ k ∈ Finset.range m, if k%2=1 then 2*m.choose k else 0 := by
    refine Finset.sum_le_sum (fun k hk => ?_)
    by_cases h : k%2=1
    · simpa [h] using loss k (Finset.mem_range.mp hk) h
    · simp [h,empty k (Finset.mem_range.mp hk) h]
  rw [Finset.sum_add_distrib,count_odd] at h
  have total := twice_odd_choose hm.ne'
  rw [Finset.sum_range_succ,Nat.choose_self,mul_one] at total
  omega

#print axioms one_boundary
#print axioms two_boundaries
#print axioms switchSet_injective
#print axioms stratum_loss
#print axioms all_strata_cap
end TwistedCapacity
