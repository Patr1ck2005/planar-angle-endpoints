import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Prod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

noncomputable section
namespace R56.Clearance

variable {K : Type*} [Fintype K]

/-- Every label is counted separately, including labels carrying the same value. -/
def atLeast (v : K→ℝ) (x : ℝ) : ℕ := ((Finset.univ : Finset K).filter (fun k=>x≤v k)).card

def values (v : K→ℝ) : Multiset ℝ := (Finset.univ : Finset K).val.map v

theorem atLeast_multiset (v : K→ℝ) (x : ℝ) :
    atLeast v x=(values v).countP (fun y=>x≤y) := by
  classical
  rw [values,Multiset.countP_map]
  rfl

private def candidates (v : K→ℝ) (d : ℕ) : Finset ℝ :=
  insert 0 ((Finset.univ.image v).filter (fun y=>d≤atLeast v y))

/-- The d-th largest value of a nonnegative indexed family, with zero padding
when d exceeds its size. The rank starts at one. -/
def kth (v : K→ℝ) (d : ℕ) : ℝ := (candidates v d).max' ⟨0,Finset.mem_insert_self _ _⟩

theorem kth_nonneg (v : K→ℝ) (d : ℕ) : 0≤kth v d :=
  Finset.le_max' _ _ (Finset.mem_insert_self _ _)

theorem atLeast_anti (v : K→ℝ) {x y : ℝ} (h : x≤y) : atLeast v y≤atLeast v x := by
  apply Finset.card_le_card
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,h.trans (Finset.mem_filter.mp hi).2⟩

private theorem select_lower (v : K→ℝ) (S : Finset K) (d : ℕ) (hd : 0<d) (enough : d≤S.card) :
    ∃ y∈S, v y≤kth v d := by
  classical
  obtain ⟨y,hy,low⟩ := Finset.exists_min_image S v (Finset.card_pos.mp (hd.trans_le enough))
  have nr : d≤atLeast v (v y) := by
    refine enough.trans (Finset.card_le_card ?_)
    intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,low _ ha⟩
  have member : v y∈candidates v d :=
    Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _),nr⟩)
  exact ⟨y,hy,Finset.le_max' _ _ member⟩

/-- The exact threshold equivalence includes a tie at the d-th largest slot. -/
theorem le_kth_iff (v : K→ℝ) {d : ℕ} (hd : 0<d) {x : ℝ} (hx : 0<x) :
    x≤kth v d ↔ d≤atLeast v x := by
  classical
  constructor
  · intro h
    have mem : kth v d∈candidates v d := Finset.max'_mem _ _
    rcases Finset.mem_insert.mp mem with z | q
    · linarith
    · exact (Finset.mem_filter.mp q).2.trans (atLeast_anti v h)
  · intro count
    let S := (Finset.univ : Finset K).filter (fun i=>x≤v i)
    obtain ⟨y,hy,lo⟩ := select_lower v S d hd count
    exact (Finset.mem_filter.mp hy).2.trans lo

/-- Strictly larger values occupy fewer than d slots, even at a tied rank. -/
theorem strictly_above (v : K→ℝ) {d : ℕ} (hd : 0<d) :
    ((Finset.univ : Finset K).filter (fun i=>kth v d<v i)).card<d := by
  classical
  by_contra! higher
  obtain ⟨y,hy,lo⟩ := select_lower v _ d hd higher
  exact (not_lt_of_ge lo) (Finset.mem_filter.mp hy).2

/-- If enough nonnegative slots exist, at least d of them reach their d-th rank. -/
theorem weakly_above (v : K→ℝ) (vn : ∀k,0≤v k) {d : ℕ} (hd : 0<d) (size : d≤Fintype.card K) :
    d≤atLeast v (kth v d) := by
  by_cases h : 0<kth v d
  · exact (le_kth_iff v hd h).mp le_rfl
  · have zero : kth v d=0 := by linarith [kth_nonneg v d]
    simpa [atLeast,zero,vn] using size

#print axioms le_kth_iff
#print axioms strictly_above
#print axioms weakly_above
end R56.Clearance
