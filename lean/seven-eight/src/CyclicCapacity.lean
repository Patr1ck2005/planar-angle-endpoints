import Std

/-! Sharp bounds for five or more cyclic residual arcs. The scalar type
is an arbitrary linearly ordered commutative ring with Lean's standard
arithmetic interfaces. No mesh or rational approximation is involved. -/
namespace SendovCycle

open Lean.Grind Std
attribute [local instance] Semiring.natCast Ring.intCast
set_option linter.unusedSectionVars false
variable {R : Type} [CommRing R] [LE R] [LT R] [IsLinearOrder R]
  [LawfulOrderLT R] [OrderedRing R]


/-- Sum over k consecutive positions of a sequence starting at i. -/
def seg {A : Type} [Zero A] [Add A] (f : Nat → A) (i : Nat) : Nat → A
  | 0 => 0
  | k+1 => f i + seg f (i+1) k

private theorem seg_end (f : Nat → R) (i k : Nat) :
    seg f i (k+1) = seg f i k + f (i+k) := by
  induction k generalizing i with
  | zero => simp [seg] <;> grind
  | succ k ih =>
    have h := ih (i+1)
    have hi : i+1+k = i+(k+1) := by omega
    rw [hi] at h
    change f i + seg f (i+1) (k+1) = (f i + seg f (i+1) k) + _
    rw [h]
    grind

private theorem seg_shift (f : Nat → R) (t : Nat) (hp : ∀ i, f (i+t) = f i)
    (i : Nat) : seg f i t = seg f 0 t := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have h := seg_end f i t
    rw [hp] at h
    change f i + seg f (i+1) t = _ at h
    grind

private theorem seg_nonneg (f : Nat → R) (h : ∀ i, 0 ≤ f i) (i k : Nat) :
    0 ≤ seg f i k := by
  induction k generalizing i with
  | zero => simp [seg] <;> grind
  | succ k ih =>
    have := ih (i+1)
    have := h i
    simp only [seg]
    grind

/-- z is the sum of the two adjacent residual arcs at a vertex. -/
def edge (y : Nat → R) (i : Nat) := y i + y (i+1)

private theorem double_count (y : Nat → R) (t : Nat) (hp : ∀ i, y (i+t) = y i) :
    seg (edge y) 0 t = 2 * seg y 0 t := by
  have aux (i k : Nat) : seg (edge y) i k = seg y i k + seg y (i+1) k := by
    induction k generalizing i with
    | zero => simp [seg] <;> grind
    | succ k ih =>
      have := ih (i+1)
      simp only [seg, edge] at *
      grind
  have := aux 0 t
  have := seg_shift y t hp 1
  grind

/-- An edge and the next disjoint edge fit inside one period. -/
private theorem disjoint_pair (y : Nat → R) (t : Nat) (ht : 4 ≤ t)
    (hp : ∀ i, y (i+t) = y i) (hn : ∀ i, 0 ≤ y i) (hl : ∀ i, 1 ≤ edge y i)
    (i : Nat) : edge y i + 1 ≤ seg y 0 t := by
  obtain ⟨k, rfl⟩ : ∃ k, t = k+4 := ⟨t-4, by omega⟩
  have hs := seg_shift y (k+4) hp i
  have ht := seg_nonneg y hn (i+4) k
  have hl' := hl (i+2)
  simp only [seg, edge] at hs hl' ⊢
  grind

/-- One unit residual and its next two disjoint edges cost three units. -/
private theorem unit_and_pairs (y : Nat → R) (t : Nat) (ht : 5 ≤ t)
    (hp : ∀ i, y (i+t) = y i) (hn : ∀ i, 0 ≤ y i) (hl : ∀ i, 1 ≤ edge y i)
    (i : Nat) (hy : 1 ≤ y i) : 3 ≤ seg y 0 t := by
  obtain ⟨k, rfl⟩ : ∃ k, t = k+5 := ⟨t-5, by omega⟩
  have hs := seg_shift y (k+5) hp i
  have hh := seg_nonneg y hn (i+5) k
  have h₁ := hl (i+1)
  have h₂ := hl (i+3)
  simp only [seg, edge] at hs h₁ h₂ ⊢
  grind

/-- The normalized multiplicative weight for a residual edge in [1,4). -/
noncomputable def weight (z : R) : Nat := by
  classical exact if z < 2 then 1 else if z < 3 then 2 else 4

private theorem dense_weight (z : R) (hz : 1 ≤ z) :
    3 * ((weight z : Nat) : R) ≤ 4*z := by
  unfold weight
  split <;> first | (split <;> grind) | grind

private theorem small_weight (z : R) (hz : 1 ≤ z) (hu : z < 3) :
    ((weight z : Nat) : R) ≤ z := by
  unfold weight
  split <;> first | (split <;> grind) | grind

private theorem sum_weights (f : Nat → Nat) (g : Nat → R) (A B : R)
    (h : ∀ i, A * (f i : R) ≤ B * g i) (i k : Nat) :
    A * ((seg f i k : Nat) : R) ≤ B * seg g i k := by
  induction k generalizing i with
  | zero => simp [seg] <;> grind
  | succ k ih =>
    have hi := ih (i+1)
    have hh := h i
    simp only [seg, Semiring.natCast_add]
    grind

private theorem dyadic_majorant (D : Nat) (hD : 4 ≤ D) :
    8*D+4 ≤ 18*2^(D-3) ∧ 8*D+8 ≤ 21*2^(D-3) := by
  obtain ⟨k, rfl⟩ : ∃ k, D = k+4 := ⟨D-4, by omega⟩
  induction k with
  | zero => decide
  | succ k ih =>
    have he : k+1+4-3 = (k+4-3)+1 := by omega
    rw [he, Nat.pow_succ]
    omega

/-- Five or more cyclically ordered residual arcs, every adjacent sum ≥1.
The last premise says that either D is already at least 3 or some residual
arc contains a full unit. For the normalized geometry this follows from
n≥3: base=0 gives D=n; a positive subtracted floor leaves residual ≥1.
low=true means the half-open low strip 2S<2D+1. -/
theorem sharp_residual_capacity (y : Nat → R) (t D : Nat) (low : Bool)
    (ht : 5 ≤ t) (hp : ∀ i, y (i+t) = y i) (hn : ∀ i, 0 ≤ y i)
    (hl : ∀ i, 1 ≤ edge y i)
    (hS : seg y 0 t < (D:R)+1)
    (hL : low = true → 2 * seg y 0 t < 2 * (D:R)+1)
    (hbase : 3 ≤ D ∨ ∃ i, 1 ≤ y i) :
    seg (fun i => weight (edge y i)) 0 t ≤ (if low then 6 else 7) * 2^(D-3) := by
  have hD : 3 ≤ D := by
    rcases hbase with h | ⟨i, hi⟩
    · exact h
    · have := unit_and_pairs y t ht hp hn hl i hi
      apply Classical.byContradiction
      intro hc
      have hh := OrderedRing.natCast_le_natCast_of_le (R:=R) D 2 (by omega)
      grind
  let W := seg (fun i => weight (edge y i)) 0 t
  change W ≤ _
  have hdc := double_count y t hp
  by_cases hd : D=3
  · subst D
    have hsmall (i : Nat) : ((weight (edge y i) : Nat) : R) ≤ edge y i := by
      have := disjoint_pair y t (by omega) hp hn hl i
      apply small_weight _ (hl i)
      grind
    have hsum := sum_weights (fun i => weight (edge y i)) (edge y) (1:R) 1
      (fun i => by have := hsmall i; grind) 0 t
    change 1*(W:R) ≤ _ at hsum
    cases low with
    | false =>
      have hlt : (W:R) < ((8:Nat):R) := by grind
      have := OrderedRing.lt_of_natCast_lt_natCast W 8 hlt
      simp
      omega
    | true =>
      have hh := hL rfl
      have hlt : (W:R) < ((7:Nat):R) := by grind
      have := OrderedRing.lt_of_natCast_lt_natCast W 7 hlt
      simp
      omega
  · have hsum := sum_weights (fun i => weight (edge y i)) (edge y) (3:R) 4
      (fun i => dense_weight _ (hl i)) 0 t
    change 3*(W:R) ≤ _ at hsum
    have hm := dyadic_majorant D (by omega)
    cases low with
    | false =>
      have hx : (((3*W:Nat):R)) < (((8*D+8:Nat):R)) := by
        simp only [Semiring.natCast_add, Semiring.natCast_mul]
        grind
      have := OrderedRing.lt_of_natCast_lt_natCast _ _ hx
      simp
      omega
    | true =>
      have hh := hL rfl
      have hx : (((3*W:Nat):R)) < (((8*D+4:Nat):R)) := by
        simp only [Semiring.natCast_add, Semiring.natCast_mul]
        grind
      have := OrderedRing.lt_of_natCast_lt_natCast _ _ hx
      simp
      omega

#print axioms sharp_residual_capacity


/-- One may specify floors by their defining inequalities. This avoids a
specialized floor operation on the scalar type. For real arcs choose
qᵢ=⌊aᵢ⌋ and gᵢ=⌊aᵢ+aᵢ₊₁⌋. -/
def floorSlot (a : R) (q : Nat) : Prop := (q:R) ≤ a ∧ a < (q:R)+1

def charge (q : Nat) : Nat := q-1

def residual (a : R) (q : Nat) : R := a - ((charge q : Nat) : R)

private theorem slot_bounds (a : R) (q : Nat) (h : floorSlot a q) :
    0 ≤ residual a q ∧ residual a q < 2 ∧
      (0 < charge q → 1 ≤ residual a q) := by
  obtain ⟨hl,hu⟩ := h
  cases q with
  | zero => simp [residual, charge] <;> grind
  | succ k =>
    simp only [residual, charge, Nat.succ_sub_one, Semiring.natCast_succ] at *
    grind

private theorem seg_cast (f : Nat → Nat) (i k : Nat) :
    ((seg f i k : Nat) : R) = seg (fun j => (f j : R)) i k := by
  induction k generalizing i with
  | zero => simp [seg] <;> grind
  | succ k ih =>
    simp only [seg, Semiring.natCast_add]
    rw [ih]

private theorem charge_split (a : Nat → R) (q : Nat → Nat) (i k : Nat) :
    seg a i k = ((seg (fun j => charge (q j)) i k : Nat) : R) +
      seg (fun j => residual (a j) (q j)) i k := by
  induction k generalizing i with
  | zero => simp [seg] <;> grind
  | succ k ih =>
    have := ih (i+1)
    simp only [seg, Semiring.natCast_add, residual] at *
    grind

private theorem seg_pos_witness (f : Nat → Nat) (i k : Nat)
    (h : 0 < seg f i k) : ∃ j, 0 < f j := by
  induction k generalizing i with
  | zero => simp [seg] at h
  | succ k ih =>
    by_cases hp : 0 < f i
    · exact ⟨i,hp⟩
    · apply ih (i+1)
      simp only [seg] at h
      omega

private theorem charge_pair_le (q : Nat → Nat) (t : Nat) (ht : 2 ≤ t)
    (hp : ∀ i, q (i+t)=q i) (i : Nat) :
    charge (q i) + charge (q (i+1)) ≤ seg (fun j => charge (q j)) 0 t := by
  obtain ⟨k,rfl⟩ : ∃ k, t=k+2 := ⟨t-2,by omega⟩
  let f (j : Nat) : Int := ((charge (q j) : Nat) : Int)
  have hfp (j : Nat) : f (j+(k+2)) = f j := by simp only [f,hp]
  have he := seg_shift f (k+2) hfp i
  have h1 := seg_cast (R:=Int) (fun j => charge (q j)) 0 (k+2)
  have h2 := seg_cast (R:=Int) (fun j => charge (q j)) i (k+2)
  change _ = seg f 0 (k+2) at h1
  change _ = seg f i (k+2) at h2
  rw [←h2,←h1] at he
  simp only [seg] at he ⊢
  omega

private theorem floor_unique (a : R) (p q : Nat)
    (h₁ : floorSlot a p) (h₂ : floorSlot a q) : p=q := by
  obtain ⟨hl,hu⟩ := h₁
  obtain ⟨hl',hu'⟩ := h₂
  have h₃ : (p:R) < ((q+1:Nat):R) := by simp only [Semiring.natCast_add]; grind
  have h₄ : (q:R) < ((p+1:Nat):R) := by simp only [Semiring.natCast_add]; grind
  have := OrderedRing.lt_of_natCast_lt_natCast _ _ h₃
  have := OrderedRing.lt_of_natCast_lt_natCast _ _ h₄
  omega

private theorem merged_power (B b c g : Nat) (z : R)
    (hbc : b+c ≤ B) (hz : 1 ≤ z) (hz' : z < 4)
    (hg : floorSlot ((b:R)+(c:R)+z) g) :
    2^(B-b-c+(g-1)) = 2^B * weight z := by
  have eq_of_bracket (u : Nat) (h : floorSlot z u) : g=b+c+u := by
    apply floor_unique _ _ _ hg
    obtain ⟨hu₁,hu₂⟩ := h
    unfold floorSlot
    simp only [Semiring.natCast_add]
    grind
  by_cases h2 : z<2
  · have eq := eq_of_bracket 1 (by unfold floorSlot; grind)
    have e : B-b-c+(g-1)=B := by omega
    simp [e,weight,h2]
  · by_cases h3 : z<3
    · have eq := eq_of_bracket 2 (by unfold floorSlot; grind)
      have e : B-b-c+(g-1)=B+1 := by omega
      simp [e,weight,h2,h3,Nat.pow_succ]
    · have eq := eq_of_bracket 3 (by unfold floorSlot; grind)
      have e : B-b-c+(g-1)=B+2 := by omega
      simp [e,weight,h2,h3,Nat.pow_add]

private theorem seg_scale (f : Nat → Nat) (c i k : Nat) :
    seg (fun j => c*f j) i k = c*seg f i k := by
  induction k generalizing i with
  | zero => simp [seg]
  | succ k ih => simp only [seg, Nat.mul_add, ih]

/-- Full scalar implication from original normalized arcs and their floors.
The score of a vertex deletes its two individual arc charges and inserts
the charge of their merged gap. All normalization and power factoring
are proved here. A separate geometric argument identifies these gaps
with those of the corresponding cyclic planar configuration. -/
theorem sharp_arc_capacity (a : Nat → R) (q g : Nat → Nat)
    (t n : Nat) (low : Bool) (ht : 5 ≤ t) (hn : 3 ≤ n)
    (hp : ∀ i, a (i+t) = a i)
    (hq : ∀ i, floorSlot (a i) (q i))
    (hg : ∀ i, floorSlot (a i + a (i+1)) (g i))
    (hlegal : ∀ i, 1 ≤ a i + a (i+1))
    (hband : floorSlot (seg a 0 t) n)
    (hL : low = true → 2*seg a 0 t < 2*(n:R)+1) :
    let B := seg (fun j => charge (q j)) 0 t
    seg (fun j => 2^(B - charge (q j) - charge (q (j+1)) + (g j-1))) 0 t
      ≤ (if low then 6 else 7) * 2^(n-3) := by
  intro B
  let y (j : Nat) := residual (a j) (q j)
  have hqp (j : Nat) : q (j+t)=q j := by
    have hj := hq (j+t)
    rw [hp] at hj
    exact floor_unique _ _ _ hj (hq j)
  have hyp (j : Nat) : y (j+t)=y j := by simp only [y,hp,hqp]
  have hy (j : Nat) := slot_bounds _ _ (hq j)
  have hy₀ (j : Nat) : 0 ≤ y j := (hy j).1
  have hel (j : Nat) : 1 ≤ edge y j := by
    have hj := hy j
    have hj' := hy (j+1)
    have ha := hlegal j
    unfold edge y
    by_cases h : 0 < charge (q j)
    · have := hj.2.2 h; grind
    · by_cases h' : 0 < charge (q (j+1))
      · have := hj'.2.2 h'; grind
      · have e : charge (q j)=0 := by omega
        have e' : charge (q (j+1))=0 := by omega
        simp only [residual,e,e']; grind
  have hs := charge_split a q 0 t
  change seg a 0 t = (B:R) + seg y 0 t at hs
  obtain ⟨hlo,hhi⟩ := hband
  have hs₀ := seg_nonneg y hy₀ 0 t
  have hbnr : (B:R)<((n+1:Nat):R) := by simp only [Semiring.natCast_add]; grind
  have hbn := OrderedRing.lt_of_natCast_lt_natCast _ _ hbnr
  let D := n-B
  have hDB : D+B=n := by dsimp [D]; omega
  have hcast : (D:R)+(B:R)=(n:R) := by
    rw [←Semiring.natCast_add,hDB]
  have hDcase : 3 ≤ D ∨ ∃ i, 1 ≤ y i := by
    by_cases hb : B=0
    · left; omega
    · right
      obtain ⟨i,hi⟩ := seg_pos_witness (fun j => charge (q j)) 0 t (by change 0<B; omega)
      exact ⟨i,(hy i).2.2 hi⟩
  have hsu : seg y 0 t < (D:R)+1 := by grind
  have hlow : low=true → 2*seg y 0 t < 2*(D:R)+1 := by
    intro hl
    have := hL hl
    grind
  have bound := sharp_residual_capacity y t D low ht hyp hy₀ hel hsu hlow hDcase
  have hD : 3 ≤ D := by
    rcases hDcase with h|⟨i,hi⟩
    · exact h
    · have := unit_and_pairs y t ht hyp hy₀ hel i hi
      apply Classical.byContradiction
      intro h
      have := OrderedRing.natCast_le_natCast_of_le (R:=R) D 2 (by omega)
      grind
  have hw (j : Nat) :
      2^(B - charge (q j) - charge (q (j+1)) + (g j-1)) =
        2^B * weight (edge y j) := by
    apply merged_power _ _ _ _ _ (charge_pair_le q t (by omega) hqp j) (hel j)
    · have h₁ := (hy j).2.1
      have h₂ := (hy (j+1)).2.1
      change y j < 2 at h₁
      change y (j+1) < 2 at h₂
      unfold edge
      grind
    · have H := hg j
      have he : ((charge (q j):Nat):R)+((charge (q (j+1)):Nat):R)+edge y j = a j+a (j+1) := by
        unfold edge y residual
        grind
      rwa [he]
  have hfun := funext hw
  rw [hfun, seg_scale]
  have hb := Nat.mul_le_mul_left (2^B) bound
  have he : n-3 = B+(D-3) := by omega
  rw [he,Nat.pow_add]
  simpa only [Nat.mul_left_comm] using hb

#print axioms sharp_arc_capacity

end SendovCycle
