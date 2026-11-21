import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic

noncomputable section
open scoped BigOperators Classical
namespace R67.Board

variable {C G J : Type*} [Fintype C] [Fintype G] [Fintype J]

/-- Global gaps belonging to one local gap at one center. -/
def fiber (slot : C→G→J) (i : C) (j : J) : Finset G := Finset.univ.filter (fun a=>slot i a=j)
def width (g : G→ℝ) (A : Finset G) : ℝ := ∑ a∈A,g a
def total (g : G→ℝ) : ℝ := width g Finset.univ
def digit (x : ℝ) : ℕ := ⌊x⌋₊-1
def exponent (slot : C→G→J) (g : G→ℝ) (i : C) := ∑ j,digit (width g (fiber slot i j))
def capacity (slot : C→G→J) (g : G→ℝ) : ℕ := ∑ i,2^(exponent slot g i)
def cutoff (k : ℕ) (δ : ℝ) : ℕ := if δ<1/2 then 2^k else 2^k+2^(k-2)

/-- An exact integer thinning. All subsets include every circular interval
and its complement without a hypothesis about the chart cut. -/
structure WeakReduction (slot : C→G→J) (large small : G→ℝ) (d : ℕ) : Prop where
  period : total large=total small+d
  rows : ∀i,exponent slot large i=exponent slot small i+d
  weak : ∀A,1≤width large A ↔ 1≤width small A
  zero : ∀a,large a=0 ↔ small a=0

structure Reduction (slot : C→G→J) (large small : G→ℝ) (d : ℕ) : Prop
    extends WeakReduction slot large small d where
  strict : ∀A,1<width large A ↔ 1<width small A

variable (slot : C→G→J)

theorem Reduction.refl (g : G→ℝ) : Reduction slot g g 0 :=
  ⟨⟨by simp,fun i=>by simp,fun _=>Iff.rfl,fun _=>Iff.rfl⟩,fun _=>Iff.rfl⟩

theorem WeakReduction.compose {a b c : G→ℝ} {d e : ℕ}
    (x : WeakReduction slot a b d) (y : WeakReduction slot b c e) : WeakReduction slot a c (d+e) :=
  ⟨by rw [x.period,y.period];push_cast;ring,fun i=>by rw [x.rows,y.rows];omega,
   fun A=>(x.weak A).trans (y.weak A),fun h=>(x.zero h).trans (y.zero h)⟩

theorem Reduction.compose {a b c : G→ℝ} {d e : ℕ}
    (x : Reduction slot a b d) (y : Reduction slot b c e) : Reduction slot a c (d+e) :=
  ⟨WeakReduction.compose slot x.toWeakReduction y.toWeakReduction,fun A=>(x.strict A).trans (y.strict A)⟩

def adjust (g : G→ℝ) (h : G) (t : ℝ) (a : G) := g a + if a=h then t else 0

theorem width_adjust (g : G→ℝ) (h : G) (t : ℝ) (A : Finset G) :
    width (adjust g h t) A=width g A+if h∈A then t else 0 := by
  classical
  simp [width,adjust,Finset.sum_add_distrib,Finset.sum_ite_eq']

/-- Integral enlargement of a gap of width at least one. The endpoint one
preserves all weak arc tests. -/
theorem grow_closed (g : G→ℝ) (nn : ∀a,0≤g a) (h : G) (long : 1≤g h) (d : ℕ) :
    WeakReduction slot (adjust g h d) g d := by
  classical
  have lower (A : Finset G) (inc : h∈A) : 1≤width g A :=
    long.trans (Finset.single_le_sum (f:=g) (fun a _ => nn a) inc)
  have nz : 0≤(d:ℝ) := Nat.cast_nonneg _
  refine ⟨by simp [total,width_adjust],?_,?_,?_⟩
  · intro i
    unfold exponent
    calc
      _=∑ j : J,(digit (width g (fiber slot i j))+if j=slot i h then d else 0) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases eq : j=slot i h
        · subst j
          have inc : h∈fiber slot i (slot i h) := by simp [fiber]
          have lo:=lower _ inc
          have fl : 1≤⌊width g (fiber slot i (slot i h))⌋₊ := Nat.le_floor (by simpa using lo)
          rw [width_adjust,ite_eq_left inc,ite_eq_left rfl]
          simp only [digit,Nat.floor_add_natCast (by linarith : 0≤width g (fiber slot i (slot i h))) d]
          omega
        · have out : h∉fiber slot i j := by simp [fiber,Ne.symm eq]
          rw [width_adjust,ite_eq_right out,ite_eq_right eq,add_zero,add_zero]
      _=_ := by simp [Finset.sum_add_distrib,Finset.sum_ite_eq']
  · intro A
    rw [width_adjust]
    by_cases inc : h∈A
    · simp only [ite_eq_left inc];exact ⟨fun _=>lower A inc,fun _=>by linarith [lower A inc]⟩
    · simp [inc]
  · intro a
    by_cases eq : a=h
    · subst a;simp [adjust,show g h≠0 by linarith,show g h+(d:ℝ)≠0 by linarith]
    · simp [adjust,eq]

/-- Integral enlargement of a gap strictly larger than one preserves strict
arc tests as well. -/
theorem grow (g : G→ℝ) (nn : ∀a,0≤g a) (h : G) (long : 1<g h) (d : ℕ) :
    Reduction slot (adjust g h d) g d := by
  classical
  refine ⟨grow_closed slot g nn h long.le d,?_⟩
  intro A
  rw [width_adjust]
  by_cases inc : h∈A
  · have lo : 1<width g A := long.trans_le (Finset.single_le_sum (f:=g) (fun a _=>nn a) inc)
    simp only [ite_eq_left inc]
    exact ⟨fun _=>lo,fun _=>by linarith [show (0:ℝ)≤d from Nat.cast_nonneg _]⟩
  · simp [inc]

/-- Shortening a global gap of width at least two by exactly one. -/
theorem thin_one (g : G→ℝ) (nn : ∀a,0≤g a) (h : G) (long : 2≤g h) :
    (∀a,0≤adjust g h (-1) a) ∧ WeakReduction slot g (adjust g h (-1)) 1 := by
  classical
  let f := adjust g h (-1)
  have fh : f h=g h-1 := by simp [f,adjust,sub_eq_add_neg]
  have nnf (a : G) : 0≤f a := by
    by_cases eq : a=h
    · subst a;linarith
    · simpa [f,adjust,eq] using nn a
  have inv : adjust f h (1:ℕ)=g := by
    funext a
    by_cases eq : a=h
    · subst a;simp [f,adjust]
    · simp [f,adjust,eq]
  have step:=grow_closed slot f nnf h (by linarith : 1≤f h) 1
  rw [inv] at step
  exact ⟨nnf,step⟩

/-- Stop at any chosen strip with target ≥ 2 times the number of global gaps.
Only a gap of width strictly greater than two is shortened. -/
theorem reduce_to (target : ℕ) (room : 2*Fintype.card G≤target) {δ : ℝ} (δpos : 0≤δ)
    (d : ℕ) (g : G→ℝ) (nn : ∀a,0≤g a) (period : total g=(target:ℝ)+d+δ) :
    ∃ f : G→ℝ, (∀a,0≤f a) ∧ total f=(target:ℝ)+δ ∧ Reduction slot g f d := by
  classical
  induction d generalizing g with
  | zero => exact ⟨g,nn,by simpa using period,Reduction.refl slot g⟩
  | succ d ih =>
    obtain ⟨h,long⟩ : ∃h,2<g h := by
      by_contra! no
      have all : total g≤(Fintype.card G:ℝ)*2 := by
        simpa [total,width] using (Finset.sum_le_sum (s:=Finset.univ) (fun a _=>no a))
      have count : (2:ℝ)*(Fintype.card G:ℝ)≤target := by exact_mod_cast room
      push_cast at period
      linarith [show (0:ℝ)≤d from Nat.cast_nonneg d]
    let f := adjust g h (-1)
    have fh : f h=g h-1 := by simp [f,adjust,sub_eq_add_neg]
    have nnf (a : G) : 0≤f a := by
      by_cases eq : a=h
      · subst a;linarith
      · simpa [f,adjust,eq] using nn a
    have inv : adjust f h (1:ℕ)=g := by
      funext a
      by_cases eq : a=h
      · subst a;simp [f,adjust]
      · simp [f,adjust,eq]
    have one := grow slot f nnf h (by linarith : 1<f h) 1
    rw [inv] at one
    have per := one.period
    push_cast at period per
    obtain ⟨b,bn,bp,tail⟩ := ih f nnf (by linarith)
    exact ⟨b,bn,bp,by simpa [Nat.add_comm] using Reduction.compose slot one tail⟩

theorem Reduction.mass {g f : G→ℝ} {d : ℕ} (h : Reduction slot g f d) :
    capacity slot g=capacity slot f*2^d := by
  simp [capacity,h.rows,pow_add,Finset.sum_mul]

theorem cutoff_shift {k : ℕ} (hk : 2≤k) (d : ℕ) (δ : ℝ) :
    cutoff (k+d) δ=cutoff k δ*2^d := by
  have sub : k+d-2=(k-2)+d := by omega
  unfold cutoff
  split_ifs <;> simp [sub,pow_add,add_mul]

/-- Any prescribed number k≥2 is reduced to min(k,20) for a ten-gap, five-center
board; excess, equality, and the full non-strict bound transfer in both directions. -/
theorem five (S : Fin 5→Fin 10→Fin 4) (g : Fin 10→ℝ) (nn : ∀a,0≤g a)
    {k : ℕ} (hk : 2≤k) {δ : ℝ} (lo : 0≤δ) (period : total g=(k:ℝ)+δ) :
    let s:=min k 20
    ∃f : Fin 10→ℝ, (∀a,0≤f a) ∧ total f=(s:ℝ)+δ ∧
      Reduction S g f (k-s) ∧
      (capacity S g≤cutoff k δ ↔ capacity S f≤cutoff s δ) ∧
      (capacity S g=cutoff k δ ↔ capacity S f=cutoff s δ) ∧
      (cutoff k δ<capacity S g ↔ cutoff s δ<capacity S f) := by
  let s:=min k 20
  have sle : s≤k := min_le_left _ _
  have sg : 2≤s := le_min hk (by decide)
  have split : s+(k-s)=k := by omega
  obtain ⟨f,nnf,area,link⟩ : ∃ f : Fin 10→ℝ,(∀a,0≤f a) ∧ total f=(s:ℝ)+δ ∧ Reduction S g f (k-s) := by
    by_cases low : k≤20
    · have eq : s=k := min_eq_left low
      exact ⟨g,nn,eq ▸ period,by rw [eq,Nat.sub_self];exact Reduction.refl S g⟩
    · have eq : s=20 := min_eq_right (by omega)
      have room : 2*Fintype.card (Fin 10)≤s := by rw [eq]; decide
      apply reduce_to S s room lo (k-s) g nn
      simpa only [←Nat.cast_add,split] using period
  have cap := Reduction.mass S link
  have cut := cutoff_shift sg (k-s) δ
  rw [split] at cut
  have positive : 0<(2:ℕ)^(k-s) := by positivity
  refine ⟨f,nnf,area,link,?_,?_,?_⟩
  · rw [cap,cut];exact Nat.mul_le_mul_right_iff positive
  · rw [cap,cut];constructor <;> intro h
    · exact Nat.eq_of_mul_eq_mul_right positive h
    · exact congrArg (fun z=>z*2^(k-s)) h
  · rw [cap,cut];exact Nat.mul_lt_mul_right positive

#print axioms R67.Board.thin_one
end R67.Board
#print axioms R67.Board.grow
#print axioms R67.Board.reduce_to
#print axioms R67.Board.five
