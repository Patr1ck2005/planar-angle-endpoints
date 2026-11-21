import FiveBoard

noncomputable section
open scoped BigOperators Classical
namespace R67.Board

abbrev FiveSlots := Fin 5→Fin 10→Fin 4

private theorem pivot {g : Fin 10→ℝ} (h : 20≤total g) : ∃a,2≤g a := by
  by_contra! no
  have sum := Finset.sum_lt_sum_of_nonempty (s:=Finset.univ) Finset.univ_nonempty (fun j _=>no j)
  have small : total g<20 := by
    unfold total width
    norm_num at sum
    exact sum
  linarith

theorem WeakReduction.mass {C G J : Type*} [Fintype C] [Fintype G] [Fintype J]
    {S : C→G→J} {g f : G→ℝ} {d : ℕ} (h : WeakReduction S g f d) :
    capacity S g=capacity S f*2^d := by
  simp [capacity,h.rows,pow_add,Finset.sum_mul]

theorem WeakReduction.excess_iff {C G J : Type*} [Fintype C] [Fintype G] [Fintype J]
    {S : C→G→J} {g f : G→ℝ} {d : ℕ} (h : WeakReduction S g f d) {s : ℕ} (hs : 2≤s) (δ : ℝ) :
    cutoff (s+d) δ<capacity S g ↔ cutoff s δ<capacity S f := by
  rw [h.mass,cutoff_shift hs]
  exact Nat.mul_lt_mul_right (by positivity)

/-- With weak macro inequalities, the last move from 20 to 19 is also valid
when its selected global gap is exactly two. -/
theorem five_weak19 (S : FiveSlots) (g : Fin 10→ℝ) (nn : ∀a,0≤g a)
    {k : ℕ} (hk : 2≤k) {δ : ℝ} (lo : 0≤δ) (period : total g=(k:ℝ)+δ) :
    let s:=min k 19
    ∃f : Fin 10→ℝ, (∀a,0≤f a) ∧ total f=(s:ℝ)+δ ∧ WeakReduction S g f (k-s) ∧
      (cutoff k δ<capacity S g ↔ cutoff s δ<capacity S f) := by
  by_cases low : k≤19
  · dsimp only
    rw [min_eq_left low,Nat.sub_self]
    exact ⟨g,nn,period,(Reduction.refl S g).toWeakReduction,Iff.rfl⟩
  have high : 20≤k := by omega
  have sum : 20+(k-20)=k := by omega
  obtain ⟨b,bn,area,link⟩ := reduce_to S 20 (by decide) lo (k-20) g nn
    (by change total g=((20:ℕ):ℝ)+((k-20:ℕ):ℝ)+δ
        rw [←Nat.cast_add,sum];exact period)
  norm_num at area
  obtain ⟨a,wide⟩ := pivot (g:=b) (by linarith)
  obtain ⟨fn,last⟩ := thin_one S b bn a wide
  let f:=adjust b a (-1)
  have area' := last.period
  have fix : WeakReduction S g f (k-19) := by
    convert WeakReduction.compose S link.toWeakReduction last using 1 <;> omega
  have eq : 19+(k-19)=k := by omega
  dsimp only
  rw [min_eq_right (by omega : 19≤k)]
  refine ⟨f,fn,?_,fix,?_⟩
  · dsimp [f] at *
    push_cast at area'
    linarith
  · simpa only [eq] using fix.excess_iff (s:=19) (by decide) δ

/-- From any strip above ten there is a gap larger than one. Enlarging it
preserves signs, weak and strict macro comparisons and every cutoff comparison. -/
theorem lift_from (S : FiveSlots) (f : Fin 10→ℝ) (nn : ∀a,0≤f a)
    {s : ℕ} (hs : 10<s) {δ : ℝ} (lo : 0≤δ) (per : total f=(s:ℝ)+δ) (d : ℕ) :
    ∃ g : Fin 10→ℝ, (∀a,0≤g a) ∧ total g=((s+d:ℕ):ℝ)+δ ∧ Reduction S g f d ∧
      (cutoff (s+d) δ<capacity S g ↔ cutoff s δ<capacity S f) := by
  obtain ⟨h,long⟩ : ∃ h,1<f h := by
    by_contra! no
    have up : total f≤10 := by
      simpa [total,width] using (Finset.sum_le_sum (s:=Finset.univ) (fun a _=>no a))
    have lt : (10:ℝ)<s := by exact_mod_cast hs
    linarith
  have link := grow S f nn h long d
  refine ⟨adjust f h d,?_,?_,link,link.toWeakReduction.excess_iff (by omega) δ⟩
  · intro a
    by_cases e : a=h <;> simp [adjust,e,nn,show ∀z,0≤f z+(d:ℝ) from fun z=>add_nonneg (nn z) (Nat.cast_nonneg _)]
  · rw [link.period,per]
    push_cast
    ring

/-- Executable search interfaces may impose any fixed collection of macro
arcs; they need only list the global gaps in each tested arc. -/
def legal (req : Finset (Fin 10)→Prop) (g : Fin 10→ℝ) :=
  ∀ A,req A → 1≤width g A

def bad (S : FiveSlots) (req : Finset (Fin 10)→Prop) (k : ℕ) (δ : ℝ) :=
  ∃g : Fin 10→ℝ,(∀j,0≤g j) ∧ total g=(k:ℝ)+δ ∧ legal req g ∧ cutoff k δ<capacity S g

/-- A fixed layout with its legal macro arcs has an overweight board in some
strip if and only if it has one in strips 2 through 19. -/
theorem bad_iff_bounded (S : FiveSlots) (req : Finset (Fin 10)→Prop) {δ : ℝ} (hp : 0≤δ) :
    (∃ k : ℕ,2≤k ∧ bad S req k δ) ↔ ∃ k : ℕ,2≤k ∧ k≤19 ∧ bad S req k δ := by
  constructor
  · rintro ⟨k,hk,g,nn,period,tests,excess⟩
    obtain ⟨f,nf,pf,link,compare⟩:=five_weak19 S g nn hk hp period
    exact ⟨min k 19,le_min hk (by decide),min_le_right _ _,f,nf,pf,
      fun A ok=>(link.weak A).mp (tests A ok),compare.mp excess⟩
  · rintro ⟨k,hk,_,witness⟩
    exact ⟨k,hk,witness⟩

/-- For a fixed layout, collection of macro tests and fractional part, the
existence of an overweight board is constant on the entire tail k≥19. -/
theorem bad_tail_iff (S : FiveSlots) (req : Finset (Fin 10)→Prop) {δ : ℝ} (hp : 0≤δ)
    {k : ℕ} (hk : 19≤k) : bad S req k δ ↔ bad S req 19 δ := by
  constructor
  · rintro ⟨g,nn,period,tests,excess⟩
    obtain ⟨f,nf,pf,link,compare⟩:=five_weak19 S g nn (by omega : 2≤k) hp period
    rw [min_eq_right hk] at pf link compare
    exact ⟨f,nf,pf,fun A ok=>(link.weak A).mp (tests A ok),compare.mp excess⟩
  · rintro ⟨f,nn,period,tests,excess⟩
    obtain ⟨g,ng,pg,link,compare⟩:=lift_from S f nn (by decide : 10<19) hp period (k-19)
    have sum : 19+(k-19)=k := by omega
    rw [sum] at pg compare
    exact ⟨g,ng,pg,fun A ok=>(link.weak A).mpr (tests A ok),compare.mpr excess⟩

end R67.Board
#print axioms R67.Board.five_weak19
#print axioms R67.Board.lift_from
#print axioms R67.Board.bad_tail_iff
#print axioms R67.Board.bad_iff_bounded
