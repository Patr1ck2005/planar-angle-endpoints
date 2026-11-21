import FiveBoardCases

noncomputable section
open scoped BigOperators Classical
namespace R67.Board
open Finset

/-- Total slot widths partition the ten gaps, including gaps of width zero. -/
theorem marked_exponent_le_total (S : FiveSlots) {g : Fin 10→ℝ}
    (nn : ∀a,0≤g a) (i : Fin 5) : (exponent S g i:ℝ)≤total g := by
  unfold exponent
  push_cast
  calc
    _ ≤ ∑j : Fin 4,width g (fiber S i j) := by
      apply sum_le_sum
      intro j _
      have h : 0≤width g (fiber S i j):=sum_nonneg (fun a _=>nn a)
      exact (show ((digit (width g (fiber S i j)) : ℕ):ℝ)≤(⌊width g (fiber S i j)⌋₊:ℝ) by
        exact_mod_cast Nat.sub_le _ _).trans (Nat.floor_le h)
    _ = total g := by
      simp only [total,width,fiber,Finset.sum_filter]
      rw [Finset.sum_comm]
      apply sum_congr rfl
      intro a _
      rw [sum_eq_single (S i a)]
      · simp
      · intro b _ ne
        exact ite_eq_right ne.symm
      · intro h
        exact (h (mem_univ _)).elim

def clipTwo (g : Fin 10→ℝ) (a : Fin 10) := min (g a) 2

private theorem clip_width (g : Fin 10→ℝ) (nn : ∀a,0≤g a) (A : Finset (Fin 10))
    {q : ℝ} (small : q≤2) : q≤width g A ↔ q≤width (clipTwo g) A := by
  constructor
  · intro ok
    by_cases w : ∃a∈A,2≤g a
    · obtain ⟨a,inc,wide⟩:=w
      exact small.trans ((show 2≤clipTwo g a by simp [clipTwo,min_eq_right wide]).trans
        (Finset.single_le_sum (f:=clipTwo g) (fun j _=>le_min (nn j) (by norm_num)) inc))
    · have eq:width (clipTwo g) A=width g A := by
        apply sum_congr rfl
        intro a ha
        exact min_eq_left (le_of_not_ge (fun wide=>w ⟨a,ha,wide⟩))
      rwa [eq]
  · intro ok
    exact ok.trans (sum_le_sum (fun a _=>min_le_left _ _))

private theorem clip_digit_one (S : FiveSlots) {g : Fin 10→ℝ} (nn : ∀a,0≤g a)
    (i : Fin 5) (pos : 1≤exponent S g i) : 1≤exponent S (clipTwo g) i := by
  obtain ⟨j,hj⟩ : ∃j,0<digit (width g (fiber S i j)) := by
    by_contra! no
    have zero : exponent S g i=0:=sum_eq_zero (fun j _=>Nat.eq_zero_of_le_zero (no j))
    omega
  have fl : 2≤⌊width g (fiber S i j)⌋₊ := by unfold digit at hj;omega
  have nnw : 0≤width g (fiber S i j) := sum_nonneg (fun a _=>nn a)
  have before : 2≤width g (fiber S i j) :=
    (show (2:ℝ)≤(⌊width g (fiber S i j)⌋₊:ℝ) by exact_mod_cast fl).trans (Nat.floor_le nnw)
  have after:=(clip_width g nn _ (q:=2) le_rfl).mp before
  have full : 2≤⌊width (clipTwo g) (fiber S i j)⌋₊:=Nat.le_floor (by simpa using after)
  exact (show 1≤digit (width (clipTwo g) (fiber S i j)) by unfold digit;omega).trans
    (single_le_sum (f:=fun z=>digit (width (clipTwo g) (fiber S i z))) (fun z _=>Nat.zero_le _) (mem_univ j))

/-- Retains all marked exponent lower bounds after subtracting the same integer from
the strip index. Each mark can carry an extra bit. The full weak subset system and
the original zero gap pattern survive. The resulting ten gaps lie in [0,2]. -/
theorem thin_marks (S : FiveSlots) (marks : Finset (Fin 5)) (marked : marks.Nonempty)
    (bonus : Fin 5→ℕ) (one : ∀i∈marks,bonus i≤1) {budget : ℝ} (k : ℕ)
    (g : Fin 10→ℝ) (nn : ∀a,0≤g a) (strict : total g<(k:ℝ)+budget)
    (rows : ∀i∈marks,k+bonus i≤exponent S g i) :
    ∃s≤k, s≤20 ∧ ∃f : Fin 10→ℝ, (∀a,0≤f a ∧ f a≤2) ∧ total f<(s:ℝ)+budget ∧
      (∀A,1≤width g A ↔ 1≤width f A) ∧ (∀a,g a=0 ↔ f a=0) ∧
      ∀i∈marks,s+bonus i≤exponent S f i := by
  induction k generalizing g with
  | zero =>
    have small (a) : 0≤clipTwo g a ∧ clipTwo g a≤2:=⟨le_min (nn a) (by norm_num),min_le_right _ _⟩
    refine ⟨0,le_rfl,by decide,clipTwo g,small,?_,fun A=>clip_width g nn A (by norm_num),?_,?_⟩
    · exact (sum_le_sum (s:=univ) (fun a _=>min_le_left (g a) 2)).trans_lt strict
    · intro a
      by_cases ge : g a≤2
      · simp [clipTwo,min_eq_left ge]
      · have gt : 2<g a:=lt_of_not_ge ge
        simp [clipTwo,min_eq_right gt.le,show g a≠0 by linarith]
    · intro i inc
      have cap:=one i inc
      by_cases z : bonus i=0
      · simp [z]
      · have h : bonus i=1 := by omega
        simpa only [h,Nat.zero_add] using clip_digit_one S nn i
          (by simpa only [h,Nat.zero_add] using rows i inc)
  | succ k ih =>
    by_cases wide : ∃a,2<g a
    · obtain ⟨a,ah⟩:=wide
      obtain ⟨nf,red⟩:=thin_one S g nn a ah.le
      have t:=red.period
      obtain ⟨s,sk,cap,f,box,lo,weak,z,keep⟩:=ih _ nf
        (by push_cast at strict t;linarith)
        (fun i inc=>by have old:=rows i inc;have eq:=red.rows i;omega)
      exact ⟨s,by omega,cap,f,box,lo,fun A=>(red.weak A).trans (weak A),
        fun j=>(red.zero j).trans (z j),keep⟩
    · have box (a):0≤g a ∧ g a≤2:=⟨nn a,le_of_not_gt (fun q=>wide ⟨a,q⟩)⟩
      obtain ⟨i,inc⟩:=marked
      have cap : total g≤20 := by
        have all:=sum_le_sum (s:=univ) (fun a _=>(box a).2)
        norm_num [total,width] at all ⊢
        exact all
      have bit : ((k+1:ℕ):ℝ)≤(exponent S g i:ℝ) := by
        exact_mod_cast (show k+1≤exponent S g i by have h:=rows i inc;omega)
      have size : k+1≤20 := by exact_mod_cast bit.trans ((marked_exponent_le_total S nn i).trans cap)
      exact ⟨k+1,le_rfl,size,g,box,strict,fun _=>Iff.rfl,fun _=>Iff.rfl,rows⟩

/-- A fixed macro-arc system and every marked position survive. -/
theorem marked_thinning (S : FiveSlots) (req : Finset (Fin 10)→Prop)
    (marks : Finset (Fin 5)) (marked : marks.Nonempty)
    (bonus : Fin 5→ℕ) (one : ∀i∈marks,bonus i≤1) {budget : ℝ} (k : ℕ)
    (g : Fin 10→ℝ) (nn : ∀a,0≤g a) (strict : total g<(k:ℝ)+budget) (mac : legal req g)
    (rows : ∀i∈marks,k+bonus i≤exponent S g i) :
    ∃s≤k, s≤20 ∧ ∃f : Fin 10→ℝ,(∀a,0≤f a ∧ f a≤2) ∧ total f<(s:ℝ)+budget ∧
      legal req f ∧ (∀a,g a=0 ↔ f a=0) ∧ ∀i∈marks,s+bonus i≤exponent S f i := by
  obtain ⟨s,le,sz,f,box,lim,weak,z,keep⟩:=thin_marks S marks marked bonus one k g nn strict rows
  exact ⟨s,le,sz,f,box,lim,fun A h=>(weak A).mp (mac A h),z,keep⟩

/-- Canonical Farkas roles: four marked sites, an optional distinguished heavy site,
and one unmarked site that is retained in every macro constraint. -/
theorem thin_farkas (S : FiveSlots) (req : Finset (Fin 10)→Prop)
    (x : Fin 5) (p : Option (Fin 5)) (k : ℕ) (g : Fin 10→ℝ) (nn : ∀a,0≤g a)
    (strict : total g<(k:ℝ)+(if p.isSome then 3 else 5/2)) (mac : legal req g)
    (rows : ∀ i, i≠x → k+(if p=some i then 1 else 0)≤exponent S g i) :
    ∃s≤k, s≤20 ∧ ∃f : Fin 10→ℝ, (∀a,0≤f a ∧ f a≤2) ∧
      total f<(s:ℝ)+(if p.isSome then 3 else 5/2) ∧ legal req f ∧
      (∀a,g a=0 ↔ f a=0) ∧ ∀ i, i≠x → s+(if p=some i then 1 else 0)≤exponent S f i := by
  let mark:Finset (Fin 5):=univ.erase x
  obtain ⟨y,ne⟩:=exists_ne x
  have nonempty : mark.Nonempty:=⟨y,mem_erase.mpr ⟨ne,mem_univ _⟩⟩
  let bonus (i : Fin 5) : ℕ:=if p=some i then 1 else 0
  have one (i) (_ : i∈mark) : bonus i≤1:=by unfold bonus;split <;> decide
  obtain ⟨s,ks,cap,f,box,lim,law,zero,fit⟩:=marked_thinning S req mark nonempty bonus one k g nn strict mac
    (fun i hi=>rows i (mem_erase.mp hi).1)
  exact ⟨s,ks,cap,f,box,lim,law,zero,fun i hi=>fit i (mem_erase.mpr ⟨hi,mem_univ _⟩)⟩

#print axioms thin_farkas
#print axioms marked_exponent_le_total
#print axioms thin_marks
#print axioms marked_thinning
end R67.Board
