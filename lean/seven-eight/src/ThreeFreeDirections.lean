import TightProjectiveGrid

noncomputable section
namespace R92.Tight
open JSP404 Real InnerProductGeometry R54.GapTest

/-- Projective directions ignore the sign and length of a nonzero vector. -/
def SameAxis (x y : Point) : Prop := ∃s:ℝ,s≠0 ∧ x=s • y

theorem same_of_bearing {x y : Point} {t : ℝ} (X : Bearing x t) (Y : Bearing y t) :
    SameAxis x y := by
  obtain ⟨r,rp,a,sg,ex⟩:=X
  obtain ⟨s,sp,b,tg,ey⟩:=Y
  have an : a≠0:=by rcases sg with rfl|rfl <;> norm_num
  have bn : b≠0:=by rcases tg with rfl|rfl <;> norm_num
  refine ⟨(r*a)/(s*b),div_ne_zero (mul_ne_zero rp.ne' an) (mul_ne_zero sp.ne' bn),?_⟩
  rw [ex,ey]
  simp only [smul_smul]
  rw [div_mul_cancel₀ _ (mul_ne_zero sp.ne' bn)]

/-- The same nonempty micro-axis family makes all tightly completing triples
use exactly the same three distinct grid positions, up to a permutation.
The anchor and its bearing are arbitrary and stay fixed across all completions. -/
theorem shared_slots {d : ℕ} {δ : ℝ} (dp : 0<δ) (tight : ((d:ℝ)+3)*δ=π)
    (micro : Fin d→Point) (anchor : Fin d) {t : ℝ} (line : Bearing (micro anchor) t)
    (base : Fin 3→Point) (ref : Packed δ (Sum.elim micro base)) :
    ∃slots : Fin 3↪Fin (d+3),(∀j,Bearing (base j) (grid t δ (slots j))) ∧
      ∀C : Fin 3→Point,Packed δ (Sum.elim micro C) →
        ∃p : Equiv.Perm (Fin 3),∀j,Bearing (C j) (grid t δ (slots (p j))) := by
  classical
  have number : Fintype.card (Fin d ⊕ Fin 3)=d+2+1 := by simp
  have cap : (((d+2:ℕ):ℝ)+1)*δ=π:=by push_cast;linarith only [tight]
  have place (C : Fin 3→Point) (fit : Packed δ (Sum.elim micro C)) :=
    anchored_lattice number dp cap (Sum.elim micro C) fit (Sum.inl anchor) t line
  obtain ⟨e0,_,old⟩:=place base ref
  let slots : Fin 3↪Fin (d+3) :=
    ⟨fun j=>e0 (Sum.inr j),fun _ _ h=>Sum.inr.inj (e0.injective h)⟩
  refine ⟨slots,fun j=>old (Sum.inr j),?_⟩
  intro C fit
  obtain ⟨e,_,now⟩:=place C fit
  have match_slot (j : Fin 3) : ∃k : Fin 3,e (Sum.inr j)=e0 (Sum.inr k) := by
    cases h:e0.symm (e (Sum.inr j)) with
    | inr k => exact ⟨k,by rw [←h,e0.apply_symm_apply]⟩
    | inl k =>
      have same : e0 (Sum.inl k)=e (Sum.inr j):=by rw [←h,e0.apply_symm_apply]
      have X:=old (Sum.inl k)
      rw [same] at X
      have gap:=apart (now (Sum.inr j)) X (by simp [pi_pos.le]) (fit.2 (Sum.inr j) (Sum.inl k) (by simp))
      rw [sub_self,abs_zero] at gap
      exact (dp.not_ge gap).elim
  choose p pm using match_slot
  have inj : Function.Injective p := by
    intro a b ab
    apply Sum.inr.inj (α:=Fin d)
    apply e.injective
    rw [pm,pm,ab]
  let perm:=Equiv.ofBijective p ⟨inj,Finite.surjective_of_injective inj⟩
  refine ⟨perm,?_⟩
  intro j
  change Bearing (C j) (grid t δ (e0 (Sum.inr (p j))))
  rw [←pm]
  exact now (Sum.inr j)

/-- A reference triple and any other feasible tightly completing triple
are identical as unordered projective directions. -/
theorem completion_perm {d : ℕ} (positive : 0<d) {δ : ℝ} (dp : 0<δ)
    (tight : ((d:ℝ)+3)*δ=π) {micro : Fin d→Point} {base C : Fin 3→Point}
    (ref : Packed δ (Sum.elim micro base)) (fit : Packed δ (Sum.elim micro C)) :
    ∃p : Equiv.Perm (Fin 3),∀j,SameAxis (C j) (base (p j)) := by
  let a : Fin d:=⟨0,positive⟩
  obtain ⟨t,_,_,line⟩:=polar (micro a) (ref.1 (Sum.inl a))
  obtain ⟨_,slots,all⟩:=shared_slots dp tight micro a line base ref
  obtain ⟨p,eq⟩:=all C fit
  exact ⟨p,fun j=>same_of_bearing (eq j) (slots (p j))⟩

/-- Each candidate may have a different tight completing triple. Distinct
projective directions among all candidates together still number at most three. -/
theorem candidate_count {I : Type*} [Fintype I] {d : ℕ} (positive : 0<d) {δ : ℝ} (dp : 0<δ)
    (tight : ((d:ℝ)+3)*δ=π) (micro : Fin d→Point) (x : I→Point)
    (distinct : ∀a b,a≠b→¬SameAxis (x a) (x b))
    (realize : ∀a,∃C : Fin 3→Point,Packed δ (Sum.elim micro C) ∧ ∃j,C j=x a) :
    Fintype.card I≤3 := by
  classical
  cases isEmpty_or_nonempty I with
  | inl h => simp
  | inr h =>
    obtain ⟨base,ref,_⟩:=realize (Classical.choice h)
    have witness (a) : ∃k,SameAxis (x a) (base k) := by
      obtain ⟨C,fit,j,eq⟩:=realize a
      obtain ⟨p,axis⟩:=completion_perm positive dp tight ref fit
      exact ⟨p j,eq ▸ axis j⟩
    choose k val using witness
    have ki : Function.Injective k := by
      intro a b same
      by_contra ne
      obtain ⟨r,rn,re⟩:=val a
      obtain ⟨s,sn,se⟩:=val b
      apply distinct a b ne
      refine ⟨r/s,div_ne_zero rn sn,?_⟩
      rw [re,se,same,smul_smul,div_mul_cancel₀ _ sn]
    simpa using Fintype.card_le_of_injective k ki

end R92.Tight
#print axioms R92.Tight.shared_slots
#print axioms R92.Tight.completion_perm
#print axioms R92.Tight.candidate_count
