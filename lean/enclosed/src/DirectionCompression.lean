import Mathlib.Basic.Real.Basic
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace R37.DirectionCompression

variable {V E : Type*}

private def Walk (src dst : E → V) (u v : V) : List E → Prop
  | [] => u = v
  | e :: rest => src e = u ∧ Walk src dst (dst e) v rest

private theorem walk_append {src dst : E → V} {u v : V} {p q : List E} :
    Walk src dst u v (p ++ q) ↔ ∃ z, Walk src dst u z p ∧ Walk src dst z v q := by
  induction p generalizing u with
  | nil => simp [Walk]
  | cons e p ih =>
    simp only [List.cons_append, Walk, ih]
    constructor
    · rintro ⟨he,z,hp,hq⟩
      exact ⟨z,⟨he,hp⟩,hq⟩
    · rintro ⟨z,⟨he,hp⟩,hq⟩
      exact ⟨he,z,hp,hq⟩

private theorem repeated {l : List E} (h : ¬l.Nodup) :
    ∃ (p : List E) (e : E) (m s : List E), l = p ++ ((e::m) ++ (e::s)) := by
  classical
  induction l with
  | nil => simp at h
  | cons a l ih =>
    by_cases ha : a ∈ l
    · obtain ⟨m,s,hs⟩ := List.append_of_mem ha
      exact ⟨[],a,m,s,by simp [hs]⟩
    · have hn : ¬l.Nodup := fun hl => h (List.nodup_cons.mpr ⟨ha,hl⟩)
      obtain ⟨p,e,m,s,hh⟩ := ih hn
      exact ⟨a::p,e,m,s,by simp [hh]⟩

private theorem erase_repeat {src dst : E → V} {u v : V} {e : E} {p m s : List E}
    (hw : Walk src dst u v (p ++ ((e::m) ++ (e::s)))) :
    Walk src dst (src e) (src e) (e::m) ∧ Walk src dst u v (p ++ (e::s)) := by
  obtain ⟨z,hp,hr⟩ := walk_append.mp hw
  obtain ⟨q,hm,hs⟩ := walk_append.mp hr
  have hz : src e = z := hm.1
  have hq : src e = q := hs.1
  subst z
  subst q
  exact ⟨hm,walk_append.mpr ⟨src e,hp,hs⟩⟩

variable [DecidableEq E]

private def marks (marked : Finset E) (l : List E) : ℕ :=
  (l.filter fun e => decide (e ∈ marked)).length

private def winds (wrap : E → ℕ) (l : List E) : ℕ := (l.map wrap).sum

private theorem marks_le (marked : Finset E) {l : List E} (hl : l.Nodup) :
    marks marked l ≤ marked.card := by
  unfold marks
  rw [← List.toFinset_card_of_nodup (hl.filter _)]
  apply Finset.card_le_card
  intro e he
  simpa using (List.mem_filter.mp (List.mem_toFinset.mp he)).2

private def weight (marked : Finset E) (wrap : E → ℕ) (unit period : ℕ) (l : List E) : ℤ :=
  (unit : ℤ) * marks marked l - (period : ℤ) * winds wrap l

private theorem weight_append (marked : Finset E) (wrap : E → ℕ) (unit period : ℕ)
    (p q : List E) :
    weight marked wrap unit period (p ++ q) =
      weight marked wrap unit period p + weight marked wrap unit period q := by
  simp [weight, marks, winds, List.sum_append, mul_add]
  ring

private theorem real_walk {src dst : E → V} (marked : Finset E) (wrap : E → ℕ)
    (T : ℝ) (x : V → ℝ)
    (h : ∀ e, (if e ∈ marked then (1:ℝ) else 0) - (wrap e : ℝ)*T ≤ x (dst e)-x (src e))
    {u v : V} {l : List E} (hw : Walk src dst u v l) :
    (marks marked l : ℝ) - (winds wrap l : ℝ)*T ≤ x v - x u := by
  induction l generalizing u with
  | nil => obtain rfl := hw; simp [marks,winds]
  | cons e l ih =>
    obtain ⟨rfl,hr⟩ := hw
    have ht := ih hr
    have he := h e
    by_cases hm : e ∈ marked <;>
      simp [marks,winds,hm,add_mul] at ht he ⊢ <;> linarith

private theorem nonpos_closed {src dst : E → V} (marked : Finset E) (wrap : E → ℕ)
    (unit period : ℕ) (T : ℝ) (x : V → ℝ)
    (h : ∀ e, (if e ∈ marked then (1:ℝ) else 0) - (wrap e : ℝ)*T ≤ x (dst e)-x (src e))
    (rounding : ∀ A B : ℕ, A ≤ marked.card → (A : ℝ) ≤ (B : ℝ)*T →
      (unit : ℤ)*A - (period : ℤ)*B ≤ 0)
    {l : List E} {v : V} (hw : Walk src dst v v l) :
    weight marked wrap unit period l ≤ 0 := by
  by_cases hn : l.Nodup
  · apply rounding _ _ (marks_le marked hn)
    have hh := real_walk marked wrap T x h hw
    linarith
  · obtain ⟨p,e,m,s,hsplit⟩ := repeated hn
    rw [hsplit] at hw ⊢
    obtain ⟨hc,hr⟩ := erase_repeat hw
    have h₁ := nonpos_closed marked wrap unit period T x h rounding hc
    have h₂ := nonpos_closed marked wrap unit period T x h rounding hr
    simp only [weight_append] at h₂ ⊢
    omega
termination_by l.length
decreasing_by all_goals (simp_all; omega)

private theorem walk_bound {src dst : E → V} (marked : Finset E) (wrap : E → ℕ)
    (unit period : ℕ) (hc : ∀ (v : V) (l : List E), Walk src dst v v l →
      weight marked wrap unit period l ≤ 0)
    {l : List E} {u v : V} (hw : Walk src dst u v l) :
    weight marked wrap unit period l ≤ (unit : ℤ)*marked.card := by
  by_cases hn : l.Nodup
  · have hm := marks_le marked hn
    dsimp [weight]
    have hi : (marks marked l : ℤ) ≤ (marked.card : ℤ) := by exact_mod_cast hm
    have ht := mul_le_mul_of_nonneg_left hi (Int.natCast_nonneg unit)
    have hz := mul_nonneg (Int.natCast_nonneg period) (Int.natCast_nonneg (winds wrap l))
    omega
  · obtain ⟨p,e,m,s,hsplit⟩ := repeated hn
    rw [hsplit] at hw ⊢
    obtain ⟨hloop,hr⟩ := erase_repeat hw
    have h₁ := hc _ _ hloop
    have h₂ := walk_bound marked wrap unit period hc hr
    simp only [weight_append] at h₂ ⊢
    omega
termination_by l.length
decreasing_by all_goals (simp_all; omega)

/-- Compress real difference constraints whenever the indicated rational predecessor
controls the totals of a walk with distinct edge labels. No finiteness of V is needed. -/
theorem integerPotentials (src dst : E → V) (marked : Finset E) (wrap : E → ℕ)
    (unit period : ℕ) (T : ℝ) (x : V → ℝ)
    (h : ∀ e, (if e ∈ marked then (1:ℝ) else 0) - (wrap e : ℝ)*T ≤ x (dst e)-x (src e))
    (rounding : ∀ A B : ℕ, A ≤ marked.card → (A : ℝ) ≤ (B : ℝ)*T →
      (unit : ℤ)*A - (period : ℤ)*B ≤ 0) :
    ∃ z : V → ℤ, ∀ e, (if e ∈ marked then (unit:ℤ) else 0) - (period:ℤ)*wrap e ≤
      z (dst e) - z (src e) := by
  let W := weight marked wrap unit period
  let ways (v : V) : Set ℤ := {a | ∃ u l, Walk src dst u v l ∧ W l = a}
  have nonempty (v : V) : (ways v).Nonempty := ⟨0,v,[],rfl,by simp [W,weight,marks,winds]⟩
  have limit (v : V) : BddAbove (ways v) := by
    refine ⟨(unit:ℤ)*marked.card,?_⟩
    rintro _ ⟨u,l,hw,rfl⟩
    exact walk_bound marked wrap unit period
      (fun _ _ hp => nonpos_closed marked wrap unit period T x h rounding hp) hw
  refine ⟨fun v => sSup (ways v),?_⟩
  intro e
  obtain ⟨u,l,hw,hval⟩ := Int.csSup_mem (nonempty (src e)) (limit (src e))
  have hlast : Walk src dst (src e) (dst e) [e] := ⟨rfl,rfl⟩
  have reach : W (l ++ [e]) ∈ ways (dst e) :=
    ⟨u,l ++ [e],walk_append.mpr ⟨src e,hw,hlast⟩,rfl⟩
  have hb := le_csSup (limit (dst e)) reach
  change W l = _ at hval
  rw [show W (l++[e]) = W l + W [e] from weight_append ..,hval] at hb
  by_cases hm : e ∈ marked <;> simp [W,weight,marks,winds,hm] at hb ⊢ <;> omega

private theorem strict_counts {A B : ℕ} {T : ℝ} (hT : T < 9/2)
    (hr : (A : ℝ) ≤ (B : ℝ)*T) (hb : 0 < B) : 2*A < 9*B := by
  have hb' : (0:ℝ) < B := by exact_mod_cast hb
  have ht := mul_lt_mul_of_pos_left hT hb'
  have hi : (2:ℝ)*A < 9*B := by linarith
  exact_mod_cast hi

theorem potentials22 (src dst : E → V) (marked : Finset E) (wrap : E → ℕ)
    (T : ℝ) (x : V → ℝ) (hm : marked.card ≤ 30) (hT : T < 9/2)
    (h : ∀ e, (if e ∈ marked then (1:ℝ) else 0) - (wrap e : ℝ)*T ≤ x (dst e)-x (src e)) :
    ∃ z : V → ℤ, ∀ e, (if e ∈ marked then (5:ℤ) else 0) - 22*(wrap e : ℤ) ≤
      z (dst e)-z (src e) := by
  apply integerPotentials src dst marked wrap 5 22 T x h
  intro A B ha hr
  by_cases hb : B = 0
  · subst B
    simp at hr
    simp [hr]
  · have hi := strict_counts hT hr (Nat.pos_of_ne_zero hb)
    omega

theorem potentials4 (src dst : E → V) (marked : Finset E) (wrap : E → ℕ)
    (T : ℝ) (x : V → ℝ) (hm : marked.card ≤ 12) (hT : T < 9/2)
    (h : ∀ e, (if e ∈ marked then (1:ℝ) else 0) - (wrap e : ℝ)*T ≤ x (dst e)-x (src e)) :
    ∃ z : V → ℤ, ∀ e, (if e ∈ marked then (1:ℤ) else 0) - 4*(wrap e : ℤ) ≤
      z (dst e)-z (src e) := by
  apply integerPotentials src dst marked wrap 1 4 T x h
  intro A B ha hr
  by_cases hb : B = 0
  · subst B
    simp at hr
    simp [hr]
  · have hi := strict_counts hT hr (Nat.pos_of_ne_zero hb)
    omega

section Bearings

variable {I : Type*} [Fintype I]

/-- From interval coordinates and only the marked arcs, produce monotone integer
positions. The two interval endpoints may coincide after projective identification. -/
theorem bearingPositions (src dst : I → V) (wrap : I → ℕ) (unit period : ℕ)
    (T : ℝ) (x : V → ℝ) (hT₀ : 0 ≤ T) (hx : ∀ v, 0 ≤ x v ∧ x v ≤ T)
    (h : ∀ i, 1 - (wrap i : ℝ)*T ≤ x (dst i) - x (src i))
    (rounding : ∀ A B : ℕ, A ≤ Fintype.card I → (A : ℝ) ≤ (B : ℝ)*T →
      (unit : ℤ)*A - (period : ℤ)*B ≤ 0) :
    ∃ z : V → ℤ, (∀ v, 0 ≤ z v ∧ z v ≤ period) ∧
      (∀ u v, x u ≤ x v → z u ≤ z v) ∧
      (∀ i, (unit : ℤ) - (period : ℤ)*wrap i ≤ z (dst i) - z (src i)) := by
  classical
  let X : Option V → ℝ
    | none => 0
    | some v => x v
  have range (a : Option V) : 0 ≤ X a ∧ X a ≤ T := by
    cases a with
    | none => exact ⟨le_rfl,hT₀⟩
    | some v => exact hx v
  let Arc := I ⊕ (Option V × Option V)
  let tag : I ↪ Arc := ⟨Sum.inl, fun _ _ h => Sum.inl.inj h⟩
  let marked : Finset Arc := Finset.univ.map tag
  let S : Arc → Option V := Sum.elim (fun i => some (src i)) Prod.fst
  let D : Arc → Option V := Sum.elim (fun i => some (dst i)) Prod.snd
  let B : Arc → ℕ := Sum.elim wrap (fun ab => if X ab.1 ≤ X ab.2 then 0 else 1)
  have includes (i : I) : Sum.inl i ∈ marked := Finset.mem_map.mpr ⟨i,Finset.mem_univ _,rfl⟩
  have excludes (ab : Option V × Option V) : Sum.inr ab ∉ marked := by
    rintro ha
    obtain ⟨i,_,hi⟩ := Finset.mem_map.mp ha
    change Sum.inl i = Sum.inr ab at hi
    cases hi
  have legal (e : Arc) : (if e ∈ marked then (1:ℝ) else 0) - (B e : ℝ)*T ≤
      X (D e) - X (S e) := by
    cases e with
    | inl i => simpa [includes,S,D,B,X] using h i
    | inr ab =>
      obtain ⟨a,b⟩ := ab
      have ha := range a
      have hb := range b
      by_cases hab : X a ≤ X b
      all_goals simp [excludes,S,D,B,hab]
      all_goals linarith
  obtain ⟨y,hy⟩ := integerPotentials S D marked B unit period T X legal
    (fun A n ha hb => rounding A n (by simpa [marked] using ha) hb)
  have mono (a b : Option V) (hab : X a ≤ X b) : y a ≤ y b := by
    have hstep := hy (.inr (a,b))
    simp [excludes,S,D,B,hab] at hstep
    omega
  refine ⟨fun v => y (some v) - y none,?_,?_,?_⟩
  · intro v
    dsimp only
    have hlow := mono none (some v) (hx v).1
    have htop := hy (.inr (some v,none))
    by_cases hab : X (some v) ≤ X none <;> simp [excludes,S,D,B,hab] at htop <;> omega
  · intro u v huv
    dsimp only
    have hstep := mono (some u) (some v) huv
    omega
  · intro i
    dsimp only
    have hstep := hy (.inl i)
    simp [includes,S,D,B] at hstep
    omega

theorem bearings22 (src dst : I → V) (wrap : I → ℕ) (T : ℝ) (x : V → ℝ)
    (hm : Fintype.card I ≤ 30) (hT₀ : 0 ≤ T) (hT : T < 9/2)
    (hx : ∀ v, 0 ≤ x v ∧ x v ≤ T)
    (h : ∀ i, 1 - (wrap i : ℝ)*T ≤ x (dst i) - x (src i)) :
    ∃ z : V → ℤ, (∀ v, 0 ≤ z v ∧ z v ≤ 22) ∧
      (∀ u v, x u ≤ x v → z u ≤ z v) ∧
      (∀ i, 5 - 22*(wrap i : ℤ) ≤ z (dst i) - z (src i)) := by
  apply bearingPositions src dst wrap 5 22 T x hT₀ hx h
  intro A B ha hr
  by_cases hb : B = 0
  · subst B
    simp at hr
    simp [hr]
  · have hi := strict_counts hT hr (Nat.pos_of_ne_zero hb)
    omega

theorem bearings4 (src dst : I → V) (wrap : I → ℕ) (T : ℝ) (x : V → ℝ)
    (hm : Fintype.card I ≤ 12) (hT₀ : 0 ≤ T) (hT : T < 9/2)
    (hx : ∀ v, 0 ≤ x v ∧ x v ≤ T)
    (h : ∀ i, 1 - (wrap i : ℝ)*T ≤ x (dst i) - x (src i)) :
    ∃ z : V → ℤ, (∀ v, 0 ≤ z v ∧ z v ≤ 4) ∧
      (∀ u v, x u ≤ x v → z u ≤ z v) ∧
      (∀ i, 1 - 4*(wrap i : ℤ) ≤ z (dst i) - z (src i)) := by
  apply bearingPositions src dst wrap 1 4 T x hT₀ hx h
  intro A B ha hr
  by_cases hb : B = 0
  · subst B
    simp at hr
    simp [hr]
  · have hi := strict_counts hT hr (Nat.pos_of_ne_zero hb)
    omega

end Bearings

#print axioms bearings22
#print axioms bearings4

#print axioms potentials22
#print axioms potentials4
end R37.DirectionCompression
