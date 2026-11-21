import TwoAnchorGeometry

/-! Finite rotational averaging, with closed arcs and with both possible
pieces of an arc crossing the phase cut. All arguments use finite sums. -/
namespace RotatingBins
open scoped BigOperators

noncomputable def overlap (a b l r : ℝ) := max 0 (min b r - max a l)

private theorem overlap_add {a c b l r : ℝ} (ha : a≤c) (hb : c≤b) :
    overlap a c l r + overlap c b l r = overlap a b l r := by
  simp only [overlap, min_def, max_def]
  split_ifs <;> linarith

/-- If every interior phase is covered at least B times by closed
line intervals, their total clipped length is at least B times the
phase-domain length. Isolated endpoint coincidences contribute zero. -/
theorem coverage {G : Type*} [Fintype G] (l r : G → ℝ) {a b B : ℝ}
    (hab : a≤b)
    (hcover : ∀ t, a<t → t<b → B ≤ ∑ g, (if l g ≤ t ∧ t ≤ r g then (1:ℝ) else 0)) :
    B*(b-a) ≤ ∑ g, overlap a b (l g) (r g) := by
  classical
  let cuts := (Finset.univ.image l) ∪ (Finset.univ.image r)
  suffices h : ∀ (s : Finset ℝ) (x y : ℝ), a≤x → y≤b → x≤y →
      (∀ z ∈ cuts, x<z → z<y → z∈s) →
      B*(y-x) ≤ ∑ g, overlap x y (l g) (r g) by
    exact h cuts a b le_rfl le_rfl hab (fun _ hz _ _ => hz)
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro x y hx hy hxy hcuts
    rcases eq_or_lt_of_le hxy with h | h
    · subst y
      simp only [sub_self,mul_zero]
      exact Finset.sum_nonneg (fun i _ => le_max_left _ _)
    · let t := (x+y)/2
      have hxt : x<t := by dsimp [t]; linarith
      have hty : t<y := by dsimp [t]; linarith
      have hc := mul_le_mul_of_nonneg_right (hcover t (by linarith) (by linarith)) (sub_nonneg.mpr h.le)
      rw [Finset.sum_mul] at hc
      refine hc.trans (Finset.sum_le_sum (fun g _ => ?_))
      split_ifs with hg
      · have lx : l g ≤ x := by
          by_contra! h'
          exact Finset.notMem_empty _ (hcuts _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ g))) h' (hg.1.trans_lt hty))
        have yr : y ≤ r g := by
          by_contra! h'
          exact Finset.notMem_empty _ (hcuts _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ g))) (hxt.trans_le hg.2) h')
        simp [overlap,min_eq_left yr,max_eq_left lx,sub_nonneg.mpr h.le]
      · simpa only [zero_mul,overlap] using (le_max_left 0 (min y (r g)-max x (l g)))
  | insert c s _ ih =>
    intro x y hx hy hxy hcuts
    by_cases h : x<c ∧ c<y
    · have hleft := ih x c hx (by linarith [h.2]) h.1.le (by
        intro z hz hxz hzc
        exact (Finset.mem_insert.mp (hcuts z hz hxz (hzc.trans h.2))).resolve_left hzc.ne)
      have hright := ih c y (by linarith [h.1]) hy h.2.le (by
        intro z hz hcz hzy
        exact (Finset.mem_insert.mp (hcuts z hz (h.1.trans hcz) hzy)).resolve_left hcz.ne')
      have hadd : (∑ g, overlap x c (l g) (r g)) + (∑ g, overlap c y (l g) (r g)) =
          ∑ g, overlap x y (l g) (r g) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun g _ => overlap_add h.1.le h.2.le)
      linarith [show B*(y-x)=B*(c-x)+B*(y-c) by ring]
    · apply ih x y hx hy hxy
      intro z hz hxz hzy
      exact (Finset.mem_insert.mp (hcuts z hz hxz hzy)).resolve_left (fun he => h (he ▸ ⟨hxz,hzy⟩))

/-- Closed majorant for the offsets covered by a single witness gap. -/
def Active (W s d t : ℝ) : Prop :=
  (s ≤ t ∧ t ≤ s+d) ∨ (s-W ≤ t ∧ t ≤ s+d-W)

private theorem clipped_arc {W s d : ℝ} (hw : 0<W) (hs : 0≤s ∧ s≤W) (hd : 0≤d ∧ d≤W) :
    overlap 0 W s (s+d) + overlap 0 W (s-W) (s+d-W) = d := by
  simp only [overlap,min_def,max_def]
  split_ifs <;> linarith [hs.1,hs.2,hd.1,hd.2]

/-- Sharp circular multi-cover inequality for genuine arcs with starts
in [0,W], obtained by explicitly splitting an arc across the seam. -/
theorem arc_coverage {G : Type*} [Fintype G] (s d : G → ℝ) {W B : ℝ} (hw : 0<W)
    (hs : ∀ g, 0≤s g ∧ s g≤W) (hd : ∀ g, 0≤d g ∧ d g≤W)
    (hcover : ∀ t, 0<t → t<W →
      B ≤ ∑ g, (if (s g ≤ t ∧ t ≤ s g+d g) ∨ (s g-W ≤ t ∧ t ≤ s g+d g-W) then (1:ℝ) else 0)) :
    B*W ≤ ∑ g, d g := by
  classical
  let l (e : Bool × G) := if e.1 then s e.2 else s e.2-W
  let r (e : Bool × G) := if e.1 then s e.2+d e.2 else s e.2+d e.2-W
  have h := coverage l r (B:=B) (a:=0) (b:=W) hw.le (by
    intro t ht ht'
    refine (hcover t ht ht').trans ?_
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool,l,r,Bool.false_eq_true,↓reduceIte]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro g _
    split_ifs <;> norm_num
    tauto)
  rw [Fintype.sum_prod_type] at h
  simp only [Fintype.sum_bool,l,r,Bool.false_eq_true,↓reduceIte,sub_zero] at h
  refine h.trans_eq ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun g _ => clipped_arc hw (hs g) (hd g))

#print axioms arc_coverage
/-- At a fixed phase, delete the vertices owning an active witness.
The surviving vertices have distinct n-bit incidence codes. A witness
must be owned by the meeting vertex of the conflicting pair of edges. -/
theorem phase_count {V G : Type*} [Fintype V] [Fintype G] {n : ℕ}
    (R : V → V → Prop) (bin : V → V → Fin n) (owner : G → V) (witness : G → Prop)
    [DecidablePred witness]
    (complete : ∀ i j, i ≠ j → R i j ∨ R j i)
    (conflict : ∀ i j k, R i j → R j k → bin i j = bin j k →
      ∃ g, owner g = j ∧ witness g) :
    Fintype.card V ≤ 2^n + (Finset.univ.filter witness).card := by
  classical
  let bad (v : V) := ∃ g, owner g = v ∧ witness g
  let bits (v : V) (b : Fin n) : Bool := decide (∃ u, R u v ∧ bin u v = b)
  have separates {v w : V} (hvw : R v w) (hv : ¬bad v) : bits v ≠ bits w := by
    intro e
    have h : bits w (bin v w) = true := decide_eq_true ⟨v,hvw,rfl⟩
    rw [←e] at h
    obtain ⟨u,hu,he⟩ := of_decide_eq_true h
    exact hv (conflict u v w hu hvw he)
  let select (v : V) : (Fin n → Bool) ⊕ {g : G // witness g} :=
    if h : bad v then Sum.inr ⟨h.choose,h.choose_spec.2⟩ else Sum.inl (bits v)
  have hinj : Function.Injective select := by
    intro v w eq
    by_cases hv : bad v <;> by_cases hw : bad w
    · have he : hv.choose = hw.choose := by
        simpa [select,hv,hw,Subtype.ext_iff] using eq
      exact hv.choose_spec.1.symm.trans ((congrArg owner he).trans hw.choose_spec.1)
    · simp [select,hv,hw] at eq
    · simp [select,hv,hw] at eq
    · have he : bits v = bits w := by simpa [select,hv,hw] using eq
      by_contra hn
      rcases complete v w hn with h | h
      · exact separates h hv he
      · exact separates h hw he.symm
  simpa [Fintype.card_subtype] using Fintype.card_le_of_injective select hinj

/-- Rotating-bin inequality obtained from the two local geometric
interfaces: every pair is oriented, and a same-bin directed turn
has an owner-matched active gap. The binary encoding, masked
cardinality, circular seam and averaging are proved internally. -/
theorem rotating_bound {V G : Type*} [Fintype V] [Fintype G] {n : ℕ}
    (R : ℝ → V → V → Prop) (bin : ℝ → V → V → Fin n)
    (owner : G → V) (s d : G → ℝ) {W lam : ℝ}
    (hw : 0<W) (hs : ∀ g, 0≤s g ∧ s g≤W) (hd : ∀ g, 0≤d g ∧ d g≤W)
    (hlen : ∀ g, d g ≤ W-lam)
    (complete : ∀ t, 0<t → t<W → ∀ i j, i ≠ j → R t i j ∨ R t j i)
    (conflict : ∀ t, 0<t → t<W → ∀ i j k, R t i j → R t j k → bin t i j = bin t j k →
      ∃ g, owner g = j ∧ Active W (s g) (d g) t) :
    ((Fintype.card V : ℝ) - (2:ℝ)^n)*W ≤ (Fintype.card G : ℝ)*(W-lam) := by
  classical
  have hphase (t : ℝ) (ht : 0<t) (ht' : t<W) := phase_count (R t) (bin t) owner
    (fun g => Active W (s g) (d g) t) (complete t ht ht') (conflict t ht ht')
  apply (arc_coverage s d hw hs hd ?_).trans
  · simpa [mul_sub] using (Finset.sum_le_sum (s:=Finset.univ) (fun g _ => hlen g))
  · intro t ht ht'
    have h : (Fintype.card V : ℝ) ≤ (2:ℝ)^n +
        ((Finset.univ.filter (fun g => Active W (s g) (d g) t)).card : ℝ) := by
      exact_mod_cast hphase t ht ht'
    have hi : ((Finset.univ.filter (fun g => Active W (s g) (d g) t)).card : ℝ) =
        ∑ g, (if (s g ≤ t ∧ t ≤ s g+d g) ∨ (s g-W ≤ t ∧ t ≤ s g+d g-W) then (1:ℝ) else 0) := by
      simp [Active,Finset.sum_boole]
    linarith

#print axioms phase_count
#print axioms rotating_bound

end RotatingBins
