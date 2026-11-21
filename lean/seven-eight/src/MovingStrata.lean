import MarkedRows
import TwistedCapacity
import Mathlib.Tactic

noncomputable section
namespace R41.MovingStrata
open R37.Seventeen R37.SignedFan

/-- The last gap ends at the first bin in the next period. Bin m can occur
as the unwrapped bin of an original bearing, and decodes by antipodality. -/
def stop (F : Row) (m : ℕ) (c : ℕ → ℕ) (i : ℕ) :=
  if i<F.n then c (i+1) else c 0+m

def Good (F : Row) (m : ℕ) (c raw : ℕ → ℕ) :=
  ∀ i ∈ localMarks F, c i≤raw i ∧ raw i<stop F m c i

private theorem casesMark {F : Row} {i : ℕ} (h : i∈localMarks F) :
    (i<F.n ∧ F.step i=1) ∨ (i=F.n ∧ F.seam=1) := by
  by_cases e : F.seam=1 <;> simp [localMarks,e] at h <;> grind

private theorem memMark {F : Row} {i : ℕ} (hi : i<F.n) (sw : F.step i=1) : i∈localMarks F := by
  by_cases e : F.seam=1 <;> simp [localMarks,e,hi,sw]

private theorem rawspan {F : Row} {m : ℕ} {c raw : ℕ → ℕ}
    (mono : Monotone c) (bound : ∀ i, c i≤m) (g : Good F m c raw)
    {i : ℕ} (h : i∈localMarks F) : c 0≤raw i ∧ raw i<c 0+m := by
  have hi := g i h
  refine ⟨(mono (Nat.zero_le i)).trans hi.1,?_⟩
  rcases casesMark h with h|⟨rfl,_⟩
  · simp [stop,h.1] at hi
    have := bound (i+1)
    omega
  · simpa [stop] using hi.2

private theorem mod_inj {m a x y : ℕ} (mp : 0<m) (ab : a≤m)
    (hx : a≤x ∧ x<a+m) (hy : a≤y ∧ y<a+m) (eq : x%m=y%m) : x=y := by
  have modrep (v : ℕ) (hv : v<2*m) : v%m=if v<m then v else v-m := by
    split_ifs with h
    · exact Nat.mod_eq_of_lt h
    · rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)]
  rw [modrep x (by omega),modrep y (by omega)] at eq
  split_ifs at eq <;> omega

private theorem gap_owner {F : Row} {m : ℕ} {c r t : ℕ → ℕ}
    (mp : 0<m) (mono : Monotone c) (bound : ∀ i, c i≤m)
    (gr : Good F m c r) (gt : Good F m c t) {i j : ℕ}
    (hi : i∈localMarks F) (hj : j∈localMarks F) (eq : r i%m=t j%m) : i=j := by
  have eq' := mod_inj mp (bound 0) (rawspan mono bound gr hi) (rawspan mono bound gt hj) eq
  have neq {a b : ℕ} {f g : ℕ → ℕ} (ab : a<b) (aa : a∈localMarks F) (bb : b∈localMarks F)
      (gf : Good F m c f) (gg : Good F m c g) : f a<g b := by
    have an : a<F.n := by rcases casesMark bb with h|h <;> omega
    have low := (gf a aa).2
    rw [stop,if_pos an] at low
    exact lt_of_lt_of_le low ((mono (by omega)).trans (gg b bb).1)
  rcases lt_trichotomy i j with h|h|h
  · exact False.elim ((ne_of_lt (neq h hi hj gr gt)) eq')
  · exact h
  · exact False.elim ((ne_of_lt (neq h hj hi gt gr)) eq'.symm)

def marked (F : Row) {m : ℕ} (mp : 0<m) (raw : ℕ → ℕ) : Finset (Fin m) :=
  (localMarks F).image (fun i => ⟨raw i%m,Nat.mod_lt _ mp⟩)

theorem different_choices {F : Row} {m : ℕ} {c r t : ℕ → ℕ}
    (mp : 0<m) (mono : Monotone c) (bound : ∀ i, c i≤m)
    (gr : Good F m c r) (gt : Good F m c t) {j : ℕ} (hj : j∈localMarks F)
    (ne : r j≠t j) : marked F mp r≠marked F mp t := by
  intro e
  have mem : (⟨r j%m,Nat.mod_lt _ mp⟩ : Fin m)∈marked F mp t :=
    e ▸ Finset.mem_image_of_mem _ hj
  obtain ⟨i,hi,eq⟩ := Finset.mem_image.mp mem
  have eq' : t i%m=r j%m := congrArg Fin.val eq
  obtain rfl := gap_owner mp mono bound gt gr hi hj eq'
  exact ne (mod_inj mp (bound 0) (rawspan mono bound gt hi) (rawspan mono bound gr hj) eq').symm

private def bits {m : ℕ} (B : Finset (Fin m)) (j : ℕ) := B.filter (fun i => i.val<j)
def read {m : ℕ} (initial : Bool) (B : Finset (Fin m)) (j : ℕ) : Bool :=
  if (bits B j).card%2=1 then !initial else initial

private theorem toggle (b x y : Bool) (p : ℕ) (h : (if p%2=1 then !b else b)=x) (ne : x≠y) :
    (if (p+1)%2=1 then !b else b)=y := by
  by_cases odd : p%2=1
  · have eo : (p+1)%2≠1 := by omega
    cases b <;> cases x <;> cases y <;> simp_all
  · have eo : (p+1)%2=1 := by omega
    cases b <;> cases x <;> cases y <;> simp_all

theorem encode (F : Row) {m : ℕ} (mp : 0<m) (c raw : ℕ → ℕ) (mono : Monotone c)
    (bound : ∀ i, c i≤m) (good : Good F m c raw) :
    (marked F mp raw).card=F.switches ∧
    ∃ initial : Bool, ∀ j, j≤F.n → read initial (marked F mp raw) (c j)=F.b j := by
  classical
  let f (i : ℕ) : Fin m := ⟨raw i%m,Nat.mod_lt _ mp⟩
  have inj : Set.InjOn f (localMarks F) := fun _ hi _ hj eq =>
    gap_owner mp mono bound good good hi hj (congrArg Fin.val eq)
  have card : (marked F mp raw).card=F.switches :=
    (Finset.card_image_of_injOn inj).trans (card_localMarks F)
  refine ⟨card,?_⟩
  let A := marked F mp raw
  let initial := if (bits A (c 0)).card%2=1 then !(F.b 0) else F.b 0
  refine ⟨initial,?_⟩
  have base : read initial A (c 0)=F.b 0 := by simp [read,initial]; split <;> simp_all
  have diff (i : ℕ) (hi : i<F.n) :
      bits A (c (i+1))=if F.step i=1 then insert (f i) (bits A (c i)) else bits A (c i) := by
    have order := mono (Nat.le_succ i)
    have interior {j : ℕ} (hj : j∈localMarks F) :
        (c i≤(f j).val ∧ (f j).val<c (i+1)) ↔ i=j := by
      have sp := rawspan mono bound good hj
      have gs := good j hj
      have b₁ := bound (i+1)
      have b₂ := bound 0
      have c₀ := mono (Nat.zero_le i)
      change (c i≤raw j%m ∧ raw j%m<c (i+1)) ↔ i=j
      by_cases low : raw j<m
      · rw [Nat.mod_eq_of_lt low]
        constructor
        · intro hh
          rcases lt_trichotomy i j with q|q|q
          · have := mono (show i+1 ≤ j by omega); omega
          · exact q
          · have jn : j<F.n := by omega
            simp [stop,jn] at gs
            have := mono (show j+1 ≤ i by omega); omega
        · rintro rfl
          simpa [stop,hi] using gs
      · have rem : raw j%m=raw j-m := by rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)]
        rw [rem]
        constructor
        · omega
        · rintro rfl
          simp [stop,hi] at gs
          omega
    ext t
    by_cases sw : F.step i=1
    · have mk := memMark hi sw
      have sharp := (interior mk).mpr rfl
      have present : f i∈A := Finset.mem_image_of_mem _ mk
      simp only [sw,if_true,bits,Finset.mem_filter,Finset.mem_insert]
      constructor
      · rintro ⟨mem,lt⟩
        by_cases h : t.val<c i
        · exact Or.inr ⟨mem,h⟩
        · obtain ⟨j,hj,e⟩ := Finset.mem_image.mp mem
          have eq := (interior hj).mp (show c i≤(f j).val ∧ (f j).val<c (i+1) by rw [show f j=t from e]; omega)
          subst j
          exact Or.inl e.symm
      · rintro (rfl|⟨mem,lt⟩)
        · exact ⟨present,sharp.2⟩
        · exact ⟨mem,lt_of_lt_of_le lt order⟩
    · simp only [sw,if_false,bits,Finset.mem_filter]
      constructor
      · rintro ⟨mem,lt⟩
        refine ⟨mem,?_⟩
        by_contra! high
        obtain ⟨j,hj,e⟩ := Finset.mem_image.mp mem
        have eq := (interior hj).mp (show c i≤(f j).val ∧ (f j).val<c (i+1) by rw [show f j=t from e]; omega)
        subst j
        rcases casesMark hj with h|h <;> omega
      · exact fun h => ⟨h.1,lt_of_lt_of_le h.2 order⟩
  intro j hj
  induction j with
  | zero => exact base
  | succ j ih =>
    have jn : j<F.n := by omega
    have old := ih (by omega)
    change read initial A (c (j+1))=_
    unfold read at old ⊢
    rw [diff j jn]
    by_cases sw : F.step j=1
    · rw [if_pos sw]
      have g := good j (memMark jn sw)
      simp [stop,jn] at g
      have rawlt : raw j<m := lt_of_lt_of_le g.2 (bound _)
      have miss : f j∉bits A (c j) := by
        intro hh
        have low := (Finset.mem_filter.mp hh).2
        change raw j%m<c j at low
        rw [Nat.mod_eq_of_lt rawlt] at low
        omega
      rw [Finset.card_insert_of_notMem miss]
      have ne : F.b j≠F.b (j+1) := by simpa [Row.step] using sw
      exact toggle initial _ _ _ old ne
    · rw [if_neg sw]
      have eq : F.b j=F.b (j+1) := by simpa [Row.step] using sw
      simpa [eq] using old

end R41.MovingStrata
#print axioms R41.MovingStrata.encode
#print axioms R41.MovingStrata.different_choices
