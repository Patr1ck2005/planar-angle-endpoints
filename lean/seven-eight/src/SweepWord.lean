import MovingStrata
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Logic.Equiv.Fin.Rotate

noncomputable section
namespace R41.SweepWord
open R37.Seventeen R37.SignedFan R41.MovingStrata

abbrev Layer (m s : ℕ) := {B : Finset (Fin m) // B.card=s}
abbrev Word (m s : ℕ) := Layer m s × Bool

def last (m : ℕ) (hm : 0<m) : Fin m := ⟨m-1,by omega⟩

def turnLayer (m s : ℕ) : Equiv.Perm (Layer m s) where
  toFun b := ⟨b.val.map (finRotate m).toEmbedding,by simpa using b.property⟩
  invFun b := ⟨b.val.map (finRotate m).symm.toEmbedding,by simpa using b.property⟩
  left_inv b := by apply Subtype.ext; simp [Finset.map_map]
  right_inv b := by apply Subtype.ext; simp [Finset.map_map]

def flip {m s : ℕ} (hm : 0<m) (b : Layer m s) : Equiv.Perm Bool :=
  if last m hm∈b.val then Equiv.swap false true else 1

def rotate (m s : ℕ) (hm : 0<m) : Equiv.Perm (Word m s) :=
  (Equiv.prodCongrRight (flip hm)).trans (Equiv.prodCongrLeft (fun _ : Bool => turnLayer m s))

theorem act {m s : ℕ} (hm : 0<m) (b : Layer m s) (x : Bool) :
    rotate m s hm (b,x)=(turnLayer m s b,if last m hm∈b.val then !x else x) := by
  change (_,(flip hm b) x)=_
  by_cases h : last m hm∈b.val <;> cases x <;> simp [flip,h]

private theorem subset_count {m s : ℕ} (hm : 0<m) (hs : 0<s) :
    (Finset.univ.filter (fun b : Layer m s => last m hm∈b.val)).card=(m-1).choose (s-1) := by
  classical
  let x := last m hm
  let A := ((Finset.univ : Finset (Fin m)).powersetCard s).filter (fun b => ({x}:Finset _)⊆b)
  have cnt : A.card=(m-1).choose (s-1) := by
    simpa [A] using Finset.card_filter_powersetCard_subset ({x} : Finset (Fin m)) Finset.univ s
      (Finset.subset_univ _) (by simp; omega)
  let L := Finset.univ.filter (fun b : Layer m s => x∈b.val)
  have eq : L.image Subtype.val=A := by
    ext b
    constructor
    · intro h
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp h
      simp [A,a.property,(Finset.mem_filter.mp ha).2]
    · intro h
      have p : b.card=s ∧ x∈b := by simpa [A] using h
      exact Finset.mem_image.mpr ⟨⟨b,p.1⟩,by simp [L,p.2],rfl⟩
  change L.card=_
  rw [←Finset.card_image_of_injective L Subtype.val_injective,eq,cnt]

theorem sign_rotate {m s : ℕ} (hm : 0<m) (hs : 0<s) :
    Equiv.Perm.sign (rotate m s hm)=(-1)^((m-1).choose (s-1)) := by
  classical
  have sig (b : Layer m s) : Equiv.Perm.sign (flip hm b)=if last m hm∈b.val then -1 else 1 := by
    by_cases h : last m hm∈b.val <;> simp [flip,h,Equiv.Perm.sign_swap]
  change Equiv.Perm.sign (Equiv.prodCongrLeft (fun _ : Bool => turnLayer m s)*
    Equiv.prodCongrRight (flip hm))=_
  rw [map_mul,Equiv.Perm.sign_prodCongrLeft,Equiv.Perm.sign_prodCongrRight]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_bool,Int.units_sq,one_mul,sig]
  rw [←Finset.prod_filter]
  simp [subset_count hm hs]

private def carry (F : Row) (m : ℕ) (r : ℕ → ℕ) :=
  ((localMarks F).filter (fun i => m≤r i)).card

def polarity (F : Row) (m : ℕ) (r : ℕ → ℕ) :=
  if carry F m r%2=1 then !(F.b 0) else F.b 0

private theorem boundsRaw {F : Row} {m : ℕ} {c r : ℕ → ℕ}
    (mono : Monotone c) (bd : ∀ i, c i≤m) (g : Good F m c r) {i : ℕ} (hi : i∈localMarks F) :
    c 0≤r i ∧ r i<c 0+m := by
  have h := g i hi
  refine ⟨(mono (Nat.zero_le _)).trans h.1,?_⟩
  by_cases small : i<F.n
  · simp [stop,small] at h
    have := bd (i+1)
    omega
  · simpa [stop,small] using h.2

/-- A canonical polarity depending only on the integer marks; the same
word can be evaluated using any common grid in which these marks fit. -/
theorem canonical (F : Row) {m : ℕ} (hm : 0<m) (c r : ℕ → ℕ) (mono : Monotone c)
    (bd : ∀ i, c i≤m) (g : Good F m c r) :
    (marked F hm r).card=F.switches ∧ ∀ j, j≤F.n →
      read (polarity F m r) (marked F hm r) (c j)=F.b j := by
  obtain ⟨card,sgn,h⟩ := encode F hm c r mono bd g
  refine ⟨card,?_⟩
  let f (i : ℕ) : Fin m := ⟨r i%m,Nat.mod_lt _ hm⟩
  have inj : Set.InjOn f (localMarks F) := by
    apply Finset.injOn_of_card_image_eq
    exact card.trans (card_localMarks F).symm
  have eq : (marked F hm r).filter (fun i => i.val<c 0)=
      ((localMarks F).filter (fun i => m≤r i)).image f := by
    ext y
    simp only [marked,Finset.mem_filter,Finset.mem_image]
    constructor
    · rintro ⟨⟨i,hi,rfl⟩,lt⟩
      have raw := boundsRaw mono bd g hi
      have big : m≤r i := by
        by_contra! small
        change r i%m<c 0 at lt
        rw [Nat.mod_eq_of_lt small] at lt
        omega
      exact ⟨i,⟨hi,big⟩,rfl⟩
    · rintro ⟨i,⟨hi,big⟩,rfl⟩
      refine ⟨⟨i,hi,rfl⟩,?_⟩
      have raw := boundsRaw mono bd g hi
      have c₀ := bd 0
      change r i%m<c 0
      rw [Nat.mod_eq_sub_mod big,Nat.mod_eq_of_lt (by omega)]
      omega
  have cnt := congrArg Finset.card eq
  rw [Finset.card_image_of_injOn (inj.mono (Finset.filter_subset _ _))] at cnt
  have base := h 0 (Nat.zero_le _)
  change (if ((marked F hm r).filter (fun i => i.val<c 0)).card%2=1 then !sgn else sgn)=F.b 0 at base
  rw [cnt] at base
  have same : polarity F m r=sgn := by
    unfold polarity carry
    split_ifs at base ⊢ with e
    · rw [←base,Bool.not_not]
    · exact base.symm
  simpa only [same] using h

theorem congr_on_marks (F : Row) {m : ℕ} (hm : 0<m) (r t : ℕ → ℕ)
    (eq : ∀ i ∈ localMarks F, r i=t i) :
    marked F hm r=marked F hm t ∧ polarity F m r=polarity F m t := by
  constructor
  · exact Finset.image_congr (fun i hi => Fin.ext (by simp [eq i hi]))
  · have he : (localMarks F).filter (fun i => m≤r i)=(localMarks F).filter (fun i => m≤t i) :=
      Finset.filter_congr (fun i hi => by rw [eq i hi])
    have h' : carry F m r=carry F m t := congrArg Finset.card he
    unfold polarity
    rw [h']

theorem full_turn (F : Row) {m : ℕ} (hm : 0<m) (r t : ℕ → ℕ)
    (small : ∀ i, r i<m) (step : ∀ i ∈ localMarks F, t i=r i+1)
    (sz : (marked F hm r).card=F.switches) :
    marked F hm t=(marked F hm r).map (finRotate m).toEmbedding ∧
    polarity F m t=(if last m hm∈marked F hm r then !(polarity F m r) else polarity F m r) := by
  classical
  letI : NeZero m := ⟨by omega⟩
  let f (i : ℕ) : Fin m := ⟨r i%m,Nat.mod_lt _ hm⟩
  have inj : Set.InjOn f (localMarks F) :=
    Finset.injOn_of_card_image_eq (sz.trans (card_localMarks F).symm)
  have val (i : ℕ) : ((finRotate m (f i)).val)=(r i+1)%m := by
    rw [finRotate_apply,Fin.val_add,Fin.val_one']
    simp [f,Nat.mod_eq_of_lt (small i)]
  constructor
  · ext y
    constructor
    · intro h
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp h
      exact Finset.mem_map.mpr ⟨f i,Finset.mem_image_of_mem _ hi,Fin.ext (by simpa [step i hi] using val i)⟩
    · intro h
      obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp h
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
      exact Finset.mem_image.mpr ⟨i,hi,Fin.ext (by simpa [step i hi] using (val i).symm)⟩
  · have zero : carry F m r=0 := by
      simp only [carry,Finset.card_eq_zero,Finset.filter_eq_empty_iff]
      exact fun i _ => Nat.not_le_of_lt (small i)
    have eq : ((localMarks F).filter (fun i => m≤t i)).image f =
        (marked F hm r).filter (fun a => a=last m hm) := by
      ext a
      constructor
      · intro h
        obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp h
        obtain ⟨hi,big⟩ := Finset.mem_filter.mp hi
        refine Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hi,Fin.ext ?_⟩
        change r i%m=m-1
        rw [Nat.mod_eq_of_lt (small i)]
        rw [step i hi] at big
        have := small i
        omega
      · intro h
        obtain ⟨ha,eq⟩ := Finset.mem_filter.mp h
        obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
        have he := congrArg Fin.val eq
        change r i%m=m-1 at he
        rw [Nat.mod_eq_of_lt (small i)] at he
        exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨hi,by rw [step i hi]; omega⟩,rfl⟩
    have cnt := congrArg Finset.card eq
    rw [Finset.card_image_of_injOn (inj.mono (Finset.filter_subset _ _))] at cnt
    change carry F m t=_ at cnt
    change carry F m t=((marked F hm r).filter (fun a => a=last m hm)).card at cnt
    by_cases present : last m hm∈marked F hm r
    · have only : (marked F hm r).filter (fun a => a=last m hm)={last m hm} := by
        ext a; simp only [Finset.mem_filter,Finset.mem_singleton]; grind
      rw [only,Finset.card_singleton] at cnt
      simp [polarity,zero,cnt,present]
    · have none : (marked F hm r).filter (fun a => a=last m hm)=∅ := by
        ext a; simp only [Finset.mem_filter,Finset.notMem_empty,iff_false]; grind
      rw [none,Finset.card_empty] at cnt
      simp [polarity,zero,cnt,present]

end R41.SweepWord
#print axioms R41.SweepWord.sign_rotate
#print axioms R41.SweepWord.canonical

#print axioms R41.SweepWord.full_turn
