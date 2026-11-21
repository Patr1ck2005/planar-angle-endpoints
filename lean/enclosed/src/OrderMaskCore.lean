import OrderOrbit
import FiveBoardModel

namespace R67.OrderOrbit

def Sym.gapSlot (w : Sym) (j : E) : E := if w.rev then w.t-j-1 else w.t+j
def Sym.gapNat (w : Sym) (j : ℕ) : ℕ := (w.gapSlot (Fin.ofNat 10 j)).val
def actualWord (o : E→E) : R67.Five.Word := List.ofFn fun j=>(o j).val
def rows (word : R67.Five.Word) (v : V) := (List.range 4).map (R67.Five.rowArc word v.val)
def family (arcs : List (List ℕ)) : Multiset (Multiset ℕ) := ((Quot.mk _ (arcs.map (fun ar=>(Quot.mk _ ar : Multiset ℕ)))) : Multiset (Multiset ℕ))
private def ins {α : Type} (le : α→α→Bool) (x : α) : List α→List α
  | [] => [x]
  | y::ys => if le x y then x::y::ys else y::ins le x ys

private def sort {α : Type} (le : α→α→Bool) : List α→List α
  | [] => []
  | x::xs => ins le x (sort le xs)

private theorem ins_perm {α : Type} (le : α→α→Bool) (x : α) (ys : List α) :
    (ins le x ys).Perm (x::ys) := by
  induction ys with
  | nil => rfl
  | cons y ys ih =>
    unfold ins
    split
    · rfl
    · exact (ih.cons y).trans (List.Perm.swap x y ys)

private theorem sort_perm {α : Type} (le : α→α→Bool) (xs : List α) : (sort le xs).Perm xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact (ins_perm le x _).trans (ih.cons x)

private def numLE (a b : ℕ) : Bool := decide (a≤b)
private def listLE : List ℕ→List ℕ→Bool
  | [],_ => true
  | _::_,[] => false
  | x::xs,y::ys => if x==y then listLE xs ys else numLE x y

def normal (arcs : List (List ℕ)) : List (List ℕ) := sort listLE (arcs.map (sort numLE))

private theorem normal_preserves (arcs : List (List ℕ)) : family (normal arcs)=family arcs := by
  unfold family normal
  apply Quot.sound
  change List.Perm ((sort listLE (arcs.map (sort numLE))).map (fun ar=>(Quot.mk _ ar : Multiset ℕ))) (arcs.map (fun ar=>(Quot.mk _ ar : Multiset ℕ)))
  apply List.Perm.trans (List.Perm.map (fun ar : List ℕ=>(Quot.mk _ ar : Multiset ℕ)) (sort_perm listLE _))
  rw [List.map_map]
  have same (ar : List ℕ) : (Quot.mk _ (sort numLE ar) : Multiset ℕ) = Quot.mk _ ar :=
    Quot.sound (sort_perm numLE _)
  simp only [Function.comp_def,same]
  exact List.Perm.refl _

private theorem normal_sound {a b : List (List ℕ)} (eq : normal a=normal b) :
    family a=family b := by rw [←normal_preserves a,eq,normal_preserves]

def MaskLaw (w : Sym) (word : R67.Five.Word) : Prop :=
  family ((R67.Five.triComplements word).map (List.map w.gapNat)) =
    family (R67.Five.triComplements (representativeWord w.r)) ∧
  ∀v : V, family ((rows word (labels w.p v)).map (List.map w.gapNat)) =
    family (rows (representativeWord w.r) v)

def maskTest (w : Sym) : Bool :=
  let word:=actualWord w.image
  let rep:=representativeWord w.r
  let trans (arcs : List (List ℕ)) := normal (arcs.map (List.map w.gapNat))
  (trans (R67.Five.triComplements word) == normal (R67.Five.triComplements rep)) &&
    (List.finRange 5).all (fun v=>trans (rows word (labels w.p v)) == normal (rows rep v))

theorem maskTest_sound (w : Sym) (h : maskTest w=true) : MaskLaw w (actualWord w.image) := by
  simp only [maskTest,Bool.and_eq_true,beq_iff_eq,List.all_eq_true] at h
  exact ⟨normal_sound h.1,fun v=>normal_sound (h.2 v (by simp))⟩

theorem gap_bijective (t : E) (rev : Bool) :
    Function.Bijective (fun j : E=>if rev then t-j-1 else t+j) := by
  revert t rev
  decide +kernel

end R67.OrderOrbit
#print axioms R67.OrderOrbit.maskTest_sound

