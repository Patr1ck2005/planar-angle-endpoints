import RawBoardMacro
import OrderMaskCore

noncomputable section
namespace R68.Raw
open R67 R67.OrderOrbit

/-- Periodic extension of the ten indexed gaps to the natural-index interface of the checker. -/
def sample (g : E→ℝ) (n : ℕ) := g (Fin.ofNat 10 n)

theorem sample_val (g : E→ℝ) (i : E) : sample g i.val=g i := by
  unfold sample
  exact congrArg g (Fin.ext (Nat.mod_eq_of_lt i.isLt))

private def evalArc (g : ℕ→ℝ) (a : Multiset ℕ) : ℝ := (a.map g).sum
private def tally (g : ℕ→ℝ) (L : Multiset (Multiset ℕ)) : ℕ :=
  (L.map (fun a=>Five.digit (evalArc g a))).sum

private theorem eval_list (g : ℕ→ℝ) (a : List ℕ) : evalArc g (a:Multiset ℕ)=Five.total g a := by
  simp [evalArc,Five.total]

private theorem family_sum (g : ℕ→ℝ) (L : List (List ℕ)) :
    tally g (family L)=(L.map (fun a=>Five.digit (Five.total g a))).sum := by
  change ((↑(L.map (fun a : List ℕ=>(a:Multiset ℕ))) : Multiset (Multiset ℕ)).map
    (fun a=>Five.digit (evalArc g a))).sum=_
  simp [List.map_map,Function.comp_def,eval_list]

private theorem family_contains (L : List (List ℕ)) (a : Multiset ℕ) :
    a∈family L ↔ ∃l∈L,(l:Multiset ℕ)=a := by
  change a∈(↑(L.map (fun l : List ℕ=>(l:Multiset ℕ))) : Multiset (Multiset ℕ)) ↔ _
  simp

private theorem total_map {G H : ℕ→ℝ} {f : ℕ→ℕ} (same : ∀j,H (f j)=G j) (a : List ℕ) :
    Five.total H (a.map f)=Five.total G a := by
  simp only [Five.total,List.map_map,Function.comp_def,same]

private theorem family_pull {G H : ℕ→ℝ} {f : ℕ→ℕ} (same : ∀j,H (f j)=G j)
    (L : List (List ℕ)) : tally H (family (L.map (List.map f)))=tally G (family L) := by
  simp only [family_sum,List.map_map,Function.comp_def,total_map same]

private theorem row_tally (G : ℕ→ℝ) (word : Five.Word) (v : V) :
    tally G (family (rows word v))=
      Five.rowSum (fun i j=>Five.digit (Five.total G (Five.rowArc word i j))) v.val := by
  rw [family_sum]
  unfold rows Five.rowSum
  rw [show List.range 4=[0,1,2,3] by decide]
  simp [add_assoc]

/-- A mask law transports all literal macro lower bounds and exactly preserves each
row's digit sum. The argument only requires a pullback identity for the gap values. -/
theorem mask_scores (w : Sym) (word : Five.Word) (law : MaskLaw w word)
    (G H : ℕ→ℝ) (same : ∀j,H (w.gapNat j)=G j)
    (macroLower : ∀a∈Five.triComplements word,1≤Five.total G a) :
    (∀a∈Five.triComplements (representativeWord w.r),1≤Five.total H a) ∧
      ∀v : V,Five.rowSum (fun i a=>Five.digit (Five.total G (Five.rowArc word i a))) (labels w.p v).val=
        Five.rowSum (fun i a=>Five.digit (Five.total H (Five.rowArc (representativeWord w.r) i a))) v.val := by
  constructor
  · intro a member
    have m:=(family_contains (Five.triComplements (representativeWord w.r)) (a:Multiset ℕ)).mpr ⟨a,member,rfl⟩
    rw [←law.1] at m
    obtain ⟨l,hl,e⟩:=(family_contains _ _).mp m
    obtain ⟨b,hb,rfl⟩:=List.mem_map.mp hl
    have values:=congrArg (evalArc H) e
    rw [eval_list,eval_list,total_map same] at values
    exact (macroLower _ hb).trans_eq values
  · intro v
    rw [←row_tally,←row_tally,←law.2 v,family_pull same]

/-- The bounded Farkas lower bound on the original indexed gap vector. A representative
certificate family suffices. Its distinguished vertex indices are pulled back through
the vertex permutation, independently of the cyclic and reversing gap permutation. -/
theorem orbit_capacity (w : Sym) (word : Five.Word) (law : MaskLaw w word)
    (cert : ∀u h : ℕ,u<5 → (h=5 ∨ h<5 ∧ h≠u) → Five.Proved (representativeWord w.r) u h)
    (u : V) (p : Option V) (apart : p≠some u) (k : ℕ) (hk : k≤30)
    (g : E→ℝ) (box : ∀a,0≤g a ∧ g a≤2)
    (macroLower : ∀a∈Five.triComplements word,1≤Five.total (sample g) a)
    (marks : ∀v : V,v≠u → k+(if p=some v then 1 else 0)≤
      Five.rowSum (fun i a=>Five.digit (Five.total (sample g) (Five.rowArc word i a))) v.val) :
    (k:ℝ)+(if p.isSome then 3 else 5/2)≤Board.total g := by
  let perm : Equiv.Perm E:=Equiv.ofBijective w.gapSlot (gap_bijective w.t w.rev)
  let vert : Equiv.Perm V:=Equiv.ofBijective (labels w.p) (labels_bijective w.p)
  let f : E→ℝ:=g ∘ perm.symm
  have same (j : ℕ) : sample f (w.gapNat j)=sample g j := by
    change sample f (perm (Fin.ofNat 10 j)).val=g _
    rw [sample_val]
    exact congrArg g (perm.symm_apply_apply _)
  obtain ⟨macroRep,eqRows⟩:=mask_scores w word law (sample g) (sample f) same macroLower
  let free:=vert.symm u
  let h : ℕ:=p.elim 5 (fun v=>(vert.symm v).val)
  have valid : h=5 ∨ h<5 ∧ h≠free.val := by
    cases eq : p with
    | none => exact Or.inl (by simp [h,eq])
    | some z =>
      have ne : z≠u:=fun eq'=>apart (eq' ▸ eq)
      right;refine ⟨by simp [h,eq],?_⟩
      change p.elim 5 _≠_
      simp only [eq,Option.elim_some]
      intro e
      exact ne (vert.symm.injective (Fin.ext e))
  have bonus (v : V) : Five.weight v.val h=(if p=some (vert v) then 1 else 0) := by
    cases eq : p with
    | none => simp [h,eq,Five.weight,show v.val≠5 by omega]
    | some z =>
      have iff : v.val=(vert.symm z).val ↔ z=vert v := by
        constructor
        · intro e
          simpa using (congrArg vert (Fin.ext e : v=vert.symm z)).symm
        · rintro rfl;simp
      simp [h,eq,Five.weight,iff]
  have want (v : ℕ) (bound : v<5) (ne : v≠free.val) :
      k+Five.weight v h≤Five.rowSum (fun i a=>Five.digit (Five.total (sample f)
        (Five.rowArc (representativeWord w.r) i a))) v := by
    let z : V:=⟨v,bound⟩
    have diff : vert z≠u := by
      intro sameVertex
      have back : z=free := by simpa [free] using congrArg vert.symm sameVertex
      exact ne (congrArg Fin.val back)
    change k+Five.weight z.val h≤_
    rw [bonus]
    exact (marks (vert z) diff).trans_eq (eqRows z)
  have got:=Five.bound_digits (cert free.val h free.isLt valid) free.isLt hk (sample f)
    (fun j _=>(box (perm.symm (Fin.ofNat 10 j))).1) (fun j _=>(box (perm.symm (Fin.ofNat 10 j))).2)
    macroRep want
  rw [all_width f (sample f) (sample_val f)] at got
  have area : Board.total f=Board.total g:=Equiv.sum_comp perm.symm g
  have goal : (Five.goal h:ℝ)/2=(if p.isSome then 3 else 5/2 : ℝ) := by
    cases eq : p with
    | none => norm_num [h,eq,Five.goal]
    | some z =>
      have nz : (vert.symm z).val≠5:=by have a:=(vert.symm z).isLt;omega
      norm_num [h,eq,Five.goal,nz]
  rwa [area,goal] at got

#print axioms mask_scores
#print axioms orbit_capacity
end R68.Raw
