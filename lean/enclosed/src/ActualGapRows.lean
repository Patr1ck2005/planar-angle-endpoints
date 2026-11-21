import GapPacking
noncomputable section
namespace R54.GapTest
open Real JSP404 R56.Windows

/-- Sort the distinct real wall representatives, then close by adjoining the
first wall plus π. The sorted list keeps both extremal lifts if present. -/
private theorem sort_row (S:Finset ℝ) (non:S.Nonempty) (range:∀x∈S,0≤x ∧ x≤π) :
    ∃R:Row S.card, (∀x∈S,∃h≤S.card,R.w h=x) ∧
      ∀h≤S.card,(R.w h∈S ∨ ∃x∈S,R.w h=x+π) := by
  classical
  let e:=S.orderIsoOfFin (k:=S.card) rfl
  let first:Fin S.card:=⟨0,Finset.card_pos.mpr non⟩
  let w (n:ℕ):ℝ:=if h:n<S.card then (e ⟨n,h⟩).val else (e first).val+π
  have w0:w 0=(e first).val:=by simp [w,first,Finset.card_pos.mpr non]
  have last:w S.card=(e first).val+π:=by simp [w]
  let R:Row S.card:=
    {w:=w
     ordered:=by
       intro a b ab bm
       by_cases hb:b<S.card
       · have ha:=lt_of_le_of_lt ab hb
         simp only [w,dif_pos ha,dif_pos hb]
         exact e.monotone (show (⟨a,ha⟩:Fin S.card)≤⟨b,hb⟩ from ab)
       · have eq:b=S.card:=by omega
         subst b
         rw [last]
         by_cases ha:a<S.card
         · rw [show w a=(e ⟨a,ha⟩).val by simp [w,ha]]
           linarith [(range _ (e ⟨a,ha⟩).property).2,(range _ (e first).property).1]
         · simp [w,ha]
     period:=by rw [last,w0]}
  refine ⟨R,?_,?_⟩
  · intro x hx
    let j:=e.symm ⟨x,hx⟩
    refine ⟨j.val,j.isLt.le,?_⟩
    change w j.val=x
    rw [show w j.val=(e j).val by simp [w,j.isLt]]
    exact congrArg Subtype.val (e.apply_symm_apply ⟨x,hx⟩)
  · intro h hb
    change w h∈S ∨ ∃x∈S,w h=x+π
    by_cases lt:h<S.card
    · left;simpa [w,lt] using (e ⟨h,lt⟩).property
    · have eq:h=S.card:=by omega
      exact Or.inr ⟨_,(e first).property,eq ▸ last⟩

/-- Ordinary distinct macrocenters with at least two labels supply complete
rows in both directions. No ordered-direction hypotheses are required. -/
theorem actual_rows {I:Type*} [Fintype I] [Nontrivial I] (c:I→Point)
    (inj:Function.Injective c) :
    ∃m:I→ℕ,∃R:∀i,Row (m i),Represents R c ∧ Witnessed R c := by
  classical
  have each (i:I) : ∃m:ℕ, ∃R:Row m,
      (∀j,i≠j→∃h≤m,Bearing (c j-c i) (R.w h)) ∧
      ∀h≤m,∃j,i≠j ∧ Bearing (c j-c i) (R.w h) := by
    let J:={j:I // i≠j}
    have nn (j:J):c j.val-c i≠0:=sub_ne_zero.mpr (inj.ne j.property.symm)
    choose a lo hi line using fun j:J=>polar _ (nn j)
    let S:=Finset.univ.image a
    obtain ⟨k,kne⟩:=exists_ne i
    have non:S.Nonempty:=⟨a ⟨k,kne.symm⟩,Finset.mem_image_of_mem a (Finset.mem_univ _)⟩
    have range (x:ℝ) (hx:x∈S):0≤x ∧ x≤π:=by
      obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hx
      exact ⟨lo j,hi j⟩
    obtain ⟨R,hit,wall⟩:=sort_row S non range
    refine ⟨S.card,R,?_,?_⟩
    · intro j ij
      let k:J:=⟨j,ij⟩
      obtain ⟨h,low,eq⟩:=hit (a k) (Finset.mem_image_of_mem _ (Finset.mem_univ _))
      exact ⟨h,low,eq.symm ▸ line k⟩
    · intro n hn
      rcases wall n hn with mem|⟨x,mem,closed⟩
      · obtain ⟨k,_,eq⟩:=Finset.mem_image.mp mem
        exact ⟨k.val,k.property,eq ▸ line k⟩
      · obtain ⟨k,_,eq⟩:=Finset.mem_image.mp mem
        exact ⟨k.val,k.property,by rw [closed,←eq];exact bearing_closes (line k)⟩
  choose m R fwd back using each
  exact ⟨m,R,fwd,back⟩

#print axioms actual_rows
end R54.GapTest
