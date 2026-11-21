import OrdinaryMixedMoment
import FixedCenterGap
noncomputable section
namespace R56.ProfileMass
open Real JSP404 R58.Plane R54.GapTest R55.WeightedCollision

def chart (F : Fan) : R56.Windows.Row (F.n+1) where
  w i := if i≤F.n then F.u i else F.u 0+π
  ordered := by
    intro a b ab bn
    split_ifs with be be
    · exact F.sorted.monotone (min_le_min_right F.n ab)
    · have ha:=F.bounds (F.idx a)
      have hz:=F.bounds (F.idx 0)
      change _ ∧ F.u a<π at ha
      change 0≤F.u 0 ∧ _ at hz
      linarith
    · omega
    · exact le_rfl
  period := by simp

theorem chord {x : Point} {t : ℝ} {s : Bool} {r : ℝ} (pos : 0<r)
    (eq : x=r • R37.SignedFan.oriented t s) : Bearing x t := by
  cases s
  · exact ⟨r,pos,-1,Or.inl rfl,by simpa [R37.SignedFan.oriented] using eq⟩
  · exact ⟨r,pos,1,Or.inr rfl,by simpa [R37.SignedFan.oriented] using eq⟩

theorem centered_gap (F : Fan) (j : Fin (F.n+1)) :
    (chart F).w (j.val+1)-(chart F).w j=gap F j := by
  have jn : j.val≤F.n:=by omega
  by_cases lt : j.val<F.n
  · simp [chart,gap,lt,jn,show j.val+1≤F.n by omega]
  · have eq : j.val=F.n:=by omega
    simp [chart,gap,eq]

theorem represented {S : Finset Point} {F : S→Fan} {l : ℝ} (P : R37.SignedFan.IsProfile S l F) :
    Witnessed (fun p=>chart (F p)) (fun p : S=>p.val) := by
  intro i j hj
  have obs:=(P i).1
  have atWall (k : Fin ((F i).n+1)) : ∃ p : S,i≠p ∧ Bearing (p.val-i.val) ((F i).bearing k) := by
    obtain ⟨p,t,tp,eq⟩:=obs.2 k
    let v : S:=⟨p.val,Finset.mem_of_mem_erase p.property⟩
    exact ⟨v,fun e=>(Finset.mem_erase.mp p.property).1 (congrArg Subtype.val e.symm),chord tp eq⟩
  by_cases le : j≤(F i).n
  · obtain ⟨v,ne,wall⟩:=atWall ⟨j,by omega⟩
    refine ⟨v,ne,?_⟩
    simpa [chart,le,R37.SignedFan.Row.u,R37.SignedFan.Row.idx,Nat.min_eq_left le] using wall
  · obtain ⟨v,ne,wall⟩:=atWall 0
    refine ⟨v,ne,?_⟩
    simpa [chart,le,R37.SignedFan.Row.u,R37.SignedFan.Row.idx] using bearing_closes wall

theorem exact_score {S : Finset Point} (F : S→Fan) (v : S) (l : ℝ) :
    R56.Windows.score (fun p=>chart (F p)) v l=digits (F v) l := by
  change (∑ j : Fin ((F v).n+1), (⌊((chart (F v)).w (j.val+1)-(chart (F v)).w j)/l⌋₊-1))=_
  simp only [centered_gap,digits]

theorem weight_bound {S : Finset Point} {F : S→Fan} {l : ℝ} (lp : 0<l)
    (P : R37.SignedFan.IsProfile S l F) {w : S→ℕ}
    (A : Admissible w (fun p : S=>p.val) (π-l)) : ∀ i,dim w i≤digits (F i) l := by
  intro i
  simpa [exact_score] using admissible_bound (fun p=>chart (F p)) lp (represented P) A i
end R56.ProfileMass
#print axioms R56.ProfileMass.weight_bound
