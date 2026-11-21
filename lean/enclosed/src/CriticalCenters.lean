import RetainedCapacity
import IrreducibleOptimizer
noncomputable section
namespace R65.Retention
open Real JSP404 R54.Profile R54.GapTest R55.WeightedCollision R56.Windows R64.Merge

/-- Every complete chart of every proper retained subset of at least two real centers
has too little total capacity at the original threshold. -/
def Critical {k : ℕ} (c : Fin k→Point) (N : ℕ) (θ : ℝ) : Prop :=
  ∀ {h : ℕ},2≤h → h<k → ∀ (e : Fin h↪Fin k) {m : Fin h→ℕ} (R : ∀i,Row (m i)),
    Represents R (c∘e) → Witnessed R (c∘e) → capacity R θ<N

private theorem below_pi {N : ℕ} (ge : 3≤N) : alpha N<π := by
  apply (Jsp404.alpha_le_alphaN N ge).trans_lt
  by_cases h : 4≤N
  · exact Jsp404.alphaN_lt_pi h
  · have eq : N=3 := by omega
    rw [eq];change π/3<π;linarith [pi_pos]

theorem minimum_centers {N : ℕ} (ge : 3≤N) :
    ∃ S : Shape,(∑i,S.w i)=N ∧ alpha N∈attainable S.w S.c ∧
      (∀ T : Shape,(∑i,T.w i)=N → alpha N∈attainable T.w T.c → S.size≤T.size) ∧
      Critical S.c N (alpha N) := by
  classical
  obtain ⟨m,h,_,c,ci,_,w,wp,sz,_,ad⟩:=realized_minimum ge
  let P (k : ℕ):=∃ T : Shape,T.size=k ∧ (∑i,T.w i)=N ∧ alpha N∈attainable T.w T.c
  have ok : ∃k,P k := ⟨m,⟨m,h,c,ci,w,wp⟩,rfl,sz,(fixed_profile wp (fin_other h) ci).mpr ad⟩
  obtain ⟨S,eq,total,hit⟩:=Nat.find_spec ok
  have least (T : Shape) (sz : (∑i,T.w i)=N) (val : alpha N∈attainable T.w T.c) : S.size≤T.size :=
    eq ▸ Nat.find_min' ok (show P T.size from ⟨T,rfl,sz,val⟩)
  refine ⟨S,total,hit,least,?_⟩
  intro k two less e m R front back
  let : Nontrivial (Fin k):=Fin.nontrivial_iff_two_le.mpr two
  let : Nontrivial (Fin S.size):=Fin.nontrivial_iff_two_le.mpr S.two
  by_contra! room
  obtain ⟨u,up,mass,cap⟩:=(retained_mass_iff S.ci S.wp (below_pi ge) hit e R front back).mpr
    (by simpa only [total] using room)
  let T : Shape:=⟨k,two,S.c∘e,S.ci.comp e.injective,u,fun i=>(S.wp (e i)).trans_le (up i)⟩
  exact (not_le_of_gt less) (least T (mass.trans total) cap)

/-- The remaining unrestricted lower bound uses only macro angles, cardinalities,
and finite sums from the actual projective gap rows, on full and retained sets. -/
theorem unrestricted_iff {N : ℕ} (ge : 3≤N) :
    alpha N=Jsp404.alphaN N ↔
      ∀ {k : ℕ},5≤k → k≤N → ∀ (c : Fin k→Point), Function.Injective c →
      ¬R58.CircleModel.OnCircle c → ∀θ : ℝ,0≤θ → θ<π → Macro c θ →
      (∃ m : Fin k→ℕ,∃ R : ∀i,Row (m i),Represents R c ∧ Witnessed R c ∧ N≤capacity R θ) →
      Critical c N θ → Jsp404.alphaN N≤θ := by
  constructor
  · rintro solved k five small c ci _ θ pos below legal ⟨m,R,front,back,room⟩ _
    let : Nontrivial (Fin k):=Fin.nontrivial_iff_two_le.mpr (by omega)
    obtain ⟨w,wp,size,att⟩:=(positive_mass_iff ci R front back pos below legal N).mpr
      ⟨by simpa using small,room⟩
    have bound:=alpha_bound (size ▸ ge) att
    simpa only [size,solved] using bound
  · intro all
    obtain ⟨S,total,hit,_,critical⟩:=minimum_centers ge
    apply le_antisymm (Jsp404.alpha_le_alphaN N ge)
    have dp:=sub_pos.mpr (below_pi ge)
    have terminal (endp : Reduces (π-alpha N) S) : Jsp404.alphaN N≤alpha N := by
      have bound:=lower_of_chain dp S endp (total ▸ ge) (by simpa only [sub_sub_cancel] using hit)
      simpa only [sub_sub_cancel,total] using bound
    by_cases four : S.size≤4
    · exact terminal (.terminal S four)
    by_cases circle : R58.CircleModel.OnCircle S.c
    · exact terminal (.cyclic S circle)
    let : Nontrivial (Fin S.size):=Fin.nontrivial_iff_two_le.mpr S.two
    obtain ⟨m,R,front,back⟩:=actual_rows S.c S.ci
    have law:=(fixed_profile S.wp (fin_other S.two) S.ci).mp hit
    have room:=(positive_mass_iff S.ci R front back law.1 (below_pi ge) law.2.1 N).mp
      ⟨S.w,S.wp,total,hit⟩
    exact all (by omega) (by simpa only [Fintype.card_fin] using room.1) S.c S.ci circle _
      law.1 (below_pi ge) law.2.1 ⟨m,R,front,back,room.2⟩ critical

#print axioms minimum_centers
#print axioms unrestricted_iff
end R65.Retention