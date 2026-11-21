import FourSiteEndpoint
import InteriorChordReserve
import DiameterRays

noncomputable section
namespace R90.Endpoint
open Real JSP404 R55.WeightedCollision R87.Diameter R89.Interior InnerProductGeometry

/-- The presence of even one other center leaves room for at most two
microscopic binary axes at the 120-degree endpoint. -/
theorem at_most_four_labels {I : Type*} [Fintype I] [Nontrivial I]
    {c : I→Point} (ci : Function.Injective c) {w : I→ℕ} (wp : ∀i,0<w i)
    (hit : 2*π/3∈attainable w c) (i : I) : w i≤4 := by
  let δ:=π/3
  have dp : 0<δ:=by dsimp [δ];positivity
  have eq : 2*π/3=π-δ:=by dsimp [δ];ring
  obtain ⟨_,_,v,unit,ins,out⟩:=(R54.Profile.fixed_profile wp (fun j=>exists_ne j) ci).mp (eq ▸ hit)
  have A : R56.Decorated.Axes c (dim w) (π-δ) :=
    ⟨v,fun j a h=>by simpa [h] using unit j a,ins,out⟩
  obtain ⟨j,off⟩:=exists_ne i
  have b:=chord_reserve ci dp (by dsimp [δ];linarith [pi_pos]) A i (fun _:Fin 1=>j)
    (fun _=>off) (fun a b ne=>(ne (Subsingleton.elim a b)).elim)
  have per : π/δ=3:=by dsimp [δ];field_simp
  rw [per] at b;norm_num at b
  have le : dim w i≤2:=by omega
  exact (Nat.le_pow_clog (by decide : 1<2) (w i)).trans (Nat.pow_le_pow_right (by decide) le)

/-- Any two fixed distinct centers accommodate arbitrary positive weights
up to four apiece at the endpoint. -/
theorem two_centers {c : Fin 2→Point} (ci : Function.Injective c) (w : Fin 2→ℕ)
    (wp : ∀i,0<w i) (small : ∀i,w i≤4) : 2*π/3∈attainable w c := by
  let δ:=π/3
  have dp : 0<δ:=by dsimp [δ];positivity
  have per : 3*δ=π:=by dsimp [δ];ring
  obtain ⟨t,T⟩:=head_exists (sub_ne_zero.mpr (ci.ne (by decide : (1:Fin 2)≠0)))
  obtain ⟨r,rp,head⟩:=T
  have eq : 2*π/3=π-δ:=by dsimp [δ];ring
  rw [eq]
  let h (j : ℕ):=t+((j:ℝ)+1)*δ
  let v (i : Fin 2) (p : Fin (dim w i)):=circleDirection (h p.val)
  have digits (i):dim w i≤2:=Nat.clog_le_of_le_pow (small i)
  have zeroOne {i : Fin 2} (p : Fin (dim w i)) : p.val=0 ∨ p.val=1:=by
    have:=digits i; have:=p.isLt;omega
  apply admissible_mem wp ci
  refine ⟨by linarith,?_,v,fun _ _=>norm_circleDirection _,?_,?_⟩
  · intro i j k ij ik jk;fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all
  · intro i p q ne r s hr hs
    have neq:=Fin.val_ne_of_ne ne
    have exactGap : |h 0-h 1|=δ := by
      rw [show h 0-h 1= -δ by dsimp [h];ring,abs_neg,abs_of_pos dp]
    have absEq : |h p.val-h q.val|=δ := by
      rcases zeroOne p with a|a <;> rcases zeroOne q with b|b <;>
        rw [a,b] at neq ⊢
      · exact (neq rfl).elim
      · exact exactGap
      · rwa [abs_sub_comm]
      · exact (neq rfl).elim
    exact signed_circleDirection_angle_le_of_separation dp.le absEq.ge (absEq.le.trans (by linarith)) r s hr hs
  · intro i j ne p s hs
    have dist : δ≤|h p.val-t| ∧ |h p.val-t|≤π-δ:=by
      rcases zeroOne p with a|a <;> unfold h <;> rw [a] <;> norm_num <;> rw [abs_of_nonneg (by linarith)] <;> constructor <;> linarith
    have plus:=signed_circleDirection_angle_le_of_separation dp.le dist.1 dist.2 s 1 hs (Or.inr rfl)
    have minus:=signed_circleDirection_angle_le_of_separation dp.le dist.1 dist.2 s (-1) hs (Or.inl rfl)
    fin_cases i <;> fin_cases j
    · exact (ne rfl).elim
    · change angle (s • circleDirection (h p.val)) (c 1-c 0)≤π-δ
      rw [head,angle_smul_right_of_pos _ _ rp];simpa using plus
    · change angle (s • circleDirection (h p.val)) (c 0-c 1)≤π-δ
      rw [←neg_sub (c 1) (c 0),head,←smul_neg,angle_smul_right_of_pos _ _ rp];simpa using minus
    · exact (ne rfl).elim
end R90.Endpoint
#print axioms R90.Endpoint.at_most_four_labels
#print axioms R90.Endpoint.two_centers
