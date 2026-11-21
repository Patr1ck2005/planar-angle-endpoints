import ConvexEar

noncomputable section
namespace R86.ConvexMass
open Real JSP404 Finset

private def ang (a b c : Point) := EuclideanGeometry.angle a b c

private def totalInterior (g : ℕ→Point) (n : ℕ) :=
  (∑j∈range (n+1),ang (g j) (g (j+1)) (g (j+2)))+
    ang (g 1) (g 0) (g (n+2))+ang (g 0) (g (n+2)) (g (n+1))

private theorem triangulate (n : ℕ) (g : ℕ→Point)
    (ci : ∀i j, i < n+3 → j < n+3 → i≠j → g i≠g j)
    (pos : ∀i j k,i < n+3 → j < n+3 → k < n+3 →
      ((i < j ∧ j < k) ∨ (j < k ∧ k < i) ∨ (k < i ∧ i < j)) → 0 < det (g j-g i) (g k-g i)) :
    totalInterior g n=((n:ℝ)+1)*π := by
  induction n generalizing g with
  | zero =>
    have s:=EuclideanGeometry.angle_add_angle_add_angle_eq_pi (g 2) (ci 0 1 (by decide) (by decide) (by decide))
    simp only [totalInterior,ang,sum_range_one,Nat.cast_zero,zero_add,one_mul]
    rw [EuclideanGeometry.angle_comm (g 0) (g 1) (g 2)]
    linarith only [s]
  | succ n ih =>
    have old:=ih g (fun i j a b neq=>ci i j (by omega) (by omega) neq)
      (fun i j k a b c cyc=>pos i j k (by omega) (by omega) (by omega) cyc)
    have spl (i a w b : ℕ) (iw : w≠i) (ih : i < n+1+3) (wh : w < n+1+3)
        (aw : 0 < det (g a-g i) (g w-g i)) (wb : 0 < det (g w-g i) (g b-g i))
        (ab : 0 < det (g a-g i) (g b-g i)) :
        ang (g a) (g i) (g b)=ang (g a) (g i) (g w)+ang (g w) (g i) (g b) :=
      arc_split (sub_ne_zero.mpr (ci w i wh ih iw)) aw wb ab
    have at₀:=spl 0 1 (n+2) (n+3) (by omega) (by omega) (by omega)
      (pos _ _ _ (by omega) (by omega) (by omega) (by omega))
      (pos _ _ _ (by omega) (by omega) (by omega) (by omega))
      (pos _ _ _ (by omega) (by omega) (by omega) (by omega))
    have atL:=spl (n+2) (n+3) 0 (n+1) (by omega) (by omega) (by omega)
      (pos _ _ _ (by omega) (by omega) (by omega) (by omega))
      (pos _ _ _ (by omega) (by omega) (by omega) (by omega))
      (pos _ _ _ (by omega) (by omega) (by omega) (by omega))
    have tr := EuclideanGeometry.angle_add_angle_add_angle_eq_pi (g (n+3))
      (ci 0 (n+2) (by omega) (by omega) (by omega))
    change ang (g (n+2)) (g 0) (g (n+3))+ang (g 0) (g (n+3)) (g (n+2))+
      ang (g (n+3)) (g (n+2)) (g 0)=π at tr
    rw [show ang (g (n+3)) (g (n+2)) (g (n+1))=ang (g (n+1)) (g (n+2)) (g (n+3)) from EuclideanGeometry.angle_comm ..] at atL
    rw [totalInterior] at old ⊢
    rw [sum_range_succ]
    push_cast
    linarith only [old,at₀,atL,tr]

/-- Exact exterior-turn sum for actual planar centers in strict convex boundary
order. No exterior-turn formula is supplied as a hypothesis. -/
theorem total_turn {n : ℕ} {c : Site n→Point} (ci : Function.Injective c) (hull : HullOrder c) :
    (∑i,exterior c i)=2*π := by
  let g (i : ℕ):=if hi:i < n+3 then c ⟨i,hi⟩ else c 0
  have tri:=triangulate n g (fun i j a b ne=>by
    simp only [g,dite_eq_left a,dite_eq_left b];apply ci.ne;exact fun eq=>ne (congrArg Fin.val eq))
    (fun i j k a b d cyc=>by
      simp only [g,dite_eq_left a,dite_eq_left b,dite_eq_left d]
      exact hull ⟨i,a⟩ ⟨j,b⟩ ⟨k,d⟩ cyc)
  let A (i : Site n):=ang (c (prev i)) (c i) (c (next i))
  have start : A 0=ang (g 1) (g 0) (g (n+2)) := by
    rw [show A 0=ang (g (n+2)) (g 0) (g 1) by simp [A,prev,next,g]]
    exact EuclideanGeometry.angle_comm ..
  have last : A (Fin.last (n+2))=ang (g 0) (g (n+2)) (g (n+1)) := by
    have pred : prev (Fin.last (n+2))=(⟨n+1,by omega⟩ : Site n) := by
      unfold prev;rw [dite_eq_left (show 0 < (Fin.last (n+2)).val by change 0 < n+2;omega)];rfl
    rw [show A (Fin.last (n+2))=ang (g (n+1)) (g (n+2)) (g 0) by simp [A,pred,next,g];rfl]
    exact EuclideanGeometry.angle_comm ..
  have mid (i : Fin (n+1)) :
      A i.succ.castSucc=ang (g i.val) (g (i.val+1)) (g (i.val+2)) := by
    have a : i.val < n+3 := by omega
    have b : i.val+1 < n+3 := by omega
    have d : i.val+2 < n+3 := by omega
    simp [A,prev,next,g,a,b,d,Fin.val_succ,show i.val≤n by omega];rfl
  have S : ∑i,A i=totalInterior g n := by
    rw [Fin.sum_univ_castSucc,Fin.sum_univ_succ]
    change A 0+(∑j:Fin (n+1),A j.succ.castSucc)+A (Fin.last (n+2))=_
    simp_rw [mid];rw [start,last]
    rw [Fin.sum_univ_eq_sum_range (fun i=>ang (g i) (g (i+1)) (g (i+2))) (n+1)]
    unfold totalInterior;ring
  change (∑i : Site n,(π-A i))=_
  rw [sum_sub_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,S,tri]
  push_cast;ring

end R86.ConvexMass
#print axioms R86.ConvexMass.total_turn
