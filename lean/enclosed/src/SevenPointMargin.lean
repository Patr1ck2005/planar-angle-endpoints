import OpenOrdinaryMinimum

noncomputable section
namespace R89.Ordinary
open JSP404 Real Finset Filter Topology R55.WeightedCollision

/-- Seven uniformly separated sites in the closed unit ball give an angular
margin above 120 degrees depending only on their separation. -/
theorem compact_seven {ρ : ℝ} (rp : 0<ρ) : ∃ε : ℝ,0<ε ∧ ∀ c : Fin 7→Point,
    (∀i,c i∈Metric.closedBall (0:Point) 1) → (∀i j,i≠j→ρ≤dist (c i) (c j)) →
    ¬Macro c (2*π/3+ε) := by
  classical
  by_contra! fail
  let d (n : ℕ) := 1/((n:ℝ)+1)
  have dp (n) : 0<d n:=by dsimp [d];positivity
  have dz : Tendsto d atTop (𝓝 0):=tendsto_one_div_add_atTop_nhds_zero_nat
  choose c bounds sep mac using fun n=>fail (d n) (dp n)
  let C : Set (Fin 7→Point):=Set.univ.pi fun _=>Metric.closedBall (0:Point) 1
  have K : IsCompact C:=isCompact_univ_pi fun _=>isCompact_closedBall (0:Point) 1
  have mem (n : ℕ) : c n∈C:=fun j _=>bounds n j
  obtain ⟨b,_,f,inc,lim⟩:=K.tendsto_subseq mem
  have cv (j : Fin 7):=tendsto_pi_nhds.mp lim j
  have inj : Function.Injective b:=by
    intro i j eq
    by_contra ne
    have gap:=le_of_tendsto_of_tendsto' (tendsto_const_nhds (x:=ρ)) ((cv i).dist (cv j))
      (fun n=>sep (f n) i j ne)
    rw [eq,dist_self] at gap;linarith
  have atLimit : Macro b (2*π/3) := by
    intro i j k ij ik jk
    have angles:= (EuclideanGeometry.continuousAt_angle (inj.ne ij) (inj.ne jk.symm)).tendsto.comp
      ((cv i).prodMk_nhds ((cv j).prodMk_nhds (cv k)))
    have rhs:= (tendsto_const_nhds (x:=2*π/3)).add (dz.comp inc.tendsto_atTop)
    have h:=le_of_tendsto_of_tendsto' angles rhs (fun n=>mac (f n) i j k ij ik jk)
    simpa using h
  have no:=at_most_six inj atLimit
  norm_num at no

/-- Scale-free form. A configuration containing seven points separated by at
least ρ times its diameter has some ordinary angle exceeding 120°+ε(ρ). -/
theorem separated_seven {ρ : ℝ} (rp : 0<ρ) :
    ∃ε : ℝ,0<ε ∧ ∀ (S : Finset Point) (c : Fin 7→Point), (∀i,c i∈S) →
      (0<Metric.diam (S:Set Point)) →
      (∀i j,i≠j→ρ*Metric.diam (S:Set Point)≤dist (c i) (c j)) →
      2*π/3+ε<maxAngle S := by
  obtain ⟨ε,positive,exclude⟩:=compact_seven rp
  refine ⟨ε,positive,?_⟩
  intro S c mem Dp sep
  let D:=Metric.diam (S:Set Point)
  let a (i : Fin 7):=D⁻¹ • (c i-c 0)
  have size (i j) : dist (a i) (a j)=D⁻¹*dist (c i) (c j):=by
    dsimp [a];rw [dist_smul₀,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr Dp),dist_sub_right]
  have ball (i) : a i∈Metric.closedBall (0:Point) 1:=by
    have eq : a 0=0:=by simp [a]
    rw [Metric.mem_closedBall,←eq,size]
    have bound:=Metric.dist_le_diam_of_mem S.finite_toSet.isBounded (mem i) (mem 0)
    change D⁻¹*dist (c i) (c 0)≤1
    calc _ ≤ D⁻¹*D:=mul_le_mul_of_nonneg_left bound (inv_pos.mpr Dp).le
         _ = 1:=inv_mul_cancel₀ Dp.ne'
  have apart (i j) (ne : i≠j) : ρ≤dist (a i) (a j):=by
    rw [size,←div_eq_inv_mul]
    exact (le_div_iff₀ Dp).mpr (sep i j ne)
  have inj : Function.Injective c:=by
    intro i j eq;by_contra ne
    have z:=sep i j ne
    rw [eq,dist_self] at z
    exact (mul_pos rp Dp).not_ge z
  by_contra! low
  apply exclude _ ball apart
  intro i j k ij ik jk
  have bound:=(angle_le_maxAngle (mem i) (mem j) (mem k) (inj.ne ij) (inj.ne ik) (inj.ne jk)).trans low
  change InnerProductGeometry.angle (a i - a j) (a k - a j)≤_
  have diff (i j) : a i-a j=D⁻¹ • (c i-c j):=by dsimp [a];rw [←smul_sub];congr 1;abel
  rw [diff,diff,InnerProductGeometry.angle_smul_left_of_pos _ _ (inv_pos.mpr Dp),
    InnerProductGeometry.angle_smul_right_of_pos _ _ (inv_pos.mpr Dp)]
  exact bound

end R89.Ordinary
#print axioms R89.Ordinary.compact_seven
#print axioms R89.Ordinary.separated_seven
