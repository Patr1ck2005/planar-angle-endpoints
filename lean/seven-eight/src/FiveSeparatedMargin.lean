import AttainedProfile
import WeightedLabels

noncomputable section
namespace R87.Stability
open Real JSP404 Finset Filter Topology R54.Profile R55.WeightedCollision R57.Compact

/-- The only geometric input to the compactness argument. -/
def EndpointCap : Prop := ∀ (m:ℕ),5≤m→∀(c:Fin m→Point),Function.Injective c→
  ∀w:Fin m→ℕ,(∀i,0<w i)→2*π/3∈attainable w c→(∑i,w i)≤6

def mark (i:Fin 5) : Fin 7 := i.castSucc.castSucc

/-- In a compact normalized seven-point sample, five marked sites stay apart.
The other two may merge with each other or with the marked sites. -/
theorem compact_five (cap:EndpointCap) {ρ:ℝ} (rp:0<ρ) :
    ∃ε:ℝ,0<ε ∧ ∀x:Fin 7→Point,Function.Injective x→
      (∀i,x i∈Metric.closedBall (0:Point) 1)→
      (∀i j:Fin 5,i≠j→ρ≤dist (x (mark i)) (x (mark j)))→
      2*π/3+ε<maxAngle (diagram x) := by
  classical
  by_contra! fail
  let d (n:ℕ):ℝ:=1/((n:ℝ)+1)
  have dp (n):0<d n:=by dsimp [d];positivity
  have dz:Tendsto d atTop (𝓝 0):=tendsto_one_div_add_atTop_nhds_zero_nat
  choose x xi ball sep angle using fun n=>fail (d n) (dp n)
  let C:Set (Fin 7→Point):=Set.univ.pi fun _=>Metric.closedBall (0:Point) 1
  have K:IsCompact C:=isCompact_univ_pi fun _=>isCompact_closedBall (0:Point) 1
  have mem (n:ℕ):x n∈C:=fun j _=>ball n j
  obtain ⟨L,_,k,inc,lim⟩:=K.tendsto_subseq mem
  have cv (j:Fin 7):=tendsto_pi_nhds.mp lim j
  have separate (i j:Fin 5) (ne:i≠j):L (mark i)≠L (mark j):=by
    intro eq
    have gap:=le_of_tendsto_of_tendsto' (tendsto_const_nhds (x:=ρ))
      ((cv (mark i)).dist (cv (mark j))) (fun n=>sep (k n) i j ne)
    rw [eq,dist_self] at gap;exact rp.not_ge gap
  obtain ⟨m,_,c,ci,w,wp,sz,E,fib⟩:=relabel L ⟨mark 0,mark 1,separate 0 1 (by decide)⟩
  let site (i:Fin 5):Fin m := (E.symm (mark i)).1
  have loc (i:Fin 5):L (mark i)=c (site i):=by simpa [site] using fib (E.symm (mark i))
  have inject:Function.Injective site:=by
    intro i j same;by_contra ne
    exact separate i j ne ((loc i).trans ((congrArg c same).trans (loc j).symm))
  have five:5≤m:=by simpa using Fintype.card_le_of_injective site inject
  have hit:2*π/3∈attainable w c:=by
    intro η ηp
    have near (j:Fin 7):∀ᶠ n in atTop,dist (x (k n) j) (L j)<η:=Metric.tendsto_nhds.mp (cv j) η ηp
    have slack:∀ᶠ n in atTop,d (k n)<η:=(dz.comp inc.tendsto_atTop).eventually_lt tendsto_const_nhds ηp
    obtain ⟨n,close,lt⟩:=((eventually_all.mpr near).and slack).exists
    let g:Label w→Point:=x (k n) ∘ E
    have same:points g=diagram (x (k n)):=by
      ext y
      simp only [points,diagram,Finset.mem_image,Finset.mem_univ,true_and]
      exact ⟨fun ⟨j,h⟩=>⟨E j,h⟩,fun ⟨j,h⟩=>⟨E.symm j,by simpa [g] using h⟩⟩
    refine ⟨g,(xi _).comp E.injective,fun j=>?_,?_⟩
    · change dist (x (k n) (E j)) (c j.1)<η
      rw [←fib];exact close _
    · rw [same];exact (angle _).trans_lt (by linarith)
  have no:=cap m five c ci w wp hit
  omega

private theorem extend_one {n:ℕ} {S:Finset Point} (room:n<S.card)
    (x:Fin n→Point) (xi:Function.Injective x) (mem:∀i,x i∈S):
    ∃y:Fin (n+1)→Point,Function.Injective y ∧ (∀i,y i∈S) ∧ ∀i,y i.castSucc=x i := by
  classical
  let T:=Finset.univ.image x
  have sz:T.card=n:=by simp [T,Finset.card_image_of_injective _ xi]
  obtain ⟨a,ha,out⟩:∃a∈S,a∉T:=by
    by_contra! none
    have h:S⊆T:=none
    have small:=Finset.card_le_card h
    omega
  have outside:a∉Set.range x:=by
    rintro ⟨j,rfl⟩;exact out (Finset.mem_image_of_mem _ (Finset.mem_univ j))
  refine ⟨Fin.snoc x a,Fin.snoc_injective_of_injective xi outside,?_,?_⟩
  · intro i
    induction i using Fin.lastCases with
    | last=>simpa using ha
    | cast j=>simpa using mem j
  · intro i;exact Fin.snoc_castSucc _ _ _

/-- Five points separated on the diameter scale give a uniform positive angular
margin, independent of the number of other points in the finite set. -/
theorem five_separated (cap:EndpointCap) {ρ:ℝ} (rp:0<ρ) :
    ∃ε:ℝ,0<ε ∧ ∀(S:Finset Point),7≤S.card→∀c:Fin 5→Point,(∀i,c i∈S)→
      (∀i j,i≠j→ρ*Metric.diam (S:Set Point)≤dist (c i) (c j))→
      2*π/3+ε<maxAngle S := by
  classical
  obtain ⟨ε,ep,exclude⟩:=compact_five cap rp
  refine ⟨ε,ep,?_⟩
  intro S size c mem apart
  let D:=Metric.diam (S:Set Point)
  have nt:S.Nontrivial:=Finset.one_lt_card_iff_nontrivial.mp (by omega)
  have pos:0<D:=Metric.diam_pos (s:=(S:Set Point)) nt S.finite_toSet.isBounded
  have ci:Function.Injective c:=by
    intro i j eq;by_contra ne
    have h:=apart i j ne;rw [eq,dist_self] at h
    exact (mul_pos rp pos).not_ge h
  obtain ⟨u,ui,um,uc⟩:=extend_one (by omega:5<S.card) c ci mem
  obtain ⟨v,vi,vm,vu⟩:=extend_one (by omega:6<S.card) u ui um
  have marked (i):v (mark i)=c i:=(vu _).trans (uc i)
  let x (i:Fin 7):=D⁻¹ • (v i-v 0)
  have distx (i j):dist (x i) (x j)=D⁻¹*dist (v i) (v j):=by
    dsimp [x];rw [dist_smul₀,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr pos),dist_sub_right]
  have xi:Function.Injective x:=by
    intro i j eq;by_contra ne
    have h:=mul_pos (inv_pos.mpr pos) (dist_pos.mpr (vi.ne ne))
    rw [←distx,eq,dist_self] at h;exact h.false
  have ball (i):x i∈Metric.closedBall (0:Point) 1:=by
    have zero:x 0=0:=by simp [x]
    rw [Metric.mem_closedBall,←zero,distx,←div_eq_inv_mul]
    apply (div_le_iff₀ pos).2
    simpa only [one_mul] using Metric.dist_le_diam_of_mem S.finite_toSet.isBounded (vm i) (vm 0)
  have sep (i j:Fin 5) (ne:i≠j):ρ≤dist (x (mark i)) (x (mark j)):=by
    rw [distx,marked,marked,←div_eq_inv_mul];exact (le_div_iff₀ pos).mpr (apart i j ne)
  apply (exclude x xi ball sep).trans_le
  apply maxAngle_le (maxAngle_nonneg _)
  intro a ha b hb e he ab ae be
  obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp ha
  obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hb
  obtain ⟨k,_,rfl⟩:=Finset.mem_image.mp he
  have diff (i j):x i-x j=D⁻¹ • (v i-v j):=by dsimp [x];rw [←smul_sub];congr 1;abel
  change InnerProductGeometry.angle (x i-x j) (x k-x j)≤_
  rw [diff,diff,InnerProductGeometry.angle_smul_left_of_pos _ _ (inv_pos.mpr pos),
    InnerProductGeometry.angle_smul_right_of_pos _ _ (inv_pos.mpr pos)]
  exact angle_le_maxAngle (vm i) (vm j) (vm k)
    (vi.ne (fun h=>ab (congrArg x h))) (vi.ne (fun h=>ae (congrArg x h))) (vi.ne (fun h=>be (congrArg x h)))

end R87.Stability
#print axioms R87.Stability.compact_five
#print axioms R87.Stability.five_separated

