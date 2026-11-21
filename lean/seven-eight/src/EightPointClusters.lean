import AttainedProfile
import EndpointShapes

noncomputable section
namespace R88.Stability
open Real JSP404 Finset Filter Topology R54.Profile R55.WeightedCollision R57.Compact

/-- An actual partition of the original set into two sets of four. -/
def FourFour (S:Finset Point) (r:ℝ) : Prop :=
  ∃A B:Finset Point,A.card=4 ∧ B.card=4 ∧ Disjoint A B ∧ A∪B=S ∧
    Metric.diam (A:Set Point)≤r ∧ Metric.diam (B:Set Point)≤r

/-- Pull two labelled fibres in one normalized sample back through its actual
similarity. One separated pair controls the scale of the full configuration. -/
private theorem pullback {S:Finset Point} {f:Fin 8→Point} (fi:Function.Injective f)
    (sim:SimilarImage S f) {ρ:ℝ} (rp:0<ρ) {w:Fin 2→ℕ} (four:∀i,w i=4)
    (E:Label w≃Fin 8) (a b:Fin 8) (far:1/2≤dist (f a) (f b))
    (near:∀x y:Label w,x.1=y.1→dist (f (E x)) (f (E y))≤ρ/2) :
    FourFour S (ρ*Metric.diam (S:Set Point)) := by
  classical
  obtain ⟨o,_,D,dp,transform⟩:=sim
  let T (x:Point):=D⁻¹ • (x-o)
  have scale (x y:Point):dist (T x) (T y)=D⁻¹*dist x y:=by
    dsimp [T];rw [dist_smul₀,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr dp),dist_sub_right]
  have ti:Function.Injective T:=by
    intro x y h
    have v:=scale x y
    rw [h,dist_self] at v
    exact dist_eq_zero.mp ((mul_eq_zero.mp v.symm).resolve_left (inv_ne_zero dp.ne'))
  have preimage (i:Fin 8):∃x∈S,T x=f i:=by
    have h:f i∈diagram f:=Finset.mem_image_of_mem _ (Finset.mem_univ _)
    rw [transform] at h;exact Finset.mem_image.mp h
  choose raw mem back using preimage
  have ri:Function.Injective raw:=by
    intro i j h;exact fi ((back i).symm.trans ((congrArg T h).trans (back j)))
  have sur (x:Point) (hx:x∈S):∃i,raw i=x:=by
    have h:T x∈diagram f:=by rw [transform];exact Finset.mem_image_of_mem _ hx
    obtain ⟨i,_,eq⟩:=Finset.mem_image.mp h
    exact ⟨i,ti ((back i).trans eq)⟩
  have scaled (i j:Fin 8):dist (raw i) (raw j)=D*dist (f i) (f j):=by
    rw [←back i,←back j,scale,←mul_assoc,mul_inv_cancel₀ dp.ne',one_mul]
  have large:D/2≤Metric.diam (S:Set Point):=by
    have d:=Metric.dist_le_diam_of_mem S.finite_toSet.isBounded (mem a) (mem b)
    rw [scaled] at d
    nlinarith only [d,mul_le_mul_of_nonneg_left far dp.le]
  let row (t:Fin 2) (j:Fin (w t)):=raw (E ⟨t,j⟩)
  let cell (t:Fin 2):Finset Point:=Finset.univ.image (row t)
  have rowi (t):Function.Injective (row t):=by
    intro j k h
    have eq: (⟨t,j⟩:Label w)=⟨t,k⟩:=E.injective (ri h)
    exact (Sigma.mk.inj_iff.mp eq).2.eq
  have card (t):(cell t).card=4:=by
    simp only [cell,Finset.card_image_of_injective _ (rowi t),Finset.card_univ,Fintype.card_fin,four]
  have rmem (t) (k:Fin (w t)):row t k∈cell t:=Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have sub (t):cell t⊆S:=by
    intro x hx;obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hx;exact mem _
  have joined:cell 0∪cell 1=S:=by
    refine Finset.Subset.antisymm (Finset.union_subset (sub 0) (sub 1)) ?_
    intro x hx
    obtain ⟨i,hi⟩:=sur x hx
    have cover (z:Label w):raw (E z)∈cell 0∪cell 1:=by
      obtain ⟨t,j⟩:=z;fin_cases t
      · exact Finset.mem_union_left _ (rmem 0 j)
      · exact Finset.mem_union_right _ (rmem 1 j)
    simpa [hi] using cover (E.symm i)
  have separate:Disjoint (cell 0) (cell 1):=by
    apply Finset.disjoint_left.mpr
    intro x a b
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp a
    obtain ⟨j,_,h⟩:=Finset.mem_image.mp b
    have eq: (⟨1,j⟩:Label w)=⟨0,i⟩:=E.injective (ri h)
    exact (by decide : (1:Fin 2)≠0) (congrArg Sigma.fst eq)
  have bound (t):Metric.diam (cell t:Set Point)≤ρ*Metric.diam (S:Set Point):=by
    apply Metric.diam_le_of_forall_dist_le (mul_nonneg rp.le Metric.diam_nonneg)
    intro x hx y hy
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hx
    obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hy
    change dist (raw _) (raw _)≤_
    rw [scaled]
    have small:=near ⟨t,i⟩ ⟨t,j⟩ rfl
    nlinarith only [mul_le_mul_of_nonneg_left small dp.le,mul_le_mul_of_nonneg_left large rp.le]
  exact ⟨cell 0,cell 1,card 0,card 1,separate,joined,bound 0,bound 1⟩

/-- Every ordinary eight-point set sufficiently close to the 120-degree endpoint
splits into two four-point subsets whose diameters are at most the requested
fraction of the full diameter. The angle threshold includes equality. -/
theorem eight_near_endpoint {ρ:ℝ} (rp:0<ρ) :
    ∃ε:ℝ,0<ε ∧ ∀S:Finset Point,S.card=8→maxAngle S≤2*π/3+ε→
      FourFour S (ρ*Metric.diam (S:Set Point)) := by
  classical
  by_contra! fail
  let d (n:ℕ):ℝ:=1/((n:ℝ)+1)
  have dp (n):0<d n:=by dsimp [d];positivity
  have dz:Tendsto d atTop (𝓝 0):=tendsto_one_div_add_atTop_nhds_zero_nat
  choose S card angle bad using fun n=>fail (d n) (dp n)
  obtain ⟨f,fi,sim,same,k,inc,L,_,_,⟨a,b,diam⟩,cv⟩:=
    compact_subsequence (by decide:3≤8) S card
  have ne:L a≠L b:=by intro eq;rw [eq,dist_self] at diam;norm_num at diam
  obtain ⟨m,two,c,ci,w,wp,sz,E,fib⟩:=relabel L ⟨a,b,ne⟩
  have hit:2*π/3∈attainable w c:=by
    intro η ηp
    have close (j:Fin 8):∀ᶠ n in atTop,dist (f (k n) j) (L j)<η:=Metric.tendsto_nhds.mp (cv j) η ηp
    have slack:∀ᶠ n in atTop,d (k n)<η:=(dz.comp inc.tendsto_atTop).eventually_lt tendsto_const_nhds ηp
    obtain ⟨n,near,lt⟩:=((eventually_all.mpr close).and slack).exists
    let g:Label w→Point:=f (k n) ∘ E
    have eq:points g=diagram (f (k n)):=by
      ext x
      simp only [points,diagram,Finset.mem_image,Finset.mem_univ,true_and]
      exact ⟨fun ⟨j,h⟩=>⟨E j,h⟩,fun ⟨j,h⟩=>⟨E.symm j,by simpa [g] using h⟩⟩
    refine ⟨g,(fi _).comp E.injective,fun j=>?_,?_⟩
    · change dist (f (k n) (E j)) (c j.1)<η;rw [←fib];exact near _
    · rw [eq,same];exact (angle _).trans_lt (by linarith)
  have : Nontrivial (Fin m):=Fintype.one_lt_card_iff_nontrivial.mp (by simp only [Fintype.card_fin];omega)
  obtain ⟨sites,four⟩:=R90.Endpoint.eight_shape ci wp sz hit
  simp only [Fintype.card_fin] at sites
  subst m
  have near (x y:Label w):∀ᶠ n in atTop,x.1=y.1→dist (f (k n) (E x)) (f (k n) (E y))≤ρ/2:=by
    by_cases h:x.1=y.1
    · have tend:=((cv (E x)).dist (cv (E y)))
      rw [fib,fib,h,dist_self] at tend
      exact (tend.eventually_lt tendsto_const_nhds (by linarith:0<ρ/2)).mono (fun _ hn _=>hn.le)
    · exact Eventually.of_forall (fun _ eq=>(h eq).elim)
  have far:∀ᶠ n in atTop,1/2<dist (f (k n) a) (f (k n) b):=by
    apply tendsto_const_nhds.eventually_lt ((cv a).dist (cv b))
    rw [diam];norm_num
  obtain ⟨n,nn,ff⟩:=((eventually_all.mpr (fun x=>eventually_all.mpr (near x))).and far).exists
  exact bad (k n) (pullback (fi _) (sim _) rp four E a b ff.le nn)

end R88.Stability
#print axioms R88.Stability.eight_near_endpoint

