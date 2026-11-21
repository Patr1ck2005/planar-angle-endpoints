import ProfileSamples

noncomputable section
namespace R57.Compact
open JSP404 R54.Profile Filter Topology InnerProductGeometry

/-- The labeled diagram is an actual translated positive rescaling of the supplied set. -/
def SimilarImage {N : ℕ} (S : Finset Point) (f : Fin N→Point) : Prop :=
  ∃ o∈S,∃ D : ℝ,0<D ∧ diagram f=S.image (fun p=>D⁻¹ • (p-o))

/-- Label an arbitrary ordinary point set and translate and rescale by its actual
diameter. Every distance is divided by that positive diameter and every angle
is preserved. -/
theorem normalize {N : ℕ} (hn : 3≤N) {S : Finset Point} (card : S.card=N) :
    ∃ f : Fin N→Point, Function.Injective f ∧ (∀ i,dist (f i) 0≤1) ∧
      (∀ i j,dist (f i) (f j)≤1) ∧ (∃ i j,dist (f i) (f j)=1) ∧
      SimilarImage S f ∧ maxAngle (diagram f)=maxAngle S := by
  classical
  let _ : NeZero N := ⟨by omega⟩
  let E : Fin N ≃ S := (Fintype.equivFinOfCardEq (by simpa using card)).symm
  let x (i : Fin N) : Point := E i
  have xi : Function.Injective x := fun _ _ h=>E.injective (Subtype.ext h)
  have mem (i : Fin N) : x i∈S := (E i).property
  have sur {v : Point} (hv : v∈S) : ∃i,x i=v := by
    obtain ⟨i,eq⟩:=E.surjective ⟨v,hv⟩
    exact ⟨i,congrArg Subtype.val eq⟩
  obtain ⟨z,_,great⟩:=Finset.exists_max_image (Finset.univ : Finset (Fin N×Fin N))
    (fun p=>dist (x p.1) (x p.2)) Finset.univ_nonempty
  let D:=dist (x z.1) (x z.2)
  have far (i j) : dist (x i) (x j)≤D := great (i,j) (Finset.mem_univ _)
  let u : Fin N:=⟨0,by omega⟩
  let v : Fin N:=⟨1,by omega⟩
  have uv : u≠v := by intro e; have := congrArg Fin.val e; norm_num [u,v] at this
  have dp : 0<D := lt_of_lt_of_le (dist_pos.mpr (xi.ne uv)) (far u v)
  let f (i : Fin N) : Point:=D⁻¹ • (x i-x z.1)
  have dif (i j) : f i-f j=D⁻¹ • (x i-x j) := by
    dsimp [f]
    rw [←smul_sub]
    congr 1
    abel
  have scale (i j) : dist (f i) (f j)=D⁻¹*dist (x i) (x j) := by
    rw [dist_eq_norm,dif,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr dp),dist_eq_norm]
  have inside (i j) : dist (f i) (f j)≤1 := by
    rw [scale,←inv_mul_cancel₀ dp.ne']
    exact mul_le_mul_of_nonneg_left (far i j) (inv_pos.mpr dp).le
  have inj : Function.Injective f := by
    intro i j eq
    by_contra ne
    have h:=mul_pos (inv_pos.mpr dp) (dist_pos.mpr (xi.ne ne))
    rw [←scale,eq,dist_self] at h
    exact lt_irrefl _ h
  have obs (i j k) : EuclideanGeometry.angle (f i) (f j) (f k)=EuclideanGeometry.angle (x i) (x j) (x k) := by
    change angle (f i-f j) (f k-f j)=angle (x i-x j) (x k-x j)
    rw [dif,dif,angle_smul_left_of_pos _ _ (inv_pos.mpr dp),angle_smul_right_of_pos _ _ (inv_pos.mpr dp)]
  have fm (i) : f i∈diagram f := Finset.mem_image_of_mem _ (Finset.mem_univ i)
  have zero : f z.1=0 := by simp [f]
  have sim : SimilarImage S f := by
    refine ⟨x z.1,mem z.1,D,dp,?_⟩
    ext p
    constructor
    · intro hp
      obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hp
      exact Finset.mem_image_of_mem _ (mem i)
    · intro hp
      obtain ⟨q,hq,eq⟩:=Finset.mem_image.mp hp
      obtain ⟨i,rfl⟩:=sur hq
      rw [←eq]
      exact fm i
  refine ⟨f,inj,fun i=>zero ▸ inside i z.1,inside,⟨z.1,z.2,?_⟩,sim,le_antisymm ?_ ?_⟩
  · rw [scale]
    exact inv_mul_cancel₀ dp.ne'
  · apply maxAngle_le (maxAngle_nonneg _)
    intro a ha b hb c hc ab ac bc
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp ha
    obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hb
    obtain ⟨k,_,rfl⟩:=Finset.mem_image.mp hc
    rw [obs]
    exact angle_le_maxAngle (mem i) (mem j) (mem k)
      (xi.ne (fun h=>ab (congrArg f h))) (xi.ne (fun h=>ac (congrArg f h))) (xi.ne (fun h=>bc (congrArg f h)))
  · apply maxAngle_le (maxAngle_nonneg _)
    intro a ha b hb c hc ab ac bc
    obtain ⟨i,rfl⟩:=sur ha
    obtain ⟨j,rfl⟩:=sur hb
    obtain ⟨k,rfl⟩:=sur hc
    rw [←obs]
    exact angle_le_maxAngle (fm i) (fm j) (fm k)
      (inj.ne (fun h=>ab (congrArg x h))) (inj.ne (fun h=>ac (congrArg x h))) (inj.ne (fun h=>bc (congrArg x h)))

/-- Any given sequence of ordinary N-point configurations has a diameter-normalized
subsequence whose labels converge to a diagram still of diameter one. -/
theorem compact_subsequence {N : ℕ} (hn : 3≤N) (S : ℕ→Finset Point) (card : ∀ n,(S n).card=N) :
    ∃ f : ℕ→Fin N→Point, (∀ n,Function.Injective (f n)) ∧
      (∀ n,SimilarImage (S n) (f n)) ∧ (∀ n,maxAngle (diagram (f n))=maxAngle (S n)) ∧
      ∃ k : ℕ→ℕ,StrictMono k ∧ ∃ L : Fin N→Point, (∀ i,dist (L i) 0≤1) ∧
      (∀ i j,dist (L i) (L j)≤1) ∧ (∃ i j,dist (L i) (L j)=1) ∧
      ∀ i,Tendsto (fun n=>f (k n) i) atTop (𝓝 (L i)) := by
  classical
  choose f inj bound upper diam sim same using fun n=>normalize hn (card n)
  obtain ⟨L,lb,k,mono,conv⟩:=(isCompact_closedBall (0 : Fin N→Point) 1).tendsto_subseq
    (show ∀ n,f n∈Metric.closedBall 0 1 from fun n=>(dist_pi_le_iff (by norm_num : (0:ℝ)≤1)).mpr (bound n))
  have coord (i : Fin N) : Tendsto (fun n=>f (k n) i) atTop (𝓝 (L i)) :=
    (continuous_apply i).continuousAt.tendsto.comp conv
  have lu (i j) : dist (L i) (L j)≤1 :=
    le_of_tendsto ((coord i).dist (coord j)) (Filter.Eventually.of_forall (fun n=>upper (k n) i j))
  have pair : ∃ i j,dist (L i) (L j)=1 := by
    by_contra! ne
    have small (i j) : ∀ᶠ n in atTop,dist (f (k n) i) (f (k n) j)<1 :=
      ((coord i).dist (coord j)).eventually_lt tendsto_const_nhds (lt_of_le_of_ne (lu i j) (ne i j))
    obtain ⟨n,all⟩:=(Filter.eventually_all.mpr (fun i=>Filter.eventually_all.mpr (small i))).exists
    obtain ⟨a,b,eq⟩:=diam (k n)
    exact (ne_of_lt (all a b)) eq
  exact ⟨f,inj,sim,same,k,mono,L,(dist_pi_le_iff (by norm_num : (0:ℝ)≤1)).mp lb,lu,pair,coord⟩

/-- Normalized labeled near-minimizers subconverge jointly. The limit still has diameter one. -/
theorem compact_limit {N : ℕ} (hn : 3≤N) :
    ∃ L : Fin N→Point, (∀ i,dist (L i) 0≤1) ∧
      (∀ i j,dist (L i) (L j)≤1) ∧ (∃ i j,dist (L i) (L j)=1) ∧
      ∀ e : ℝ,0<e → ∃ f : Fin N→Point, Function.Injective f ∧
        (∀ i,dist (f i) (L i)<e) ∧ maxAngle (diagram f)<alpha N+e := by
  classical
  let d (n : ℕ) : ℝ:=1/((n:ℝ)+1)
  have pos (n) : 0<d n := by dsimp [d];positivity
  have zero : Tendsto d atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose S card near using fun n=>exists_configuration_maxAngle_lt hn (lt_add_of_pos_right (alpha N) (pos n))
  obtain ⟨f,inj,sim,same,k,mono,L,lb,lu,pair,coord⟩:=compact_subsequence hn S card
  refine ⟨L,lb,lu,pair,?_⟩
  intro e ep
  have each (i) : ∀ᶠ n in atTop,dist (f (k n) i) (L i)<e :=
    Metric.tendsto_nhds.mp (coord i) e ep
  have dn:= (zero.comp mono.tendsto_atTop).eventually_lt tendsto_const_nhds ep
  obtain ⟨n,close,sm⟩:=((Filter.eventually_all.mpr each).and dn).exists
  refine ⟨f (k n),inj _,close,?_⟩
  rw [same]
  change d (k n)<e at sm
  linarith [near (k n)]

end R57.Compact
#print axioms R57.Compact.normalize
#print axioms R57.Compact.compact_subsequence
#print axioms R57.Compact.compact_limit
