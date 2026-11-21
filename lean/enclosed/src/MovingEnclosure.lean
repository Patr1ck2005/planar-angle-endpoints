import EnclosedRigidity
import Mathlib.Analysis.Convex.Combination

noncomputable section
namespace R94.Enclosed
open JSP404 Real Filter Topology R55.WeightedCollision

/-- Barycentric coefficients indexed by the fixed labels, including possible
zero coefficients. This representation survives motion of all vertices. -/
theorem coefficients {J : Type*} [Fintype J] {u : J→Point} {x : Point}
    (inside : x∈convexHull ℝ (Set.range u)) :
    ∃ p : J→ℝ,(∀j,0≤p j) ∧ ∑j,p j=1 ∧ ∑j,p j • u j=x := by
  classical
  rw [convexHull_range_eq_exists_affineCombination] at inside
  obtain ⟨s,w,pos,one,rep⟩:=inside
  let p (j : J) := if j∈s then w j else 0
  refine ⟨p,fun j=>by by_cases h:j∈s <;> simp [p,h,pos],?_,?_⟩
  · simpa [p] using one
  · rw [affineCombination_eq_centerMass one,Finset.centerMass_eq_of_sum_1 _ _ one] at rep
    simpa [p,ite_smul] using rep

/-- Closedness of membership in the convex hull of moving finite labeled
vertices. Neither nondegeneracy nor a fixed affine basis is required. -/
theorem hull_limit {J : Type*} [Fintype J] {u : ℕ→J→Point} {v : J→Point}
    {x : ℕ→Point} {y : Point} (uc : ∀j,Tendsto (fun n=>u n j) atTop (𝓝 (v j)))
    (xc : Tendsto x atTop (𝓝 y)) (inside : ∀n,x n∈convexHull ℝ (Set.range (u n))) :
    y∈convexHull ℝ (Set.range v) := by
  classical
  choose p pos one rep using fun n=>coefficients (inside n)
  let C : Set (J→ℝ):=Set.univ.pi fun _=>Set.Icc (0:ℝ) 1
  have K : IsCompact C:=isCompact_univ_pi fun _=>isCompact_Icc
  have mem (n : ℕ) : p n∈C := by
    intro j _
    refine ⟨pos n j,?_⟩
    rw [←one n]
    exact Finset.single_le_sum (fun i _=>pos n i) (Finset.mem_univ j)
  obtain ⟨a,ha,f,inc,lim⟩:=K.tendsto_subseq mem
  have cv (j : J):=tendsto_pi_nhds.mp lim j
  have sm : Tendsto (fun n=>∑j,p (f n) j) atTop (𝓝 (∑j,a j)) :=
    tendsto_finsetSum _ fun j _=>cv j
  have sv : Tendsto (fun n=>∑j,p (f n) j • u (f n) j) atTop (𝓝 (∑j,a j • v j)) :=
    tendsto_finsetSum _ fun j _=>(cv j).smul ((uc j).comp inc.tendsto_atTop)
  exact mem_convexHull_of_exists_fintype a v (fun j=>(ha j (Set.mem_univ j)).1)
    (tendsto_nhds_unique sm (by simpa only [one] using (tendsto_const_nhds (x:=(1:ℝ)))))
    (fun j=>Set.mem_range_self j)
    (tendsto_nhds_unique sv (by simpa only [rep,Function.comp_apply,Function.comp_def] using xc.comp inc.tendsto_atTop))

/-- The graph of attainable caps is sequentially closed in labeled centers
and cap, directly from the ordinary finite approximation witnesses. -/
theorem attainable_limit {J : Type*} [Fintype J] {w : J→ℕ} {c : ℕ→J→Point} {b : J→Point}
    {u : ℕ→ℝ} {B : ℝ} (cc : ∀j,Tendsto (fun n=>c n j) atTop (𝓝 (b j)))
    (uc : Tendsto u atTop (𝓝 B)) (hit : ∀n,u n∈attainable w (c n)) :
    B∈attainable w b := by
  intro ε ep
  have hp : 0<ε/2:=by linarith
  have near (j : J) := Metric.tendsto_nhds.mp (cc j) (ε/2) hp
  obtain ⟨n,cl,small⟩:=((eventually_all.mpr near).and
    (uc.eventually_lt tendsto_const_nhds (show B<B+ε/2 by linarith))).exists
  obtain ⟨f,inj,rad,cap⟩:=hit n (ε/2) hp
  refine ⟨f,inj,fun a=>?_,by linarith⟩
  exact (dist_triangle _ (c n a.1) _).trans_lt (by linarith [rad a,cl a.1])

end R94.Enclosed
#print axioms R94.Enclosed.hull_limit
#print axioms R94.Enclosed.attainable_limit
