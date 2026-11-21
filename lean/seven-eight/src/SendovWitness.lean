import SendovInner

noncomputable section
open Filter Topology
namespace R52.SendovCloud
open Real JSP404
set_option maxHeartbeats 1200000

abbrev Label (k : ℕ) := ClusterWord (threeClusterDims (k+2))
abbrev center (k : ℕ) := threeClusterCenters (k+2)
def representative (k : ℕ) (i : Fin 3) : Label k := ⟨i,fun _ => false⟩
def angleCap (k : ℕ) := π-2*threeClusterPhi (k+2)

theorem cap_formula (k : ℕ) : angleCap k=(1-2/(2*(k:ℝ)+5))*π := by
  unfold angleCap threeClusterPhi
  push_cast
  rw [show 2*((k:ℝ)+2)+1=2*k+5 by ring]
  ring

theorem label_card (k : ℕ) : Fintype.card (Label k)=5*2^k := by
  rw [clusterWord_card,threeCluster_cardinality (n:=k+2) (by omega)]
  simp

structure Realization (k : ℕ) (ε ρ : ℝ) where
  point : Label k → Point
  injective : Function.Injective point
  fixed : ∀ i, point (representative k i)=center k i
  radius : ∀ a j, a.1≠j →
    dist (center k a.1) (point a)<ρ*dist (center k a.1) (center k j)
  angle : maxAngle (Finset.univ.image point)<angleCap k+ε

private theorem outer_angles {I : Type*} [Fintype I] (c x : I → Point)
    (inj : Function.Injective (fun i=>(c i,x i))) {h : ℝ}
    (cap : ∀ a b d, a≠b → d≠b → clusterAngle c x a b d<h) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ a b d, a≠b → d≠b →
      EuclideanGeometry.angle (perturb c x s a) (perturb c x s b) (perturb c x s d)<h := by
  apply Filter.eventually_all.mpr; intro a
  apply Filter.eventually_all.mpr; intro b
  apply Filter.eventually_all.mpr; intro d
  by_cases hab : a=b
  · exact Filter.Eventually.of_forall (by simp [hab])
  by_cases hdb : d=b
  · exact Filter.Eventually.of_forall (by simp [hdb])
  exact ((tendsto_perturb_angle c x inj hab hdb).eventually_lt tendsto_const_nhds
    (cap a b d hab hdb)).mono (fun _ h _ _ => h)

theorem full_witness (k : ℕ) {ε ρ : ℝ} (he : 0<ε) (hr : 0<ρ) :
    Nonempty (Realization k ε ρ) := by
  classical
  let n:=k+2
  have hn : 2≤n := by dsimp [n]; omega
  let v:=threeClusterDirections n
  let cc : Label k → Point:=fun a=>center k a.1
  have hθ : 0≤angleCap k := by
    have h:=threeClusterPhi_lt_half_pi hn
    change 0≤π-2*threeClusterPhi n
    linarith
  have angles:=inner_angles (threeClusterCenters n) (threeClusterCenters_injective n) v
    (threeClusterDirections_ne_zero n) hθ (show 0<ε/2 by positivity)
    (threeClusterCenters_angle_le hn) (threeClusterDirections_internal hn) (threeClusterDirections_cross hn)
  obtain ⟨t,hinj,hangle⟩:=((eventually_injective_center_cluster (threeClusterCenters n)
    (threeClusterCenters_injective n) v (threeClusterDirections_ne_zero n)).and angles).exists
  let x : Label k → Point:=clusterProjection v t
  have outs:=outer_angles cc x hinj hangle
  have rad : ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ (a : Label k) (j : Fin 3), a.1≠j →
      dist (cc a) (perturb cc x s a)<ρ*dist (cc a) (center k j) := by
    apply Filter.eventually_all.mpr; intro a
    apply Filter.eventually_all.mpr; intro j
    by_cases eq : a.1=j
    · exact Filter.Eventually.of_forall (by simp [eq])
    have lim : Tendsto (fun s : ℝ=>perturb cc x s a) (𝓝[>] 0) (𝓝 (cc a)) := by
      have h : Continuous (fun s : ℝ=>cc a+s • x a) := by fun_prop
      have h0:=h.continuousAt (x:=0)
      simpa [perturb] using h0.tendsto.mono_left (nhdsWithin_le_nhds (s:=Set.Ioi (0:ℝ)))
    have hd := (tendsto_const_nhds (x:=cc a)).dist lim
    have nz : 0<ρ*dist (cc a) (center k j) := mul_pos hr
      (dist_pos.mpr ((threeClusterCenters_injective (k+2)).ne eq))
    have ev:=hd.eventually_lt tendsto_const_nhds (by simpa using nz)
    exact ev.mono (fun _ h _=>h)
  obtain ⟨s,inj,ang,close⟩:=((eventually_injective_perturb cc x hinj).and (outs.and rad)).exists
  let f:=perturb cc x s
  refine ⟨{point:=f,injective:=inj,fixed:=?_,radius:=close,angle:=?_}⟩
  · intro i
    simp [f,perturb,cc,x,clusterProjection,representative,binaryProjection,realDigit]
  · have le : maxAngle (Finset.univ.image f)≤angleCap k+ε/2 := by
      apply maxAngle_le (by linarith)
      intro A hA B hB D hD ab ad bd
      obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hA
      obtain ⟨b,_,rfl⟩:=Finset.mem_image.mp hB
      obtain ⟨d,_,rfl⟩:=Finset.mem_image.mp hD
      exact (ang a b d (fun h=>ab (congrArg f h)) (fun h=>bd (congrArg f h.symm))).le
    linarith

#print axioms full_witness
end R52.SendovCloud

