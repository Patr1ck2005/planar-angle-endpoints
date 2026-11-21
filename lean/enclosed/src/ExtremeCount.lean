import DiameterRays
import Jsp000404.CircleSeparation
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.Convex.Topology
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality

noncomputable section
namespace R89.Hull
open JSP404 Real Finset InnerProductGeometry R55.WeightedCollision R87.Diameter
open scoped RealInnerProductSpace

/-- A vertex of the finite hull has a bisector which makes angle at most θ/2
with every chord into the set. No cyclic labeling of the hull is required. -/
theorem vertex_fan {I : Type*} [Fintype I] [Nontrivial I] {c : I→Point}
    (ci : Function.Injective c) {θ : ℝ} (pos : 0≤θ) (mac : Macro c θ)
    (i : I) (vertex : c i∉convexHull ℝ (c '' {j | j≠i})) :
    ∃u:Point,u≠0 ∧ ∀j,j≠i→angle u (c j-c i)≤θ/2 := by
  classical
  let P:=c '' {j | j≠i}
  have finite : P.Finite:=(Set.toFinite _).image c
  obtain ⟨a,ai⟩:=exists_ne i
  have point (j) (ne : j≠i) : c j∈convexHull ℝ P:=subset_convexHull ℝ P ⟨j,ne,rfl⟩
  have convex:=convex_convexHull ℝ P
  obtain ⟨q,member,least⟩:=exists_norm_eq_iInf_of_complete_convex ⟨_,point a ai⟩
    (finite.isClosed_convexHull ℝ).isComplete convex (c i)
  let v:=q-c i
  have vn : v≠0:=sub_ne_zero.mpr (fun eq=>vertex (eq ▸ member))
  have normal:=(norm_eq_iInf_iff_real_inner_le_zero convex member).mp least
  have dot (j) (ne : j≠i) : 0<⟪v,c j-c i⟫ := by
    have h:=normal (c j) (point j ne)
    rw [show c i-q= -v by dsimp [v];abel,inner_neg_left] at h
    rw [show c j-c i=(c j-q)+v by dsimp [v];abel,inner_add_right]
    have own : 0<⟪v,v⟫:=real_inner_self_pos.mpr vn
    linarith
  obtain ⟨t,T⟩:=head_exists vn
  let J:={j : I // j≠i}
  let : Nonempty J:=⟨⟨a,ai⟩⟩
  choose b lo hi ray using fun j : J=>acute_head T (sub_ne_zero.mpr (ci.ne j.property))
    (lt_of_not_ge (fun bad=> (dot j j.property).not_ge (inner_nonpos_iff_pi_div_two_le_angle.mpr bad)))
  obtain ⟨l,_,minL⟩:=exists_min_image univ b univ_nonempty
  obtain ⟨r,_,maxR⟩:=exists_max_image univ b univ_nonempty
  have span {j k : J} : |b j-b k|≤π:=abs_le.mpr ⟨by linarith [lo j,hi k],by linarith [lo k,hi j]⟩
  have width : b r-b l≤θ := by
    by_cases eq : l=r
    · simpa [eq] using pos
    · have h:=mac l i r l.property (fun e=>eq (Subtype.ext e)) r.property.symm
      change angle (c l-c i) (c r-c i)≤θ at h
      rw [head_angle (ray l) (ray r) span,abs_of_nonpos (sub_nonpos.mpr (minL r (mem_univ _)))] at h
      linarith
  let mid:=(b l+b r)/2
  let u:=circleDirection mid
  have U : Head u mid:=⟨1,by norm_num,by simp [u]⟩
  refine ⟨u,?_,?_⟩
  · intro z;have:=norm_circleDirection mid;change ‖u‖=1 at this;simp [z] at this
  · intro j ji
    let k : J:=⟨j,ji⟩
    have minK:=minL k (mem_univ _);have maxK:=maxR k (mem_univ _)
    have bnd : |mid-b k|≤π:=abs_le.mpr ⟨by dsimp [mid];linarith [lo l,lo r,hi k],
      by dsimp [mid];linarith [hi l,hi r,lo k]⟩
    change angle u (c k-c i)≤θ/2
    rw [head_angle U (ray k) bnd]
    apply abs_le.mpr;dsimp [mid];constructor <;> linarith

/-- Any m distinct vertices of the full convex hull consume a total exterior
angular width m(π−θ)≤2π. Interior sites may occur in arbitrary number. -/
theorem vertex_count {I : Type*} [Fintype I] [Nontrivial I] {c : I→Point}
    (ci : Function.Injective c) {θ : ℝ} (pos : 0≤θ) (mac : Macro c θ) {m : ℕ}
    (two : 2≤m) (e : Fin m ↪ I) (vertices : ∀j,c (e j)∉convexHull ℝ (c '' {k | k≠e j})) :
    (m:ℝ)*(π-θ)≤2*π := by
  choose u nz fan using fun j=>vertex_fan ci pos mac (e j) (vertices j)
  apply Jsp404.circle_separation_bound (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation two u nz
  intro i j ne
  have ij:=e.injective.ne ne
  have a:=fan i (e j) ij.symm
  have b:=fan j (e i) ij
  have neg : angle (u j) (c (e j)-c (e i))=π-angle (u j) (c (e i)-c (e j)):=by
    rw [show c (e j)-c (e i)= -(c (e i)-c (e j)) by abel,angle_neg_right]
  have tri:=angle_le_angle_add_angle (u j) (u i) (c (e j)-c (e i))
  rw [neg,angle_comm (u j) (u i)] at tri
  linarith
end R89.Hull
#print axioms R89.Hull.vertex_fan
#print axioms R89.Hull.vertex_count
