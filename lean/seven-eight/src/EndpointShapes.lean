import TwoEndpointSites
import FourInteriorMass

noncomputable section
namespace R90.Endpoint
open Real JSP404 R55.WeightedCollision Finset

/-- Four or more extreme sites have total capacity at most six at 120 degrees. -/
theorem extreme_six {I : Type*} [Fintype I] [Nontrivial I] {c : I→Point}
    (ci : Function.Injective c) {w : I→ℕ} (wp : ∀i,0<w i) (four : 4≤Fintype.card I)
    (all : ∀i,c i∉convexHull ℝ (c '' {j | j≠i})) (hit : 2*π/3∈attainable w c) :
    (∑i,w i)≤6 := by
  have A:=(R54.Profile.fixed_profile wp (fun j=>exists_ne j) ci).mp hit
  have count : Fintype.card I≤∑i,w i:=by
    simpa using (sum_le_sum (s:=univ) (fun i _=>show 1≤w i from wp i))
  have small (i):w i≤2:=(R96.Endpoint.weight_le_two ci (by omega) A i).2
  have room (i) : (w i:ℝ)*(π/3)≤π:=by
    have h : (w i:ℝ)≤2:=by exact_mod_cast small i
    nlinarith only [mul_le_mul_of_nonneg_right h pi_pos.le,pi_pos]
  have fans (i) : ∃u:Point,u≠0 ∧ ∀j,j≠i→InnerProductGeometry.angle u (c j-c i)≤(π-(w i:ℝ)*(π/3))/2 := by
    by_cases heavy : 2≤w i
    · obtain ⟨_,eq,u,nz,cap⟩:=R95.Heavy.heavy_site ci A four i heavy
      refine ⟨u,nz,fun j ne=>?_⟩;rw [eq];push_cast;linarith [cap j ne]
    · have eq : w i=1:=by have:=wp i;omega
      obtain ⟨u,nz,cap⟩:=R89.Hull.vertex_fan ci (by positivity) A.2.1 i (all i)
      refine ⟨u,nz,fun j ne=>?_⟩;rw [eq];push_cast;linarith [cap j ne]
  have cap:=R90.Aperture.weighted_fans c w (by omega) (by positivity : 0<π/3) room fans
  by_contra! large
  have n : (7:ℝ)≤(∑i,w i:ℕ):=by exact_mod_cast large
  nlinarith only [cap,mul_le_mul_of_nonneg_right n pi_pos.le,pi_pos]

theorem support_shape {I : Type*} [Fintype I] [Nontrivial I] {c : I→Point}
    (ci : Function.Injective c) {w : I→ℕ} (wp : ∀i,0<w i)
    (many : 7≤∑i,w i) (hit : 2*π/3∈attainable w c) :
    Fintype.card I=2 ∨ (Fintype.card I=4 ∧ (∑i,w i)=7 ∧
      ∃i,c i∈convexHull ℝ (c '' {j | j≠i}) ∧ w i=1 ∧ ∀j,j≠i→w j=2) := by
  classical
  have upper:=support_at_most_four ci wp many hit
  have lower:=Fintype.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial I)
  by_cases two : Fintype.card I=2
  · exact Or.inl two
  have A:=(R54.Profile.fixed_profile wp (fun j=>exists_ne j) ci).mp hit
  have small (i):w i≤2:=(R96.Endpoint.weight_le_two ci (by omega) A i).2
  have cap : (∑i,w i)≤Fintype.card I*2:=by simpa using sum_le_sum (s:=univ) (fun i _=>small i)
  have four : Fintype.card I=4:=by omega
  by_cases all : ∀i,c i∉convexHull ℝ (c '' {j | j≠i})
  · have z:=extreme_six ci wp four.ge all hit;omega
  push Not at all
  obtain ⟨i,inside⟩:=all
  obtain ⟨mass,one,exactAt⟩:=R96.Endpoint.four_mass ci wp four hit i inside
  have eq:=le_antisymm mass many
  exact Or.inr ⟨four,eq,i,inside,one,(exactAt eq).1⟩

/-- At N=8 every normalized attainable endpoint support has precisely two
macroscopic sites carrying four labels each. Both sites may be prescribed. -/
theorem eight_shape {I : Type*} [Fintype I] [Nontrivial I] {c : I→Point}
    (ci : Function.Injective c) {w : I→ℕ} (wp : ∀i,0<w i) (eight : (∑i,w i)=8)
    (hit : 2*π/3∈attainable w c) : Fintype.card I=2 ∧ ∀i,w i=4 := by
  obtain two|impossible:=support_shape ci wp (by omega) hit
  · refine ⟨two,fun i=>?_⟩
    have small:=at_most_four_labels ci wp hit
    apply le_antisymm (small i)
    by_contra! less
    have h:=sum_lt_sum (s:=univ) (fun j _=>small j) ⟨i,mem_univ _,less⟩
    simp [eight,two] at h
  · omega

/-- At N=7 the two-site split is 3+4. Any other endpoint support consists
of three doubled outer sites surrounding a single site of weight one. -/
theorem seven_shape {I : Type*} [Fintype I] [Nontrivial I] {c : I→Point}
    (ci : Function.Injective c) {w : I→ℕ} (wp : ∀i,0<w i) (seven : (∑i,w i)=7)
    (hit : 2*π/3∈attainable w c) :
    (∃e : Fin 2≃I,w (e 0)=3 ∧ w (e 1)=4) ∨ (Fintype.card I=4 ∧
      ∃i,c i∈convexHull ℝ (c '' {j | j≠i}) ∧ w i=1 ∧ ∀j,j≠i→w j=2) := by
  obtain two|⟨four,_,rest⟩:=support_shape ci wp seven.ge hit
  · let e:Fin 2≃I:=(Fintype.equivFinOfCardEq two).symm
    have h : (∑j,w (e j))=7:=(e.sum_comp w).trans seven
    simp only [Fin.sum_univ_two] at h
    have l:=at_most_four_labels ci wp hit (e 0)
    have r:=at_most_four_labels ci wp hit (e 1)
    left
    by_cases eq : w (e 0)=3
    · exact ⟨e,eq,by omega⟩
    · let g:=(Equiv.swap (0:Fin 2) 1).trans e
      refine ⟨g,?_,?_⟩ <;> simp [g] <;> omega
  · exact Or.inr ⟨four,rest⟩
end R90.Endpoint
#print axioms R90.Endpoint.extreme_six
#print axioms R90.Endpoint.support_shape
#print axioms R90.Endpoint.eight_shape
#print axioms R90.Endpoint.seven_shape
