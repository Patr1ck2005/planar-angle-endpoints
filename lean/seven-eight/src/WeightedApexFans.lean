import ClosedSixtyWindow
import InteriorRigidity
import ExtremeCount
import CollisionSpectrum

noncomputable section
namespace R95.Heavy
open JSP404 Real InnerProductGeometry R54.GapTest R55.WeightedCollision R92.Tight

/-- Four distinct centers suffice for the local statement. The positive
microscopic dimension is exactly one, and there is an actual 30-degree
bisector for all the outgoing rays at that site. -/
theorem heavy_site {I : Type*} [Fintype I] {c : I→Point} (ci : Function.Injective c)
    {w : I→ℕ} (A : Admissible w c (2*π/3)) (many : 4≤Fintype.card I)
    (i : I) (heavy : 2≤w i) :
    dim w i=1 ∧ w i=2 ∧ ∃v : Point,v≠0 ∧ ∀j,j≠i→angle v (c j-c i)≤π/6 := by
  classical
  obtain ⟨_,mac,v,unit,inter,out⟩:=A
  have positive : 0<dim w i:=Nat.clog_pos (by decide) (by omega)
  let b : Fin (dim w i):=⟨0,positive⟩
  have nz (k : Fin (dim w i)) : v i k≠0:=by intro z;simpa [z] using unit i k
  obtain ⟨t,_,_,ref⟩:=polar _ (nz b)
  let J:={j : I // j≠i}
  let u (j : J):=c j.val-c i
  have cardJ : Fintype.card J=Fintype.card I-1:=by simp [J,Fintype.card_subtype_compl]
  have wc (j : J) := window ref (sub_ne_zero.mpr (ci.ne j.property))
    (fun r hr=>out i j j.property.symm b r hr)
  choose a lo hi line using wc
  have inj : Function.Injective a:=by
    intro j k eq
    by_contra ne
    apply R93.Interior.different_axes ci (by linarith [pi_pos] : 2*π/3<π) mac j.property k.property
      (fun e=>ne (Subtype.ext e))
    exact same_of_bearing (eq ▸ line j) (line k)
  obtain ⟨p,pl,pr⟩:=interior_label (by omega : 3≤Fintype.card J) a inj lo hi
  have one : dim w i=1:=by
    by_contra bad
    have enough : 1<dim w i:=by omega
    let k : Fin (dim w i):=⟨1,enough⟩
    have ne : b≠k:=by intro e;have h:=congrArg Fin.val e;norm_num [b,k] at h
    obtain ⟨z,zl,zh,Z⟩:=window ref (nz k) (fun r hr=>by simpa using inter i b k ne r 1 hr (Or.inr rfl))
    have small : |z-a p|<π/3:=abs_lt.mpr ⟨by linarith,by linarith⟩
    have sep:=apart Z (line p) (small.le.trans (by linarith [pi_pos])) (δ:=π/3)
      (fun r hr=>by linarith only [out i p p.property.symm k r hr])
    linarith
  have weight:=Nat.le_pow_clog (by decide : 1<2) (w i)
  change w i≤2^(dim w i) at weight
  rw [one,pow_one] at weight
  obtain ⟨u0,un,all⟩:=narrow_fan (u:=u) lo hi line p pl pr (fun j ne=>
    mac j i p j.property (fun e=>ne (Subtype.ext e)) p.property.symm)
  exact ⟨one,le_antisymm weight heavy,u0,un,fun j ji=>all ⟨j,ji⟩⟩

/-- Under the attainable 120-degree cap every site of a five-or-more-site
support has weight one or two. The inward bisector has half-width at most
(π−wᵢπ/3)/2, simultaneously for all sites. -/
theorem physical_fans {I : Type*} [Fintype I] {c : I→Point} (ci : Function.Injective c)
    {w : I→ℕ} (wp : ∀i,0<w i) (many : 5≤Fintype.card I)
    (hit : 2*π/3∈attainable w c) :
    (∀i,w i≤2) ∧ ∃v : I→Point,(∀i,v i≠0) ∧
      ∀i j,i≠j→angle (v i) (c j-c i)≤(π-(w i:ℝ)*(π/3))/2 := by
  classical
  let : Nontrivial I:=Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have A:=(R54.Profile.fixed_profile wp (fun j=>exists_ne j) ci).mp hit
  have each (i : I) : w i≤2 ∧ ∃v : Point,v≠0 ∧
      ∀j,j≠i→angle v (c j-c i)≤(π-(w i:ℝ)*(π/3))/2 := by
    by_cases heavy : 2≤w i
    · obtain ⟨_,eq,v,vn,h⟩:=heavy_site ci A (by omega) i heavy
      refine ⟨eq.le,v,vn,?_⟩
      intro j ji
      rw [eq];push_cast;linarith only [h j ji]
    · have one : w i=1:=by have:=wp i;omega
      have vertex : c i∉convexHull ℝ (c '' {j | j≠i}) :=by
        intro inside
        have:=R91.Rigid.four_sites ci inside A.2.1
        omega
      obtain ⟨v,vn,h⟩:=R89.Hull.vertex_fan ci (by positivity) A.2.1 i vertex
      refine ⟨by omega,v,vn,?_⟩
      intro j ji
      rw [one];push_cast;linarith only [h j ji]
  choose v nz fan using fun i=>(each i).2
  exact ⟨fun i=>(each i).1,v,nz,fun i j ij=>fan i j ij.symm⟩

end R95.Heavy
#print axioms R95.Heavy.heavy_site
#print axioms R95.Heavy.physical_fans
