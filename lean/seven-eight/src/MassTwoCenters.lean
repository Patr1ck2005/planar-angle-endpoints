import MassWitness
import TwoCenterCard
noncomputable section
namespace R53.Mass
open JSP404 R51.TwoCenters R53.Islands R52.TwoAnchor InnerProductGeometry Real Filter Topology

theorem of_byCard {N k : ℕ} (total : 5*2^k<N) {u : ℝ} (hu : u∈byCard N) :
    u∈scores N (highClass k) := by
  classical
  obtain ⟨r,s,sz,rt,sp,sr,f,c,d,cd,left,right,inj,cap⟩:=hu
  let i₀ : Fin r:=⟨0,by omega⟩
  let j₀ : Fin s:=⟨0,sp⟩
  let L (i : Fin r) := (Sum.inl i : Labels r s)
  let R (j : Fin s) := (Sum.inr j : Labels r s)
  let v:=d-c
  have nz : v≠0 := sub_ne_zero.mpr cd.symm
  intro e ep
  have near (j : Fin s) (i : Fin r) : ∀ᶠ t in 𝓝[>] (0:ℝ),
      angle (f t (R j)-f t (L i₀)) (f t (R j)-f t (L i))<e := by
    have pair : Tendsto (fun t=>(f t (R j)-f t (L i₀),f t (R j)-f t (L i))) (𝓝[>] 0) (𝓝 (v,v)) :=
      ((right j).sub (left i₀)).prodMk_nhds ((right j).sub (left i))
    have ang:=(InnerProductGeometry.continuousAt_angle (x:=(v,v)) nz nz).tendsto.comp pair
    change Tendsto (fun t=>angle (f t (R j)-f t (L i₀)) (f t (R j)-f t (L i))) _ (𝓝 (angle v v)) at ang
    rw [angle_self nz] at ang
    exact ang.eventually_lt tendsto_const_nhds ep
  have all := Filter.eventually_all.mpr (fun j=>Filter.eventually_all.mpr (near j))
  obtain ⟨t,it,ct,mt⟩:=(inj.and (all.and (cap e ep))).exists
  let S:=configuration (f t)
  let F:=Finset.univ.image (fun i=>f t (L i))
  have sz' : S.card=N := by
    rw [show S=Finset.univ.image (f t) from rfl,Finset.card_image_of_injective _ it,Finset.card_univ]
    simpa [Labels] using sz.symm
  have memL (i : Fin r) : f t (L i)∈F := Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have inR : f t (R j₀)∈S := Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have outR : f t (R j₀)∉F := by
    rintro h
    obtain ⟨i,_,hi⟩:=Finset.mem_image.mp h
    have eq : (Sum.inl i : Labels r s)=Sum.inr j₀ := it hi
    cases eq
  have sub : F⊆S := by
    intro x hx
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hx
    exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have island : Island S F (f t (L i₀)) e := by
    refine ⟨sub,memL _,ep.le,?_⟩
    intro p hp x hx
    obtain ⟨ps,pf⟩:=Finset.mem_sdiff.mp hp
    obtain ⟨z,_,rfl⟩:=Finset.mem_image.mp ps
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hx
    cases z with
    | inl m=> exact (pf (memL m)).elim
    | inr j=> exact (ct j i).le
  have sizeF : F.card=r := by
    rw [show F=Finset.univ.image (fun i=>f t (L i)) from rfl,Finset.card_image_of_injective]
    · simp
    · exact it.comp Sum.inl_injective
  have large : 2*2^k<F.card := by omega
  exact ⟨S,sz',mt,Or.inl ⟨F,f t (L i₀),island,⟨_,Finset.mem_sdiff.mpr ⟨inR,outR⟩⟩,large⟩⟩

theorem high_witness {N k : ℕ} (lo : 5*2^k<N) (hi : N≤8*2^k) :
    π-π/((k:ℝ)+3)∈scores N (highClass k) := by
  have p:=Nat.one_le_pow k 2 (by decide)
  have hu:=of_byCard lo (sharp_by_card (N:=N) (by omega)).1
  have count : Nat.clog 2 N≤k+3 := by apply Nat.clog_le_of_le_pow;rw [pow_add];norm_num;omega
  have real : (Nat.clog 2 N:ℝ)≤(k:ℝ)+3 := by exact_mod_cast count
  have pos : 0<(Nat.clog 2 N:ℝ) := by exact_mod_cast (Nat.clog_pos (by decide : 1<2) (show 1<N by omega))
  intro e ep
  obtain ⟨S,sz,mt,cl⟩:=hu e ep
  exact ⟨S,sz,by linarith [div_le_div_of_nonneg_left pi_pos.le pos real],cl⟩

end R53.Mass
#print axioms R53.Mass.high_witness
