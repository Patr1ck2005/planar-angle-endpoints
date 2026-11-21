import ProfileSamples
noncomputable section
namespace R54.Profile
open JSP404 Real Filter Topology InnerProductGeometry R51.Anchored R56.Rounding R56.Decorated

theorem approximating_axes {I : Type*} [Fintype I] {w : I→ℕ} {c : I→Point} {θ : ℝ}
    (pos : ∀ i,0<w i) (other : ∀ i : I,∃ j,j≠i) (ci : Function.Injective c) (R : Realizable w c θ)
    {e : ℝ} (ep : 0<e) (slack : θ+2*e<π) :
    ∃ b : I→Point,(∀ i,dist (b i) (c i)<e) ∧
      ∃ V : Axes b (fun i=>Nat.clog 2 (w i)) (θ+2*e),∀ i j,‖V.v i j‖=1 := by
  classical
  obtain ⟨f,inj,close,cap,view⟩:=samples pos ci R ep
  let b (i : I) := f (rep pos i)
  let S:=diagram f
  let piece (i : I) := Finset.univ.image (fun x : Fin (w i)=>f ⟨i,x⟩)
  have sub (i : I) : piece i⊆S := by
    intro x hx
    obtain ⟨y,_,rfl⟩:=Finset.mem_image.mp hx
    exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have am (i : I) : b i∈piece i := Finset.mem_image_of_mem _ (Finset.mem_univ (⟨0,pos i⟩ : Fin (w i)))
  have ext (i j : I) (ne : i≠j) : b j∉piece i := by
    rintro h
    obtain ⟨x,_,eq⟩:=Finset.mem_image.mp h
    exact ne (congrArg Sigma.fst (inj eq))
  have cone (i j : I) (ne : i≠j) : InCone (piece i) (b j) (b j-b i) e := by
    intro p hp
    obtain ⟨x,_,rfl⟩:=Finset.mem_image.mp hp
    exact (view i j ne x).le
  have sz (i : I) : (piece i).card=w i := by
    rw [show piece i=Finset.univ.image (fun x : Fin (w i)=>f ⟨i,x⟩) from rfl,Finset.card_image_of_injective]
    · simp
    · intro x y eq;exact eq_of_heq (Sigma.mk.inj (inj eq)).2
  have sl : 0<π-maxAngle S-e := by change maxAngle S<θ+e at cap;linarith
  have one (i : I) : ∃ v : Fin (Nat.clog 2 (w i))→Point, (∀ x,‖v x‖=1) ∧
      (∀ x y,x≠y → ∀ r s : ℝ,(r= -1 ∨ r=1) → (s= -1 ∨ s=1) →
        angle (r • v x) (s • v y)≤θ+2*e) ∧
      ∀ j,i≠j → ∀ x (r : ℝ),(r= -1 ∨ r=1) → angle (r • v x) (b j-b i)≤θ+2*e := by
    obtain ⟨j,jne⟩:=other i
    have sel:=select_axes (sub i) (am i) ep.le sl ⟨b j,sub j (am j),ext i j jne.symm,cone i j jne.symm⟩
    rw [sz i] at sel
    obtain ⟨v,nv,int,cross⟩:=sel
    have bound : maxAngle S+e≤θ+2*e := by change maxAngle S<θ+e at cap;linarith
    exact ⟨v,nv,fun x y ne r s hr hs=>(int x y ne r s hr hs).trans bound,
      fun j ne x r hr=>(cross _ (sub j (am j)) (ext i j ne) (cone i j ne) x r hr).trans bound⟩
  choose v norm int cross using one
  exact ⟨b,fun i=>close _,⟨v,fun i j h=>by simpa [h] using norm i j,int,cross⟩,norm⟩

end R54.Profile
#print axioms R54.Profile.approximating_axes
