import ConvexTotalTurn
import DeleteConvexEar

noncomputable section
namespace R86.ConvexMass
open Real JSP404 R54.GapTest R55.WeightedCollision R56.Windows Finset R65.Retention R85.CriticalMass

/-- An arbitrary nonempty collection of locally affordable ears suffices. -/
theorem eligible_ear {n : ℕ} {c : Site n→Point} (ci : Function.Injective c) (hull : HullOrder c)
    {θ : ℝ} (U : Finset (Site n)) (un : U.Nonempty)
    (budget : (∑j∈univ \ U,exterior c j)+U.card*(2*(π-θ))≤2*π) :
    ∃j∈U,2*(π-θ)≤exterior c j := by
  by_contra! all
  have small:=sum_lt_sum (s:=U) (f:=exterior c) (g:=fun _=>2*(π-θ)) (fun j mem=>(all j mem).le)
    (un.imp fun j hj=>⟨hj,all j hj⟩)
  have add:=sum_sdiff (f:=exterior c) (show U⊆univ from subset_univ U)
  rw [total_turn ci hull] at add
  simp only [sum_const,nsmul_eq_mul] at small
  linarith

/-- The removal and redistribution keep the original positions of all survivors
and all of their original positive fiber weights. -/
theorem weighted_peel {n : ℕ} {c : Site n→Point} (ci : Function.Injective c) (hull : HullOrder c)
    {w : Site n→ℕ} (wp : ∀i,0<w i) {θ : ℝ} (below : θ<π) (hit : θ∈attainable w c)
    {m : Site n→ℕ} (R : ∀i,Row (m i)) (front : Represents R c) (back : Witnessed R c)
    (U : Finset (Site n)) (un : U.Nonempty)
    (cheap : ∀j∈U,mass R θ j≤mass R θ (prev j) ∧ mass R θ j≤mass R θ (next j))
    (budget : (∑j∈univ \ U,exterior c j)+U.card*(2*(π-θ))≤2*π) :
    ∃j∈U,∃u : Fin (n+2)→ℕ,(∀a,w (j.succAbove a)≤u a) ∧ (∑a,u a)=∑a,w a ∧
       θ∈attainable u (c∘j.succAboveEmb) := by
  obtain ⟨j,mem,big⟩:=eligible_ear ci hull U un budget
  obtain ⟨pos,mac,_⟩:=(R54.Profile.fixed_profile wp (fun i=>exists_ne i) ci).mp hit
  obtain ⟨p,Q,fwd,rev⟩:=actual_rows (c∘j.succAboveEmb) (ci.comp j.succAboveEmb.injective)
  have improve:=delete_ear ci hull below mac R front j big (cheap j mem).1 (cheap j mem).2 Q rev
  have fit:=(fits_iff ci R front back pos below mac wp).mp hit
  have total : (∑i,w i)≤capacity R θ := sum_le_sum (s:=univ) (fun i _=>fit i)
  exact ⟨j,mem,(retained_mass_iff ci wp below hit j.succAboveEmb Q fwd rev).mpr (total.trans improve)⟩

/-- Equal true capacities on an arbitrary strictly convex polygon give a
one-site reduction whenever the number of sites times δ is at most π.
Original assigned weights can be unequal. -/
theorem equal_peel {n : ℕ} {c : Site n→Point} (ci : Function.Injective c) (hull : HullOrder c)
    {w : Site n→ℕ} (wp : ∀i,0<w i) {θ : ℝ} (below : θ<π) (hit : θ∈attainable w c)
    {m : Site n→ℕ} (R : ∀i,Row (m i)) (front : Represents R c) (back : Witnessed R c)
    (flat : ∀i,mass R θ i=mass R θ 0) (small : ((n:ℝ)+3)*(π-θ)≤π) :
    ∃j : Site n,∃u : Fin (n+2)→ℕ,(∀a,w (j.succAbove a)≤u a) ∧ (∑a,u a)=∑a,w a ∧
       θ∈attainable u (c∘j.succAboveEmb) := by
  obtain ⟨j,_,u,ok⟩:=weighted_peel ci hull wp below hit R front back univ univ_nonempty
    (fun j _=>⟨((flat j).trans (flat _).symm).le,((flat j).trans (flat _).symm).le⟩) (by
      rw [show (univ \ (univ : Finset (Site n))) = ∅ by ext; simp, sum_empty, zero_add, card_univ, Fintype.card_fin]
      push_cast
      linarith only [small])
  exact ⟨j,u,ok⟩

/-- Up to one heavy exception, the eligible mass class can still have any number
of vertices, and the selected deletion avoids that exceptional site. -/
theorem one_heavy_peel {n : ℕ} {c : Site n→Point} (ci : Function.Injective c) (hull : HullOrder c)
    {w : Site n→ℕ} (wp : ∀i,0<w i) {θ : ℝ} (below : θ<π) (hit : θ∈attainable w c)
    {m : Site n→ℕ} (R : ∀i,Row (m i)) (front : Represents R c) (back : Witnessed R c)
    (x : Site n) (minima : ∀j,j≠x → ∀i,mass R θ j≤mass R θ i)
    (small : 2*((n:ℝ)+2)*(π-θ)≤π) :
    ∃j,j≠x ∧ ∃u : Fin (n+2)→ℕ,(∀a,w (j.succAbove a)≤u a) ∧ (∑a,u a)=∑a,w a ∧
       θ∈attainable u (c∘j.succAboveEmb) := by
  obtain ⟨z,zx⟩:=exists_ne x
  have non : (univ.erase x).Nonempty:=⟨z,mem_erase.mpr ⟨zx,mem_univ _⟩⟩
  have outside : univ \ (univ.erase x)={x} := by ext;simp
  have turn : exterior c x≤π := by unfold exterior;linarith [EuclideanGeometry.angle_nonneg (c (prev x)) (c x) (c (next x))]
  obtain ⟨j,mem,u,ok⟩:=weighted_peel ci hull wp below hit R front back (univ.erase x) non
    (fun j hj=>⟨minima j (mem_erase.mp hj).1 _,minima j (mem_erase.mp hj).1 _⟩) (by
      rw [outside,sum_singleton,card_erase_of_mem (mem_univ x),card_univ,Fintype.card_fin]
      change exterior c x+((n+2:ℕ):ℝ)*(2*(π-θ))≤2*π
      push_cast;linarith only [small,turn])
  exact ⟨j,(mem_erase.mp mem).1,u,ok⟩

end R86.ConvexMass
#print axioms R86.ConvexMass.weighted_peel
#print axioms R86.ConvexMass.equal_peel
#print axioms R86.ConvexMass.one_heavy_peel
