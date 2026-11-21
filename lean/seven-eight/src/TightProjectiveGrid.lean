import ClosedIntervalPacking
import AxisChart

noncomputable section
namespace R92.Tight
open Real JSP404 R54.GapTest InnerProductGeometry Finset

/-- Distinct indices specify nonzero projective axes with clearance δ. -/
def Packed {J : Type*} (δ : ℝ) (u : J→Point) : Prop :=
  (∀j,u j≠0) ∧ ∀j k,j≠k → ∀s : ℝ,(s= -1 ∨ s=1) → angle (s • u j) (u k)≤π-δ

def grid {D : ℕ} (t δ : ℝ) (j : Fin D) : ℝ := t+j.val*δ

/-- Fix any member and any real bearing of that member. A tight circle
packing occupies exactly once every site in the half-open projective grid. -/
theorem anchored_lattice {J : Type*} [Fintype J] {D : ℕ} (size : Fintype.card J=D+1)
    {δ : ℝ} (dp : 0<δ) (tight : ((D:ℝ)+1)*δ=π)
    (u : J→Point) (pack : Packed δ u) (j : J) (t : ℝ) (first : Bearing (u j) t) :
    ∃e : J≃Fin (D+1),e j=0 ∧ ∀k,Bearing (u k) (grid t δ (e k)) := by
  classical
  have choose_wall (k : J) : ∃a,t≤a ∧ a≤t+π ∧ Bearing (u k) a ∧ (k=j→a=t) := by
    by_cases eq:k=j
    · subst k;exact ⟨t,le_rfl,by linarith [pi_pos],first,fun _=>rfl⟩
    · obtain ⟨a,lo,hi,H⟩:=lifted_polar _ (pack.1 k) t
      exact ⟨a,lo,hi,H,fun h=>(eq h).elim⟩
  choose a lo hi H anchor using choose_wall
  have span (k l) : |a k-a l|≤π:=abs_le.mpr ⟨by linarith [lo k,hi l],by linarith [hi k,lo l]⟩
  have apart' (k l) (ne : k≠l) : δ≤|a k-a l| := apart (H k) (H l) (span k l) (pack.2 k l ne)
  have ai : Function.Injective a := by
    intro k l e
    by_contra ne
    have bad:=apart' k l ne
    rw [e,sub_self,abs_zero] at bad;linarith
  let S:=univ.image a
  have card : S.card=D+1:=by simp [S,card_image_of_injective _ ai,size]
  have ample (k) : a k≤t+(D:ℝ)*δ := by
    by_cases eq:k=j
    · subst k;rw [anchor _ rfl];linarith [mul_nonneg (Nat.cast_nonneg D (α:=ℝ)) dp.le]
    · have dist:=apart (H k) (bearing_closes first) (abs_le.mpr ⟨by linarith [lo k],by linarith [hi k,pi_pos]⟩)
          (pack.2 k j eq)
      rw [abs_of_nonpos (by linarith [hi k])] at dist
      linarith
  have lim:=R70.EqualPacking.lattice S card (a:=t) (b:=t+(D:ℝ)*δ) (l:=δ)
    (by rintro _ h;obtain ⟨k,_,rfl⟩:=mem_image.mp h;exact ⟨lo k,ample k⟩) (by linarith)
    (by rintro _ hx _ hy lt;obtain ⟨k,_,rfl⟩:=mem_image.mp hx;obtain ⟨l,_,rfl⟩:=mem_image.mp hy
        simpa only [abs_of_pos (sub_pos.mpr lt)] using apart' l k (fun h=>lt.ne (congrArg a h.symm)))
  have set_eq : S=univ.image (grid (D:=D+1) t δ):=lim.2
  have site (k) : ∃i : Fin (D+1),grid t δ i=a k := by
    have m : a k∈S:=mem_image_of_mem a (mem_univ k)
    obtain ⟨i,_,e⟩:=mem_image.mp (set_eq ▸ m)
    exact ⟨i,e⟩
  choose idx val using site
  have gi : Function.Injective (grid (D:=D+1) t δ) := by
    intro k l e
    have r : (k.val:ℝ)=(l.val:ℝ):=by unfold grid at e;nlinarith only [e,dp]
    exact Fin.ext (by exact_mod_cast r)
  have bij : Function.Bijective idx := by
    constructor
    · intro k l eq
      exact ai ((val k).symm.trans ((congrArg _ eq).trans (val l)))
    · intro i
      have m : grid t δ i∈S:=set_eq ▸ mem_image_of_mem _ (mem_univ i)
      obtain ⟨k,_,eq⟩:=mem_image.mp m
      exact ⟨k,gi ((val k).trans eq)⟩
  let e:=Equiv.ofBijective idx bij
  refine ⟨e,gi (show grid t δ (idx j)=grid t δ 0 by rw [val,anchor _ rfl];simp [grid]),?_⟩
  intro k
  change Bearing (u k) (grid t δ (idx k))
  rw [val];exact H k

end R92.Tight
#print axioms R92.Tight.anchored_lattice
