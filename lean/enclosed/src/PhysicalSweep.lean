import MovingStrata
import Mathlib.Data.Prod.Lex

noncomputable section
namespace R41.PhysicalSweep
open Real R37.Seventeen R37.SignedFan R41.MovingStrata

def endPos (F : Row) (i : ℕ) := if i<F.n then F.u (i+1) else F.u 0+π

private theorem gap_width {F : Row} {lam : ℝ} (leg : F.Legal lam) (i : ℕ) (hi : i∈localMarks F) :
    lam≤endPos F i-F.u i := by
  have cases : (i<F.n ∧ F.step i=1) ∨ (i=F.n ∧ F.seam=1) := by
    by_cases e : F.seam=1 <;> simp [localMarks,e] at hi <;> grind
  rcases cases with ⟨hn,sw⟩|⟨rfl,sw⟩
  · simpa [endPos,hn,sw] using F.step_budget leg i
  · have h := F.seam_budget leg
    simp [sw] at h
    simp [endPos]
    linarith

private theorem moment {x y : ℝ} (hx : 0≤x) (gap : x+1<y) :
    ∃ z : ℝ, 0<z ∧ z<1 ∧ ∀ t : ℝ, 0≤t → t≤1 →
      (t≤z → ⌊x+t⌋₊≤⌊x⌋₊ ∧ ⌊x⌋₊<⌊y+t⌋₊) ∧
      (z≤t → ⌊x+t⌋₊≤⌊x⌋₊+1 ∧ ⌊x⌋₊+1<⌊y+t⌋₊) := by
  let a := (⌊x⌋₊:ℝ)+1-x
  let b := max 0 ((⌊x⌋₊:ℝ)+2-y)
  have lo := Nat.floor_le hx
  have hi := Nat.lt_floor_add_one x
  have aa : 0<a := by dsimp [a]; linarith
  have au : a≤1 := by dsimp [a]; linarith
  have bn : 0≤b := le_max_left _ _
  have bb : b<a := max_lt aa (by dsimp [a]; linarith)
  have bl : (⌊x⌋₊:ℝ)+2-y≤b := le_max_right _ _
  refine ⟨(b+a)/2,by linarith,by linarith,?_⟩
  intro t ht ht'
  have xt : 0≤x+t := by linarith
  constructor
  · intro z
    constructor
    · have e : ⌊x+t⌋₊<⌊x⌋₊+1 := (Nat.floor_lt xt).mpr (by push_cast; dsimp [a] at *; linarith)
      omega
    · apply Nat.le_floor
      push_cast
      linarith
  · intro z
    constructor
    · have e : ⌊x+t⌋₊<⌊x⌋₊+1+1 := (Nat.floor_lt xt).mpr (by push_cast; linarith)
      omega
    · apply Nat.le_floor
      push_cast
      linarith

structure Schedule {V : Type*} [Fintype V] (m s : ℕ) (F : V → Row) where
  q : ℕ
  size : q=Fintype.card V*s
  c : ℕ → V → ℕ → ℕ
  r : ℕ → V → ℕ → ℕ
  mono : ∀ k v, Monotone (c k v)
  bd : ∀ k v i, c k v i≤m
  shared : ∀ k v u i j, (F v).u i=(F u).u j → c k v i=c k u j
  good : ∀ k v, Good (F v) m (c k v) (r k v)
  next : ∀ k v, Good (F v) m (c k v) (r (k+1) v)
  step : ∀ k, k<q → ∃ v i, i∈localMarks (F v) ∧ r (k+1) v i≠r k v i ∧
    ∀ u, u≠v → ∀ j ∈ localMarks (F u), r (k+1) u j=r k u j
  low : ∀ v i, r 0 v i<m
  endEq : ∀ v i, i∈localMarks (F v) → r q v i=r 0 v i+1

/-- Every individual true switch supplies one move. Tied phases can be
ordered arbitrarily since both adjacent choices are legal at equality. -/
theorem schedule {V : Type*} [Fintype V] {m s : ℕ} (hm : 0<m) {lam : ℝ}
    (margin : π/(m:ℝ)<lam) (F : V → Row) (leg : ∀ v, (F v).Legal lam)
    (size : ∀ v, (F v).switches=s) : Nonempty (Schedule m s F) := by
  classical
  let w := π/(m:ℝ)
  have mp : 0<(m:ℝ) := by exact_mod_cast hm
  have wp : 0<w := div_pos pi_pos mp
  have per : (m:ℝ)*w=π := by dsimp [w]; field_simp
  have rat : π/w=(m:ℝ) := (div_eq_iff wp.ne').mpr per.symm
  let x (v : V) (i : ℕ) := (F v).u i/w
  let y (v : V) (i : ℕ) := endPos (F v) i/w
  let E := (v : V) × ↥(localMarks (F v))
  let q := Fintype.card E
  have sz : q=Fintype.card V*s := by
    simp [q,E,Fintype.card_sigma,card_localMarks,size]
  have xpos (v : V) (i : ℕ) : 0≤x v i := div_nonneg ((F v).bounds ((F v).idx i)).1 wp.le
  have xmax (v : V) (i : ℕ) : x v i<(m:ℝ) :=
    (div_lt_iff₀ wp).mpr (by rw [per]; exact ((F v).bounds ((F v).idx i)).2)
  have g (e : E) : x e.1 e.2.val+1<y e.1 e.2.val := by
    have big := gap_width (leg e.1) e.2.val e.2.property
    dsimp [x,y]
    rw [←div_self wp.ne',←add_div,div_lt_div_iff_of_pos_right wp]
    linarith
  choose z pos lt1 choices using fun e : E => moment (xpos e.1 e.2.val) (g e)
  let labels : Fin q ≃ E := (Fintype.equivFin E).symm
  let key (e : E) : ℝ ×ₗ Fin q := (z e,labels.symm e)
  have ki : Function.Injective key := fun _ _ eq => labels.symm.injective (congrArg (fun p : ℝ ×ₗ Fin q => (ofLex p).2) eq)
  letI : LinearOrder E := LinearOrder.lift' key ki
  let so := (Finset.univ : Finset E).orderIsoOfFin (show Finset.univ.card=q from Finset.card_univ)
  let forget : ↥(Finset.univ : Finset E) ≃ E := ⟨Subtype.val,fun e => ⟨e,Finset.mem_univ _⟩,fun _ => rfl,fun _ => rfl⟩
  let order : Fin q ≃ E := so.toEquiv.trans forget
  have increasing : Monotone (z ∘ order) := by
    intro a b e
    have hh := so.monotone e
    exact Prod.Lex.monotone_fst (key (order a)) (key (order b)) hh
  let t (k : ℕ) := if h : k<q then z (order ⟨k,h⟩) else 1
  have ts (k : ℕ) : 0≤t k ∧ t k≤1 := by
    unfold t
    split
    · exact ⟨(pos _).le,(lt1 _).le⟩
    · norm_num
  let c (k : ℕ) (v : V) (i : ℕ) := ⌊x v i+t k⌋₊
  let seed (v : V) (i : ℕ) := ⌊x v i⌋₊
  let r (k : ℕ) (v : V) (i : ℕ) :=
    if hi : i∈localMarks (F v) then
      if (order.symm ⟨v,⟨i,hi⟩⟩).val<k then seed v i+1 else seed v i
    else seed v i
  have endSlot (k : ℕ) (v : V) (i : ℕ) :
      ⌊y v i+t k⌋₊=stop (F v) m (c k v) i := by
    by_cases h : i<(F v).n
    · simp [y,endPos,stop,h,c,x]
    · simp only [y,endPos,stop,h,ite_false,add_div,rat,c,x]
      rw [add_right_comm,Nat.floor_add_natCast (add_nonneg (xpos v 0) (ts k).1)]
  have compatible (k l : ℕ) (kl : k≤l) (lk : l≤k+1) (v : V) :
      Good (F v) m (c k v) (r l v) := by
    intro i hi
    let e : E := ⟨v,⟨i,hi⟩⟩
    rw [←endSlot]
    simp only [r,hi,dif_pos]
    by_cases eq : (order.symm e).val<l
    · have past : z e≤t k := by
        by_cases h : k<q
        · have hh := increasing (show order.symm e≤(⟨k,h⟩:Fin q) from by change (order.symm e).val≤k; omega)
          simpa [t,h] using hh
        · simpa [t,h] using (lt1 e).le
      simpa [e,eq,c,seed] using (choices e (t k) (ts k).1 (ts k).2).2 past
    · have h : k<q := by have := (order.symm e).isLt; omega
      have fut : t k≤z e := by
        have hh := increasing (show (⟨k,h⟩:Fin q)≤order.symm e from by change k≤(order.symm e).val; omega)
        simpa [t,h] using hh
      simpa [e,eq,c,seed] using (choices e (t k) (ts k).1 (ts k).2).1 fut
  refine ⟨⟨q,sz,c,r,?_,?_,?_,fun k v => compatible k k le_rfl (by omega) v,
    fun k v => compatible k (k+1) (by omega) le_rfl v,?_,?_,?_⟩⟩
  · intro k v i j ij
    apply Nat.floor_mono
    have h : (F v).u i≤(F v).u j :=
      (F v).sorted.monotone (show (F v).idx i≤(F v).idx j from min_le_min_right _ ij)
    dsimp [x]
    linarith [div_le_div_of_nonneg_right h wp.le]
  · intro k v i
    have hh : ⌊x v i+t k⌋₊<m+1 := (Nat.floor_lt (add_nonneg (xpos _ _) (ts _).1)).mpr
      (by push_cast; linarith [(ts k).2,xmax v i])
    exact Nat.le_of_lt_succ hh
  · intro k v u i j eq
    simp [c,x,eq]
  · intro k hk
    let p : Fin q := ⟨k,hk⟩
    let e := order p
    refine ⟨e.1,e.2.val,e.2.property,?_,?_⟩
    · have back : order.symm ⟨e.1,⟨e.2.val,e.2.property⟩⟩=p := order.symm_apply_apply p
      change order.symm e=p at back
      simp [r,e.2.property,back,p]
    · intro u ne j hj
      let b : E := ⟨u,⟨j,hj⟩⟩
      have diff : (order.symm b).val≠k := by
        intro eq
        have h : order.symm b=p := Fin.ext eq
        have q : b=e := (order.apply_symm_apply b).symm.trans (congrArg order h)
        exact ne (congrArg Sigma.fst q)
      by_cases lt : (order.symm b).val<k
      · have next : (order.symm b).val<k+1 := by omega
        simp only [r,hj,dif_pos]
        change (if (order.symm b).val<k+1 then _ else _) = if (order.symm b).val<k then _ else _
        simp [lt,next]
      · have next : ¬(order.symm b).val<k+1 := by omega
        simp only [r,hj,dif_pos]
        change (if (order.symm b).val<k+1 then _ else _) = if (order.symm b).val<k then _ else _
        simp [lt,next]
  · intro v i
    simpa [r,seed] using (Nat.floor_lt (xpos v i)).mpr (xmax v i)
  · intro v i hi
    have lt := (order.symm ⟨v,⟨i,hi⟩⟩).isLt
    simp [r,hi,lt]

end R41.PhysicalSweep
#print axioms R41.PhysicalSweep.schedule
