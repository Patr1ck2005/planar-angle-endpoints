import PhysicalSweep
import SweepWord
import RotatingBins
import EvenTail

noncomputable section
namespace R42.Average
open Real JSP404 R37.Seventeen R37.SignedFan R40.EvenTail
open R41.MovingStrata R41.SweepWord R41.PhysicalSweep

private def start (x : ℝ) := (⌊x⌋₊:ℝ)+1-x

private theorem missed {x y r t : ℝ} (hx : 0≤x) (span : x+r≤y)
    (ht : 0<t ∧ t<1) (miss : ⌊y+t⌋₊≤⌊x+t⌋₊) :
    RotatingBins.Active 1 (start x) (1-r) t := by
  have flo := Nat.floor_le hx
  have ceil := Nat.lt_floor_add_one x
  have low := Nat.floor_le (by linarith : 0≤x+t)
  have limit := Nat.lt_floor_add_one (y+t)
  have mm : (⌊y+t⌋₊:ℝ)≤(⌊x+t⌋₊:ℝ) := by exact_mod_cast miss
  have lower : ⌊x⌋₊≤⌊x+t⌋₊ := Nat.floor_mono (by linarith)
  have upper : ⌊x+t⌋₊<⌊x⌋₊+2 := (Nat.floor_lt (by linarith)).mpr (by push_cast; linarith)
  rcases (show ⌊x+t⌋₊=⌊x⌋₊ ∨ ⌊x+t⌋₊=⌊x⌋₊+1 by omega) with e|e
  · right
    rw [e] at low mm
    dsimp [start]
    constructor <;> linarith
  · left
    rw [e] at low mm
    push_cast at low mm
    dsimp [start]
    constructor <;> linarith

/-- For every phase, each vertex can be charged either to one compatible
word or to a missing grid boundary in one of its registered switch gaps. -/
private theorem charge {V : Type*} [Fintype V] {s m : ℕ} (hm : 0<m) (F : V → Row)
    (cnt : ∀ v, (F v).switches=s) (c : V → ℕ → ℕ) (mono : ∀ v, Monotone (c v))
    (bound : ∀ v i, c v i≤m)
    (edge : ∀ v u, v≠u → ∃ i j, c v i=c u j ∧ i≤(F v).n ∧ j≤(F u).n ∧ (F v).b i≠(F u).b j)
    (active : ((v : V) × ↥(localMarks (F v))) → Prop) [DecidablePred active]
    (gap : ∀ v i (hi : i∈localMarks (F v)), ¬active ⟨v,⟨i,hi⟩⟩ → c v i<stop (F v) m (c v) i) :
    Fintype.card V ≤ 2*m.choose s+(Finset.univ.filter active).card := by
  classical
  let E := (v : V) × ↥(localMarks (F v))
  let bad (v : V) := ∃ e : E, active e ∧ e.1=v
  have safe (v : V) (h : ¬bad v) : Good (F v) m (c v) (c v) := by
    intro i hi
    exact ⟨le_rfl,gap v i hi (fun eh => h ⟨⟨v,⟨i,hi⟩⟩,eh,rfl⟩)⟩
  have cert (v : V) (h : ¬bad v) := canonical (F v) hm _ _ (mono v) (bound v) (safe v h)
  let word (v : V) (h : ¬bad v) : Word m s :=
    (⟨marked (F v) hm (c v),(cert v h).1.trans (cnt v)⟩,polarity (F v) m (c v))
  let enc (v : V) : Word m s ⊕ {e : E // active e} :=
    if h : bad v then Sum.inr ⟨h.choose,h.choose_spec.1⟩ else Sum.inl (word v h)
  have inj : Function.Injective enc := by
    intro v u eq
    by_cases hv : bad v <;> by_cases hu : bad u
    · have e : hv.choose=hu.choose := by simpa [enc,hv,hu,Subtype.ext_iff] using eq
      exact hv.choose_spec.2.symm.trans ((congrArg Sigma.fst e).trans hu.choose_spec.2)
    · simp [enc,hv,hu] at eq
    · simp [enc,hv,hu] at eq
    · have he : word v hv=word u hu := by simpa [enc,hv,hu] using eq
      by_contra ne
      obtain ⟨i,j,p,hi,hj,sg⟩ := edge v u ne
      have one : polarity (F v) m (c v)=polarity (F u) m (c u) := congrArg Prod.snd he
      have two : marked (F v) hm (c v)=marked (F u) hm (c u) := congrArg (fun z => z.1.val) he
      have left := (cert v hv).2 i hi
      have right := (cert u hu).2 j hj
      rw [one,two,p,right] at left
      exact sg left.symm
  have card : Fintype.card (Word m s)=2*m.choose s := by simp [Word,Layer,Fintype.card_finset_len,Nat.mul_comm]
  simpa only [Fintype.card_sum,card,Fintype.card_subtype] using Fintype.card_le_of_injective enc inj

/-- Geometry for an arbitrary uniform lower gap-to-bin ratio r<=1.
Bounds hold in every actual stratum, including one-switch support rows. -/
theorem stratum_average {m : ℕ} (hm : 0<m) {lam r : ℝ} (hr : 0≤r) (hr' : r≤1)
    (ratio : r*(π/(m:ℝ))≤lam) (S : Finset Point) (F : S → Row) (profile : IsProfile S lam F)
    (s : ℕ) : (census F s:ℝ)*(1-(s:ℝ)*(1-r)) ≤ 2*(m.choose s:ℝ) := by
  classical
  let K := Finset.univ.filter (fun v : S => (F v).switches=s)
  let G (v : K) := F v.val
  let E := (v : K) × ↥(localMarks (G v))
  have cnt (v : K) : (G v).switches=s := (Finset.mem_filter.mp v.property).2
  have ck : Fintype.card K=census F s := Fintype.card_coe _
  have ce : Fintype.card E=census F s*s := by simp [E,Fintype.card_sigma,card_localMarks,cnt,show K.card=census F s from rfl]
  let w := π/(m:ℝ)
  have mp : 0<(m:ℝ) := by exact_mod_cast hm
  have wp : 0<w := div_pos pi_pos mp
  have per : (m:ℝ)*w=π := by dsimp [w]; field_simp
  have period : π/w=(m:ℝ) := (div_eq_iff wp.ne').mpr per.symm
  let x (v : K) (i : ℕ) := (G v).u i/w
  let y (v : K) (i : ℕ) := endPos (G v) i/w
  have xpos (v : K) (i : ℕ) : 0≤x v i := div_nonneg ((G v).bounds ((G v).idx i)).1 wp.le
  have xmax (v : K) (i : ℕ) : x v i<(m:ℝ) :=
    (div_lt_iff₀ wp).mpr (by rw [per]; exact ((G v).bounds ((G v).idx i)).2)
  have span (v : K) (i : ℕ) (hi : i∈localMarks (G v)) : x v i+r≤y v i := by
    have cases : (i<(G v).n ∧ (G v).step i=1) ∨ (i=(G v).n ∧ (G v).seam=1) := by
      by_cases e : (G v).seam=1 <;> simp [localMarks,e] at hi <;> grind
    have leg := (profile v.val).2
    change (G v).Legal lam at leg
    have hh : lam≤endPos (G v) i-(G v).u i := by
      rcases cases with ⟨hn,sw⟩|⟨rfl,sw⟩
      · simpa [endPos,hn,sw] using (G v).step_budget leg i
      · have h := (G v).seam_budget leg
        simp [sw] at h
        simp [endPos]; linarith
    change r*w≤lam at ratio
    dsimp [x,y]
    rw [←le_sub_iff_add_le',←sub_div,le_div_iff₀ wp]
    linarith
  let a (e : E) := start (x e.1 e.2.val)
  have starts (e : E) : 0≤a e ∧ a e≤1 := by
    have u := Nat.floor_le (xpos e.1 e.2.val)
    have l := Nat.lt_floor_add_one (x e.1 e.2.val)
    dsimp [a,start]
    constructor <;> linarith
  have density := RotatingBins.arc_coverage a (fun _ => 1-r)
    (B:=(census F s:ℝ)-2*(m.choose s:ℝ)) (by norm_num : (0:ℝ)<1) starts
    (fun _ => ⟨by linarith,by linarith⟩) (by
      intro t ht ht'
      let c (v : K) (i : ℕ) := ⌊x v i+t⌋₊
      let active (e : E) := RotatingBins.Active 1 (a e) (1-r) t
      letI : DecidablePred active := fun e => by dsimp [active,RotatingBins.Active]; infer_instance
      have mono (v : K) : Monotone (c v) := by
        intro i j ij
        apply Nat.floor_mono
        have ord : (G v).u i≤(G v).u j :=
          (G v).sorted.monotone (show (G v).idx i≤(G v).idx j from min_le_min_right _ ij)
        dsimp [x]
        linarith [div_le_div_of_nonneg_right ord wp.le]
      have bd (v : K) (i : ℕ) : c v i≤m := by
        have h : ⌊x v i+t⌋₊<m+1 := (Nat.floor_lt (by linarith [xpos v i])).mpr (by push_cast; linarith [xmax v i])
        exact Nat.le_of_lt_succ h
      have share (v u : K) (ne : v≠u) :
          ∃ i j, c v i=c u j ∧ i≤(G v).n ∧ j≤(G u).n ∧ (G v).b i≠(G u).b j := by
        have vn : v.val≠u.val := fun ee => ne (Subtype.ext ee)
        obtain ⟨i,j,bear,sg⟩ := shared_chord profile _ _ vn
        have ia : (G v).idx i.val=i := Fin.ext (min_eq_left (Nat.le_of_lt_succ i.isLt))
        have jb : (G u).idx j.val=j := Fin.ext (min_eq_left (Nat.le_of_lt_succ j.isLt))
        refine ⟨i.val,j.val,?_,Nat.le_of_lt_succ i.isLt,Nat.le_of_lt_succ j.isLt,?_⟩
        · change (G v).bearing i=(G u).bearing j at bear
          simp [c,x,Row.u,ia,jb,bear]
        · simpa only [Row.b,ia,jb] using sg
      have endSlot (v : K) (i : ℕ) : ⌊y v i+t⌋₊=stop (G v) m (c v) i := by
        by_cases h : i<(G v).n
        · simp [y,endPos,stop,h,c,x]
        · simp only [y,endPos,stop,h,ite_false,add_div,period,c,x]
          rw [add_right_comm,Nat.floor_add_natCast (add_nonneg (xpos v 0) ht.le)]
      have valid (v : K) (i : ℕ) (hi : i∈localMarks (G v)) (off : ¬active ⟨v,⟨i,hi⟩⟩) :
          c v i<stop (G v) m (c v) i := by
        rw [←endSlot]
        by_contra! bad
        exact off (missed (xpos v i) (span v i hi) ⟨ht,ht'⟩ bad)
      have bound := charge hm G cnt c mono bd share active valid
      rw [ck] at bound
      have real : (census F s:ℝ)≤2*(m.choose s:ℝ)+((Finset.univ.filter active).card:ℝ) := by exact_mod_cast bound
      have nn : ((Finset.univ.filter active).card:ℝ)=∑ e : E, (if active e then (1:ℝ) else 0) := by
        rw [Finset.card_filter]
        push_cast
        apply Finset.sum_congr rfl
        intro e _
        split_ifs <;> norm_num
      rw [nn] at real
      change _≤∑ e : E, (if active e then (1:ℝ) else 0)
      linarith)
  simp only [mul_one,Finset.sum_const,Finset.card_univ,ce,nsmul_eq_mul,Nat.cast_mul] at density
  linarith

end R42.Average
#print axioms R42.Average.stratum_average
