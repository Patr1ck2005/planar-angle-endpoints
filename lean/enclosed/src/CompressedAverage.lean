import AverageStrata
import RowCompression

noncomputable section
namespace R42.CompressedAverage
open Real JSP404 R37.Seventeen R37.SignedFan R40.EvenTail
open R41.MovingStrata R41.SweepWord

/- The phase-cell and disjoint charging steps are the finite arguments in AverageStrata.
We need them for abstract rows since a common rational contraction may collapse bearings. -/
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

def chartEnd {V : Type*} (G : V → Row) (x : V → ℕ → ℝ) (m : ℕ) (v : V) (i : ℕ) :=
  if i<(G v).n then x v (i+1) else x v 0+m

/-- Rotational averaging survives every common monotone direction contraction,
including zero-length inter-bearing cells and both endpoints of the seam. -/
theorem chart_average {V : Type*} [Fintype V] {m s : ℕ} (hm : 0<m) (G : V → Row)
    (cnt : ∀ v, (G v).switches=s) (x : V → ℕ → ℝ)
    (bd : ∀ v i, 0≤x v i ∧ x v i≤m) (mono : ∀ v, Monotone (x v))
    (edge : ∀ v u, v≠u → ∃ i j, x v i=x u j ∧ i≤(G v).n ∧ j≤(G u).n ∧ (G v).b i≠(G u).b j)
    {r : ℝ} (hr : 0≤r) (hr' : r≤1)
    (span : ∀ v i, i∈localMarks (G v) → x v i+r≤chartEnd G x m v i) :
    (Fintype.card V:ℝ)*(1-(s:ℝ)*(1-r))≤2*(m.choose s:ℝ) := by
  classical
  let E := (v : V) × ↥(localMarks (G v))
  have ce : Fintype.card E=Fintype.card V*s := by simp [E,Fintype.card_sigma,card_localMarks,cnt]
  let a (e : E) := start (x e.1 e.2.val)
  have starts (e : E) : 0≤a e ∧ a e≤1 := by
    have u := Nat.floor_le (bd e.1 e.2.val).1
    have l := Nat.lt_floor_add_one (x e.1 e.2.val)
    dsimp [a,start]
    constructor <;> linarith
  have density := RotatingBins.arc_coverage a (fun _ => 1-r)
    (B:=(Fintype.card V:ℝ)-2*(m.choose s:ℝ)) (by norm_num : (0:ℝ)<1) starts
    (fun _ => ⟨by linarith,by linarith⟩) (by
      intro t ht ht'
      let c (v : V) (i : ℕ) := ⌊x v i+t⌋₊
      let active (e : E) := RotatingBins.Active 1 (a e) (1-r) t
      letI : DecidablePred active := fun e => by dsimp [active,RotatingBins.Active]; infer_instance
      have mo (v : V) : Monotone (c v) := fun _ _ ij => Nat.floor_mono (by linarith [mono v ij])
      have cb (v : V) (i : ℕ) : c v i≤m := by
        have h : ⌊x v i+t⌋₊<m+1 := (Nat.floor_lt (by linarith [(bd v i).1])).mpr (by push_cast; linarith [(bd v i).2])
        exact Nat.le_of_lt_succ h
      have shared (v u : V) (ne : v≠u) :
          ∃ i j, c v i=c u j ∧ i≤(G v).n ∧ j≤(G u).n ∧ (G v).b i≠(G u).b j := by
        obtain ⟨i,j,e,hi,hj,sg⟩ := edge v u ne
        exact ⟨i,j,by simp [c,e],hi,hj,sg⟩
      have endSlot (v : V) (i : ℕ) : ⌊chartEnd G x m v i+t⌋₊=stop (G v) m (c v) i := by
        by_cases h : i<(G v).n
        · simp [chartEnd,stop,h,c]
        · simp only [chartEnd,stop,h,ite_false,c]
          rw [add_right_comm,Nat.floor_add_natCast (add_nonneg (bd v 0).1 ht.le)]
      have valid (v : V) (i : ℕ) (hi : i∈localMarks (G v)) (off : ¬active ⟨v,⟨i,hi⟩⟩) :
          c v i<stop (G v) m (c v) i := by
        rw [←endSlot]
        by_contra! bad
        exact off (missed (bd v i).1 (span v i hi) ⟨ht,ht'⟩ bad)
      have bound := charge hm G cnt c mo cb shared active valid
      have real : (Fintype.card V:ℝ)≤2*(m.choose s:ℝ)+((Finset.univ.filter active).card:ℝ) := by exact_mod_cast bound
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

/-- General finite-mark compression followed by the physical signed-stratum average.
The rational rounding and the finite vertex count are the only arithmetic premises. -/
theorem finite_mark_average {S : Finset Point} {V : Type*} [Fintype V]
    (f : V ↪ S) {lam : ℝ} (hl : 0<lam) (F : S → Row) (profile : IsProfile S lam F)
    (m s p q : ℕ) (hm : 0<m) (hq : 0<q) (mpq : m*p≤q) (cnt : ∀ v, (F (f v)).switches=s)
    (rounding : ∀ A B : ℕ, A≤Fintype.card V*s → (A:ℝ)≤(B:ℝ)*(π/lam) →
      (p:ℤ)*A-(q:ℤ)*B≤0) :
    (Fintype.card V:ℝ)*(1-(s:ℝ)*(1-(m:ℝ)*p/q))≤2*(m.choose s:ℝ) := by
  classical
  let G (v : V) := F (f v)
  have cs (v : V) : (G v).switches=s := cnt v
  obtain ⟨C,bd,mo,gap,wrap,shared⟩ := R37.RowCompression.positions G p q hl
    (fun v => (profile (f v)).2) (fun A B h h' => rounding A B (by simpa [cs] using h) h')
  have qp : 0<(q:ℝ) := by exact_mod_cast hq
  have mp : 0≤(m:ℝ) := by positivity
  let x (v : V) (i : ℕ) := (m:ℝ)*(C v i:ℝ)/q
  apply chart_average hm G cs x
  · intro v i
    have l : (0:ℝ)≤C v i := by exact_mod_cast (bd v i).1
    have u : (C v i:ℝ)≤q := by exact_mod_cast (bd v i).2
    exact ⟨div_nonneg (mul_nonneg mp l) qp.le,(div_le_iff₀ qp).mpr (mul_le_mul_of_nonneg_left u mp)⟩
  · intro v i j ij
    have h : (C v i:ℝ)≤C v j := by exact_mod_cast mo v ij
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h mp) qp.le
  · intro v u ne
    obtain ⟨i,j,e,sg⟩ := shared_chord profile (f v) (f u) (fun h => ne (f.injective h))
    have ia : (G v).idx i.val=i := Fin.ext (min_eq_left (Nat.le_of_lt_succ i.isLt))
    have jb : (G u).idx j.val=j := Fin.ext (min_eq_left (Nat.le_of_lt_succ j.isLt))
    have same := shared v u i.val j.val (by simpa only [Row.u,ia,jb] using e)
    exact ⟨i.val,j.val,by simp [x,same],Nat.le_of_lt_succ i.isLt,Nat.le_of_lt_succ j.isLt,
      by simpa only [Row.b,ia,jb] using sg⟩
  · positivity
  · apply (div_le_one qp).mpr
    exact_mod_cast mpq
  · intro v i hi
    have cases : (i<(G v).n ∧ (G v).step i=1) ∨ (i=(G v).n ∧ (G v).seam=1) := by
      by_cases e : (G v).seam=1 <;> simp [localMarks,e] at hi <;> grind
    rcases cases with ⟨hn,sw⟩|⟨rfl,sw⟩
    · have gi := gap v i hn
      simp [sw] at gi
      have gr : (p:ℝ)≤(C v (i+1):ℝ)-C v i := by exact_mod_cast gi
      simp only [chartEnd,hn,ite_true,x,←add_div,div_le_div_iff_of_pos_right qp]
      nlinarith [mul_nonneg mp (sub_nonneg.mpr gr)]
    · have gi := wrap v
      simp [sw] at gi
      have gr : (p:ℝ)≤(q:ℝ)-C v (G v).n+C v 0 := by exact_mod_cast gi
      simp only [chartEnd,lt_irrefl,ite_false,x]
      field_simp
      nlinarith [mul_nonneg mp (sub_nonneg.mpr gr)]

end R42.CompressedAverage
#print axioms R42.CompressedAverage.chart_average
#print axioms R42.CompressedAverage.finite_mark_average
