import DecoratedCapacity
import FiniteGapScore
import ThirtyNine

noncomputable section
open scoped Classical
namespace R56.Windows
open JSP404 Real InnerProductGeometry

/-- Row in an arbitrary lifted projective chart. Repeated walls are allowed. -/
structure Row (m : ℕ) where
  w : ℕ → ℝ
  ordered : ∀ {a b}, a≤b → b≤m → w a≤w b
  period : w m=w 0+π

variable {m : ℕ} (R : Row m) {δ : ℝ}

def Row.digits (i : Fin m) (δ : ℝ) : ℕ := ⌊(R.w (i.val+1)-R.w i)/δ⌋₊-1
abbrev Row.Site (δ : ℝ) := (i : Fin m) × Fin (R.digits i δ)
def Row.site (s : R.Site δ) : ℝ := R.w s.1+((s.2.val:ℝ)+1)*δ

theorem Row.local_bounds (dp : 0<δ) (s : R.Site δ) :
    R.w s.1+δ≤R.site s ∧ R.site s≤R.w (s.1.val+1)-δ := by
  have inside := s.2.isLt
  let z := ⌊(R.w (s.1.val+1)-R.w s.1)/δ⌋₊
  change s.2.val<z-1 at inside
  have order := R.ordered (a:=s.1.val) (b:=s.1.val+1) (by omega) (by have h:=s.1.isLt;omega)
  have base : (z:ℝ)≤(R.w (s.1.val+1)-R.w s.1)/δ :=
    Nat.floor_le (div_nonneg (sub_nonneg.mpr order) dp.le)
  have room : s.2.val+2≤z := by omega
  have h : (s.2.val:ℝ)+2≤z := by exact_mod_cast room
  have hi := (le_div_iff₀ dp).mp (h.trans base)
  have pos : 0≤(s.2.val:ℝ)*δ := mul_nonneg (Nat.cast_nonneg _) dp.le
  unfold Row.site
  constructor <;> linarith

theorem Row.global_bounds (dp : 0<δ) (s : R.Site δ) :
    R.w 0+δ≤R.site s ∧ R.site s≤R.w 0+π-δ := by
  have a:=R.local_bounds dp s
  have h:=s.1.isLt
  have b:=R.ordered (a:=0) (b:=s.1.val) (by omega) (by omega)
  have c:=R.ordered (a:=s.1.val+1) (b:=m) (by omega) le_rfl
  rw [R.period] at c
  constructor <;> linarith

private theorem Row.one_left (dp : 0<δ) {a b : R.Site δ} (lt : a.1.val<b.1.val) :
    R.site a+δ≤R.site b := by
  have x:=R.local_bounds dp a
  have y:=R.local_bounds dp b
  have z:=R.ordered (a:=a.1.val+1) (b:=b.1.val) (by omega) b.1.isLt.le
  linarith

theorem Row.pair_apart (dp : 0<δ) {a b : R.Site δ} (ne : a≠b) :
    δ≤|R.site a-R.site b| ∧ |R.site a-R.site b|≤π-δ := by
  have ga:=R.global_bounds dp a
  have gb:=R.global_bounds dp b
  refine ⟨?_,abs_le.mpr ⟨by linarith,by linarith⟩⟩
  rcases lt_trichotomy a.1.val b.1.val with lt|eq|gt
  · rw [abs_sub_comm]
    exact (le_abs_self _).trans' (by linarith [R.one_left dp lt])
  · obtain ⟨i,p⟩:=a
    obtain ⟨j,q⟩:=b
    change i.val=j.val at eq
    obtain rfl : i=j := Fin.ext eq
    have qne : p.val≠q.val := by
      intro e; exact ne (congrArg (Sigma.mk i) (Fin.ext e))
    rcases lt_or_gt_of_ne qne with lt|gt
    · have h : (p.val:ℝ)+1≤q.val := by exact_mod_cast lt
      rw [abs_sub_comm]
      apply (le_abs_self _).trans'
      dsimp [Row.site]
      nlinarith [mul_le_mul_of_nonneg_right h dp.le]
    · have h : (q.val:ℝ)+1≤p.val := by exact_mod_cast gt
      apply (le_abs_self _).trans'
      dsimp [Row.site]
      nlinarith [mul_le_mul_of_nonneg_right h dp.le]
  · exact (le_abs_self _).trans' (by linarith [R.one_left dp gt])

theorem Row.wall_apart (dp : 0<δ) (s : R.Site δ) {j : ℕ} (hj : j≤m) :
    δ≤|R.site s-R.w j| ∧ |R.site s-R.w j|≤π-δ := by
  have x:=R.local_bounds dp s
  have y:=R.global_bounds dp s
  have l:=R.ordered (a:=0) (b:=j) (by omega) hj
  have u:=R.ordered (a:=j) (b:=m) hj le_rfl
  rw [R.period] at u
  refine ⟨?_,abs_le.mpr ⟨by linarith,by linarith⟩⟩
  by_cases h : j≤s.1.val
  · have z:=R.ordered h s.1.isLt.le
    exact (le_abs_self _).trans' (by linarith)
  · have z:=R.ordered (a:=s.1.val+1) (b:=j) (by omega) hj
    rw [abs_sub_comm]
    exact (le_abs_self _).trans' (by linarith)

section
variable {I : Type*} [Fintype I] {m : I→ℕ} (R : ∀ i, Row (m i)) {c : I→Point} {δ : ℝ}

def Represents (R : ∀ i, Row (m i)) (c : I→Point) : Prop :=
  ∀ i j,i≠j → ∃ h≤m i, ∃ z : ℝ, 0<z ∧ ∃ e : ℝ, (e= -1 ∨ e=1) ∧
    c j-c i=z • (e • circleDirection ((R i).w h))

def score (i : I) (δ : ℝ) := R51.Anchored.gapScore (m i) (R i).w δ

private def enumerate (i : I) (δ : ℝ) : Fin (score R i δ) ≃ (R i).Site δ :=
  by
    have card : Fintype.card ((R i).Site δ)=score R i δ := by
      change Fintype.card (Sigma (fun j : Fin (m i) => Fin ((R i).digits j δ)))=_
      rw [Fintype.card_sigma]
      exact Finset.sum_congr rfl (fun j _=>Fintype.card_fin ((R i).digits j δ))
    exact (finCongr card.symm).trans (Fintype.equivFin ((R i).Site δ)).symm

/-- Simultaneous full decoration of every gap of every row. -/
def full_axes (dp : 0<δ) (rep : Represents R c) : R56.Decorated.Axes c (fun i=>score R i δ) (π-δ) where
  v i p:=circleDirection ((R i).site (enumerate R i δ p))
  nonzero i p:=by
    intro eq
    have h:=norm_circleDirection ((R i).site (enumerate R i δ p))
    rw [eq,norm_zero] at h
    exact zero_ne_one h
  internal i p q ne r s hr hs:=by
    have a:=(R i).pair_apart dp (fun eq=>ne ((enumerate R i δ).injective eq))
    exact signed_circleDirection_angle_le_of_separation dp.le a.1 a.2 r s hr hs
  outside i j ne p r hr:=by
    obtain ⟨h,hb,z,hz,e,he,eq⟩:=rep i j ne
    have a:=(R i).wall_apart dp (enumerate R i δ p) hb
    rw [eq,angle_smul_right_of_pos _ _ hz]
    exact signed_circleDirection_angle_le_of_separation dp.le a.1 a.2 r e hr he

theorem capacity_lt (dp : 0<δ) (anglePos : 0≤π-δ) (inj : Function.Injective c)
    (rep : Represents R c) {N : ℕ} (three : 3≤N) (known : π-δ<alpha N)
    (law : ∀ i j k,i≠j → k≠j → EuclideanGeometry.angle (c i) (c j) (c k)≤π-δ) :
    (∑ i,2^score R i δ)<N :=
  R56.Decorated.count_of_alpha inj anglePos three known law (full_axes R dp rep)

theorem capacity_le_38 (below : 2*π/11<δ) (anglePos : 0≤π-δ) (inj : Function.Injective c)
    (rep : Represents R c)
    (law : ∀ i j k,i≠j → k≠j → EuclideanGeometry.angle (c i) (c j) (c k)≤π-δ) :
    (∑ i,2^score R i δ)≤38 := by
  have bd:=capacity_lt R (by linarith [Real.pi_pos] : 0<δ) anglePos inj rep (N:=39)
    (by decide) (by rw [R43.FiniteStrata.alpha_thirty_nine];linarith) law
  omega

end
end R56.Windows
#print axioms R56.Windows.full_axes
#print axioms R56.Windows.capacity_le_38
