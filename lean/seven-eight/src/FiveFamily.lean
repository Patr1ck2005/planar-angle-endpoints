import FiveRows
import FiveAngles
noncomputable section
namespace R64.Five
open Real JSP404 R54.GapTest R54.ProfileFormula R55.WeightedCollision

def weight (n : ℕ) (_ : Fin 5) : ℕ := 2^(n-2)
def size (n : ℕ) : ℕ := 5*2^(n-2)
def dyadic (N : ℕ) : ℝ := π-π/(Nat.clog 2 N:ℝ)

theorem mass (n : ℕ) : (∑ i,weight n i)=size n := by simp [weight,size]

theorem five_attainable {n : ℕ} (hn : 16≤n) :
    π-defect n ∈ attainable (weight n) (point (defect n)) := by
  apply (fixed_centers_iff (chart n) (injective _) (front _) (back _) (w:=weight n)
    (fun _=>Nat.two_pow_pos _) _).mpr
  have h:=(macro_iff _ (injective _) _).mp (five_maxAngle hn).le
  refine Or.inr ⟨h.1,h.2,fun i=>?_⟩
  rw [sub_sub_cancel,five_score hn]
  exact (Nat.clog_pow 2 _ (by decide)).le

theorem size_clog {n : ℕ} (hn : 2≤n) : Nat.clog 2 (size n)=n+1 := by
  obtain ⟨k,rfl⟩:=Nat.exists_eq_add_of_le hn
  have pos : 0 < (2:ℕ)^k := by positivity
  have eq : 2+k-2=k := by omega
  have a : 2^(2+k) < size (2+k) := by simp only [size,eq,pow_add];omega
  have b : size (2+k)≤2^(2+k+1) := by simp only [size,eq,pow_add];norm_num;omega
  have lower := (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).mpr a
  have upper := Nat.clog_le_of_le_pow b
  omega

theorem below_dyadic {n : ℕ} (hn : 16≤n) : π-defect n < dyadic (size n) := by
  unfold dyadic defect
  rw [size_clog (by omega : 2≤n),Nat.cast_add,Nat.cast_one]
  have smaller : π/((n:ℝ)+1) < π/((n:ℝ)+3/4) := by
    apply div_lt_div_of_pos_left pi_pos (by positivity)
    linarith
  linarith

/-- Ordinary, distinct planar points can be taken arbitrarily close to the five labelled centers. -/
theorem ordinary_near {n : ℕ} (hn : 16≤n) {ε : ℝ} (ep : 0 < ε) :
    ∃ f : Label (weight n)→Point, Function.Injective f ∧
      (∀ a,dist (f a) (point (defect n) a.1)<ε) ∧
      (points f).card=size n ∧ maxAngle (points f)<dyadic (size n) := by
  let margin:=dyadic (size n)-(π-defect n)
  have mg : 0 < margin:=sub_pos.mpr (below_dyadic hn)
  obtain ⟨f,inj,near,h⟩:=five_attainable hn (min ε margin) (lt_min ep mg)
  refine ⟨f,inj,fun i=>(near i).trans_le (min_le_left _ _),(card inj).trans (mass n),?_⟩
  have e:=min_le_right ε margin
  dsimp [margin] at e h
  linarith

theorem ordinary_below {n : ℕ} (hn : 16≤n) :
    ∃ S : Finset Point,S.card=5*2^(n-2) ∧ maxAngle S < dyadic (size n) := by
  obtain ⟨f,_,_,sz,small⟩:=ordinary_near hn (by norm_num : (0:ℝ)<1)
  exact ⟨points f,sz,small⟩

/-- The cardinality threshold in the fixed-shape dyadic theorem cannot depend on five alone. -/
theorem no_uniform_cutoff (K : ℕ) :
    ∃ (c : Fin 5→Point) (w : Fin 5→ℕ) (θ : ℝ), Function.Injective c ∧
      (∀ i,0 < w i) ∧ K≤∑i,w i ∧ θ∈attainable w c ∧ θ < dyadic (∑i,w i) := by
  let n:=K+16
  have hn : 16≤n := by dsimp [n];omega
  have big : K≤size n := by
    have power : n-2 < 2^(n-2) := Nat.lt_two_pow_self
    have idx : K≤n-2 := by dsimp [n];omega
    unfold size
    omega
  exact ⟨point (defect n),weight n,π-defect n,injective _,fun _=>Nat.two_pow_pos _,
    (mass n) ▸ big,five_attainable hn,(mass n) ▸ below_dyadic hn⟩

#print axioms five_attainable
#print axioms ordinary_below
#print axioms no_uniform_cutoff
end R64.Five