import PlanarProfile
import Mathlib.Tactic

noncomputable section
namespace R40.TopStratum
open Real JSP404 R37.SignedFan
open InnerProductGeometry

/-- A three-ray fan either spans a half-plane or winds once. -/
def Fan (T x y z : ℝ) : Prop :=
  x+y=z ∨ y+z=x ∨ z+x=y ∨ x+y+z=2*T

private theorem abs_turn (a b c : ℝ) :
    |a-b|+|b-c|=|c-a| ∨ |b-c|+|c-a|=|a-b| ∨ |c-a|+|a-b|=|b-c| := by
  by_cases h₁ : 0≤a-b <;> by_cases h₂ : 0≤b-c <;> by_cases h₃ : 0≤c-a <;>
    simp_all [abs_of_nonneg,abs_of_neg,lt_of_not_ge] <;> grind

private theorem row_fan (F : Row) (i j k : Fin (F.n+1)) :
    Fan π (angle (oriented (F.bearing i) (F.sign i)) (oriented (F.bearing j) (F.sign j)))
      (angle (oriented (F.bearing j) (F.sign j)) (oriented (F.bearing k) (F.sign k)))
      (angle (oriented (F.bearing k) (F.sign k)) (oriented (F.bearing i) (F.sign i))) := by
  rw [angle_oriented (F.bounds i) (F.bounds j), angle_oriented (F.bounds j) (F.bounds k),
      angle_oriented (F.bounds k) (F.bounds i)]
  have hd := abs_turn (F.bearing i) (F.bearing j) (F.bearing k)
  rcases hd with h|h|h <;> cases F.sign i <;> cases F.sign j <;> cases F.sign k <;>
    simp [Fan] <;> first | left; linarith | right; left; linarith |
      right; right; left; linarith | right; right; right; linarith

theorem profile_fan (S : Finset Point) (F : S → Row) {lam : ℝ}
    (h : IsProfile S lam F) (a b c d : S) (hb : b≠a) (hc : c≠a) (hd : d≠a) :
    Fan π (EuclideanGeometry.angle (b:Point) a c) (EuclideanGeometry.angle (c:Point) a d)
      (EuclideanGeometry.angle (d:Point) a b) := by
  have ray (p : S) (ne : p≠a) :
      ∃ j, ∃ r : ℝ, 0<r ∧ (p:Point)-a =
        r • oriented ((F a).bearing j) ((F a).sign j) :=
    (h a).1.1 ⟨p,Finset.mem_erase.mpr ⟨fun eq => ne (Subtype.ext eq), p.property⟩⟩
  obtain ⟨i,ri,pi,ei⟩ := ray b hb
  obtain ⟨j,rj,pj,ej⟩ := ray c hc
  obtain ⟨k,rk,pk,ek⟩ := ray d hd
  change Fan π (angle ((b:Point)-a) ((c:Point)-a)) (angle ((c:Point)-a) ((d:Point)-a))
    (angle ((d:Point)-a) ((b:Point)-a))
  rw [ei,ej,ek,angle_smul_left_of_pos _ _ pi,angle_smul_left_of_pos _ _ pj,
    angle_smul_left_of_pos _ _ pk,angle_smul_right_of_pos _ _ pi,
    angle_smul_right_of_pos _ _ pj,angle_smul_right_of_pos _ _ pk]
  exact row_fan _ _ _ _

private def idx (x : ℝ) : ℤ := ⌊x/2⌋
def residual (x : ℝ) : ℝ := x-2*(idx x:ℝ)

theorem residual_bounds {n : ℕ} {T x : ℝ} (hd : T-(n:ℝ)<1)
    (h : FullSwitchTriangle.Band n T x) : 0≤residual x ∧ residual x≤T-(n:ℝ) := by
  obtain ⟨j,hj,hj'⟩ := h
  have he : idx x = (j:ℤ) := by
    apply Int.floor_eq_iff.mpr
    push_cast
    constructor <;> linarith
  dsimp [residual]
  rw [he]
  push_cast
  constructor <;> linarith

private theorem even_zero (k : ℤ) {a : ℝ} (h : a=2*(k:ℝ))
    (l : -2<a) (u : a<2) : a=0 := by
  have lo : (-1:ℝ)<(k:ℝ) := by linarith
  have hi : (k:ℝ)<1 := by linarith
  have hlo : (-1:ℤ)<k := by exact_mod_cast lo
  have hhi : k<(1:ℤ) := by exact_mod_cast hi
  have hk : k=0 := by omega
  simp [h,hk]

private theorem add_res {x y z d : ℝ} (hd : d<1) (eq : x+y=z)
    (hx : 0≤residual x ∧ residual x≤d) (hy : 0≤residual y ∧ residual y≤d)
    (hz : 0≤residual z ∧ residual z≤d) : residual x+residual y=residual z := by
  have q : residual x+residual y-residual z=2*((idx z-idx x-idx y:ℤ):ℝ) := by
    push_cast
    dsimp [residual]
    linarith
  have r := even_zero _ q (by linarith) (by linarith)
  linarith

theorem three_ray_budget {n : ℕ} {T x y z : ℝ} (hT : T-(n:ℝ)<1)
    (turn : Fan T x y z)
    (hx : 0≤residual x ∧ residual x≤T-(n:ℝ)) (hy : 0≤residual y ∧ residual y≤T-(n:ℝ))
    (hz : 0≤residual z ∧ residual z≤T-(n:ℝ)) :
    residual x+residual y+residual z ≤ 2*(T-(n:ℝ)) := by
  rcases turn with h|h|h|h
  · linarith [add_res hT h hx hy hz]
  · linarith [add_res hT h hy hz hx]
  · linarith [add_res hT h hz hx hy]
  · have q : residual x+residual y+residual z-2*(T-(n:ℝ)) =
        2*(((n:ℤ)-idx x-idx y-idx z:ℤ):ℝ) := by
      push_cast
      dsimp [residual]
      linarith
    have r := even_zero _ q (by linarith) (by linarith)
    linarith

theorem triangle_budget {n : ℕ} {T x y z : ℝ} (hn : n%2=1) (hd : T-(n:ℝ)<1)
    (tri : x+y+z=T) (hx : 0≤residual x) (hy : 0≤residual y) (hz : 0≤residual z) :
    1+(T-(n:ℝ)) ≤ residual x+residual y+residual z := by
  let K : ℤ := 2*(idx x+idx y+idx z)
  have he : residual x+residual y+residual z=T-(K:ℝ) := by
    dsimp [residual,K]
    push_cast
    linarith
  have hh : (K:ℝ)<(n:ℝ)+1 := by linarith
  have hb : K<(n:ℤ)+1 := by exact_mod_cast hh
  have hk : K+1≤(n:ℤ) := by dsimp [K] at *; omega
  have hr : (K:ℝ)+1≤(n:ℝ) := by exact_mod_cast hk
  linarith

private theorem Fan.div {T x y z : ℝ} (h : Fan T x y z) (l : ℝ) :
    Fan (T/l) (x/l) (y/l) (z/l) := by
  rcases h with h|h|h|h
  · exact Or.inl (by rw [←add_div,h])
  · exact Or.inr (Or.inl (by rw [←add_div,h]))
  · exact Or.inr (Or.inr (Or.inl (by rw [←add_div,h])))
  · exact Or.inr (Or.inr (Or.inr (by rw [←add_div,←add_div,h]; ring)))

/-- Four actual top pencils cannot coexist anywhere in the open unit strip. -/
theorem no_four_profile (S : Finset Point) {lam : ℝ} (hl : 0<lam) (F : S → Row)
    (h : IsProfile S lam F) (n : ℕ) (hn : n%2=1) (width : π/lam-(n:ℝ)<1)
    (e : Fin 4 ↪ S) (top : ∀ i, (F (e i)).switches=n) : False := by
  let x (i j k : Fin 4) := EuclideanGeometry.angle ((e j).val) ((e i).val) ((e k).val)/lam
  let r (i j k : Fin 4) := residual (x i j k)
  have swap (i j k : Fin 4) : r i j k = r i k j := by
    simp only [r,x,EuclideanGeometry.angle_comm]
  have bound (i j k : Fin 4) (hj : j≠i) (hk : k≠i) :
      0≤r i j k ∧ r i j k≤π/lam-(n:ℝ) := by
    have B := profile_angle_band S hl F h (e j) (e i) (e k)
      (fun eq => hj (e.injective eq)) (fun eq => hk (e.injective eq))
    rw [top i] at B
    exact residual_bounds width B
  have triangle (i j k : Fin 4) (hij : i≠j) (hjk : j≠k) (hki : k≠i) :
      1+(π/lam-(n:ℝ)) ≤ r i j k+r j k i+r k i j := by
    have he : ((e i).val:Point)≠(e j).val := fun eq => hij (e.injective (Subtype.ext eq))
    have hs : x i j k+x j k i+x k i j=π/lam := by
      dsimp [x]
      rw [←add_div,←add_div]
      have tri := EuclideanGeometry.angle_add_angle_add_angle_eq_pi ((e k).val) he
      apply congrArg (fun u : ℝ => u/lam)
      linarith only [tri]
    exact triangle_budget hn width hs (bound i j k hij.symm hki).1
      (bound j k i hjk.symm hij).1 (bound k i j hki.symm hjk).1
  have vertex (i j k l : Fin 4) (hj : j≠i) (hk : k≠i) (hl' : l≠i) :
      r i j k+r i k l+r i l j ≤ 2*(π/lam-(n:ℝ)) := by
    have U := profile_fan S F h (e i) (e j) (e k) (e l)
      (fun eq => hj (e.injective eq)) (fun eq => hk (e.injective eq))
      (fun eq => hl' (e.injective eq))
    exact three_ray_budget width (U.div lam) (bound i j k hj hk) (bound i k l hk hl')
      (bound i l j hl' hj)
  have t₀ := triangle 0 1 2 (by decide) (by decide) (by decide)
  have t₁ := triangle 0 1 3 (by decide) (by decide) (by decide)
  have t₂ := triangle 0 2 3 (by decide) (by decide) (by decide)
  have t₃ := triangle 1 2 3 (by decide) (by decide) (by decide)
  have v₀ := vertex 0 1 2 3 (by decide) (by decide) (by decide)
  have v₁ := vertex 1 0 2 3 (by decide) (by decide) (by decide)
  have v₂ := vertex 2 0 1 3 (by decide) (by decide) (by decide)
  have v₃ := vertex 3 0 1 2 (by decide) (by decide) (by decide)
  simp only [swap] at t₀ t₁ t₂ t₃ v₀ v₁ v₂ v₃
  linarith only [t₀,t₁,t₂,t₃,v₀,v₁,v₂,v₃,width]

theorem at_most_three_top (S : Finset Point) {lam : ℝ} (hl : 0<lam) (F : S → Row)
    (h : IsProfile S lam F) (n : ℕ) (hn : n%2=1) (width : π/lam-(n:ℝ)<1) :
    (Finset.univ.filter (fun v : S => (F v).switches=n)).card≤3 := by
  classical
  by_contra! many
  let P := Finset.univ.filter (fun v : S => (F v).switches=n)
  have four : 4≤Fintype.card P := by
    rw [Fintype.card_coe]
    exact many
  let choose (i : Fin 4) : P := (Fintype.equivFin P).symm ⟨i.val,by omega⟩
  let e : Fin 4 ↪ S := ⟨fun i => (choose i).val,by
    intro i j eq
    have hh := congrArg (Fintype.equivFin P) (Subtype.ext eq : choose i=choose j)
    dsimp [choose] at hh
    simpa [Fin.ext_iff] using hh⟩
  apply no_four_profile S hl F h n hn width e
  intro i
  exact (Finset.mem_filter.mp (choose i).property).2

/-- Ordinary input only; the finite signed pencils are constructed in the conclusion. -/
theorem planar_top_count (S : Finset Point) (hs : 2≤S.card) {lam : ℝ}
    (hl : 0<lam) (hπ : lam≤π) (n : ℕ) (hn : n%2=1) (width : π/lam-(n:ℝ)<1)
    (legal : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a≠b → a≠c → b≠c →
      EuclideanGeometry.angle a b c≤π-lam) :
    ∃ F : S → Row, IsProfile S lam F ∧
      (Finset.univ.filter (fun v : S => (F v).switches=n)).card≤3 := by
  obtain ⟨F,rep,_⟩ := planar_switch_profile S hs hl hπ legal
  exact ⟨F,rep,at_most_three_top S hl F rep n hn width⟩

end R40.TopStratum

#print axioms R40.TopStratum.profile_fan
#print axioms R40.TopStratum.no_four_profile
#print axioms R40.TopStratum.at_most_three_top
#print axioms R40.TopStratum.planar_top_count
