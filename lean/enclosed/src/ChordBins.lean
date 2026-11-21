import CubeRanks

noncomputable section
namespace R49.ChordBins
open Real JSP404 R37.SignedFan InnerProductGeometry R48.CubeRanks

structure Chart (S : Finset Point) (n : ℕ) where
  label : S ↪ Word n
  slot : S → S → Fin n
  bearing : S → S → ℝ
  same_slot : ∀ a b, slot a b = slot b a
  same_bearing : ∀ a b, bearing a b = bearing b a
  range : ∀ a b, 0 ≤ bearing a b ∧ bearing a b < π
  bins : ∀ a b, ((slot a b).val : ℝ)*(π/n) ≤ bearing a b ∧
    bearing a b < (((slot a b).val : ℝ)+1)*(π/n)
  separates : ∀ a b, a ≠ b → label a (slot a b) ≠ label b (slot a b)
  realized : ∀ a b : S, a ≠ b → ∃ r : ℝ, 0<r ∧ (b : Point)-a =
    r • oriented (bearing a b) (label a (slot a b))

private theorem ray {S : Finset Point} {lam : ℝ} {F : S → Row} (h : IsProfile S lam F)
    (v u : S) (ne : v≠u) : ∃ k, ∃ r : ℝ, 0<r ∧ (u:Point)-v=r • oriented ((F v).bearing k) ((F v).sign k) := by
  have mem : u.val∈S.erase v.val := Finset.mem_erase.mpr ⟨fun e => ne (Subtype.ext e.symm),u.property⟩
  exact (h v).1.1 ⟨u.val,mem⟩

private theorem opposite {v u : Point} (ne : v≠u) {x y : ℝ} {a b : Bool}
    (hx : 0≤x ∧ x<π) (hy : 0≤y ∧ y<π)
    (rv : ∃ r : ℝ, 0<r ∧ u-v=r • oriented x a)
    (ru : ∃ r : ℝ, 0<r ∧ v-u=r • oriented y b) : x=y ∧ a≠b := by
  obtain ⟨r,rp,rv⟩ := rv
  obtain ⟨s,sp,ru⟩ := ru
  have eq : angle (u-v) (v-u)=π := by
    rw [←neg_sub u v,angle_neg_right,angle_self (sub_ne_zero.mpr ne.symm),sub_zero]
  rw [rv,ru,angle_smul_left_of_pos _ _ rp,angle_smul_right_of_pos _ _ sp,angle_oriented hx hy] at eq
  have small : |x-y|<π := abs_lt.mpr ⟨by linarith,by linarith⟩
  by_cases e : a=b
  · rw [if_pos e] at eq; linarith
  · rw [if_neg e] at eq
    exact ⟨sub_eq_zero.mp (abs_eq_zero.mp (by linarith)),e⟩

theorem of_profile {S : Finset Point} {n : ℕ} (hn : 0<n) {lam : ℝ}
    (margin : π/(n:ℝ)<lam) (F : S → Row) (profile : IsProfile S lam F) :
    Nonempty (Chart S n) := by
  classical
  let w := π/(n:ℝ)
  have np : (0:ℝ)<n := by exact_mod_cast hn
  have wp : 0<w := div_pos pi_pos np
  have per : (n:ℝ)*w=π := by dsimp [w]; field_simp
  have gap : w<lam := margin
  let cell (a : ℝ) := ⌊a/w⌋₊
  have cell_bound {a : ℝ} (ha : 0≤a ∧ a<π) : cell a<n :=
    (Nat.floor_lt (div_nonneg ha.1 wp.le)).mpr ((div_lt_iff₀ wp).mpr (by simpa [per] using ha.2))
  let slot (v : S) (i : Fin ((F v).n+1)) : Fin n :=
    ⟨cell ((F v).bearing i),cell_bound ((F v).bounds i)⟩
  have low (v : S) (i : Fin ((F v).n+1)) : ((slot v i).val:ℝ)*w≤(F v).bearing i :=
    (le_div_iff₀ wp).mp (Nat.floor_le (div_nonneg ((F v).bounds i).1 wp.le))
  have high (v : S) (i : Fin ((F v).n+1)) : (F v).bearing i<(((slot v i).val:ℝ)+1)*w :=
    (div_lt_iff₀ wp).mp (Nat.lt_floor_add_one _)
  have same (v : S) (i j : Fin ((F v).n+1)) (eq : slot v i=slot v j) : (F v).sign i=(F v).sign j := by
    by_contra ne
    have leg := (profile v).2 i j
    rw [angle_oriented ((F v).bounds i) ((F v).bounds j),if_neg ne] at leg
    have l := low v i; have h := high v i
    rw [eq] at l h
    have close : |(F v).bearing i-(F v).bearing j|<w := abs_lt.mpr
      ⟨by nlinarith [low v j,high v j],by nlinarith [low v j,high v j]⟩
    linarith
  let label (v : S) (k : Fin n) := if h : ∃ i, slot v i=k then (F v).sign h.choose else false
  have agrees (v : S) (i : Fin ((F v).n+1)) : label v (slot v i)=(F v).sign i := by
    have ex : ∃ j, slot v j=slot v i := ⟨i,rfl⟩
    exact (dif_pos ex).trans (same v _ _ ex.choose_spec)
  let idx (v u : S) : Fin ((F v).n+1) := if h : v≠u then (ray profile v u h).choose else 0
  have represented (v u : S) (ne : v≠u) : ∃ r : ℝ, 0<r ∧ (u:Point)-v=
      r • oriented ((F v).bearing (idx v u)) ((F v).sign (idx v u)) := by
    simpa only [idx,dif_pos ne] using (ray profile v u ne).choose_spec
  let bearing (v u : S) := (F v).bearing (idx v u)
  have pair (v u : S) (ne : v≠u) : bearing v u=bearing u v ∧ (F v).sign (idx v u)≠(F u).sign (idx u v) :=
    opposite (fun e => ne (Subtype.ext e)) ((F v).bounds _) ((F u).bounds _)
      (represented v u ne) (represented u v ne.symm)
  have sym (v u : S) : bearing v u=bearing u v := by by_cases e : v=u <;> first | simp [e] | exact (pair v u e).1
  let dim (v u : S) := slot v (idx v u)
  have dim_sym (v u : S) : dim v u=dim u v := by
    apply Fin.ext
    exact congrArg cell (sym v u)
  have disagree (v u : S) (ne : v≠u) : label v (dim v u)≠label u (dim v u) := by
    have a := agrees v (idx v u); have b := agrees u (idx u v)
    change label v (dim v u)=_ at a
    change label u (dim u v)=_ at b
    rw [←dim_sym v u] at b
    rw [a,b]; exact (pair v u ne).2
  have injective : Function.Injective label := by
    intro v u eq; by_contra ne; exact disagree v u ne (congrFun eq _)
  refine ⟨⟨⟨label,injective⟩,dim,bearing,dim_sym,sym,fun v u => (F v).bounds _,
    fun v u => ⟨low v _,high v _⟩,disagree,?_⟩⟩
  intro v u ne
  change ∃ r : ℝ, 0<r ∧ (u:Point)-v=r • oriented ((F v).bearing (idx v u)) (label v (slot v (idx v u)))
  rw [agrees]
  exact represented v u ne

theorem planar {S : Finset Point} (hs : 2≤S.card) {n : ℕ} (hn : 0<n) {lam : ℝ}
    (margin : π/(n:ℝ)<lam) (hp : lam≤π)
    (legal : ∀ a∈S, ∀ b∈S, ∀ c∈S, a≠b → a≠c → b≠c → EuclideanGeometry.angle a b c≤π-lam) :
    Nonempty (Chart S n) := by
  have hl : 0<lam := lt_trans (div_pos pi_pos (by exact_mod_cast hn)) margin
  obtain ⟨F,profile,_⟩ := planar_switch_profile S hs hl hp legal
  exact of_profile hn margin F profile

end R49.ChordBins
#print axioms R49.ChordBins.planar