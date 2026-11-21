import PlaneRows

noncomputable section
open scoped Classical
namespace R58.Plane
open Real JSP404 R37.SignedFan R58.FullRows Finset

/-- The bound holds for every fully realized signed profile of the given
ordinary point set, with its unshifted, cyclic pencil gaps. -/
theorem profile_bound (S : Finset Point) {l : ℝ} (lp : 0<l) (limit : l≤π)
    (law : maxAngle S≤π-l) (F : S→Fan) (profile : IsProfile S l F) :
    (∑ v : S,2^(digits (F v) l+cells (F v) l))≤2^⌊2*π/l⌋₊ := by
  classical
  by_cases existsS : S.Nonempty
  · let default : S:=⟨existsS.choose,existsS.choose_spec⟩
    let loc (p : Point) : S:=if h : p∈S then ⟨p,h⟩ else default
    have self (p : S) : loc p=p := by simp [loc,p.property]
    choose R long cnt dig rep using fun p : S=>row_chart (F p) (fun q : S.erase p.val=>(q:Point)-p.val)
      lp (profile p).1 (profile p).2
    have cap:=R58.AllRows.capacity S (fun p=>(F (loc p)).n+1) (fun p=>R (loc p)) lp limit law
      (fun p _=>by simpa using long (loc p)) (by
        intro p hp u hu ne
        let v : S:=⟨p,hp⟩
        have h : loc p=v := self v
        rw [h]
        exact rep v ⟨u,Finset.mem_erase.mpr ⟨ne.symm,hu⟩⟩)
    have eq : (∑ v∈S,2^((∑ j : Fin ((F (loc v)).n+1),(R (loc v)).digits j l)+
        cellSum (R (loc v)) l ((F (loc v)).n+1)))=
        ∑ p : S,2^(digits (F p) l+cells (F p) l) := by
      simp_rw [dig,cnt]
      rw [←Finset.sum_attach S]
      simp [self]
    exact eq ▸ cap
  · have empty:=Finset.not_nonempty_iff_eq_empty.mp existsS
    subst S
    simp

/-- Original-plane mixed moment. A legal point set alone produces a fully
realized profile. Every gap, including the last one, is measured on the actual
projective pencil in the fixed chart measured from direction zero. -/
theorem ordinary_mixed_moment (S : Finset Point) (size : 2≤S.card) {l : ℝ}
    (lp : 0<l) (law : maxAngle S≤π-l) :
    ∃ F : S→Fan, IsProfile S l F ∧
      (∑ v : S,2^(digits (F v) l+cells (F v) l))≤2^⌊2*π/l⌋₊ := by
  classical
  have lim : l≤π := by linarith [maxAngle_nonneg S]
  choose F obs ok using fun v : S=>exists_planar_row S v v.property size lp lim (fun _ ha _ hb _ hc ab ac bc=>
    (angle_le_maxAngle ha hb hc ab ac bc).trans law)
  have prof : IsProfile S l F:=fun p=>⟨obs p,ok p⟩
  exact ⟨F,prof,profile_bound S lp lim law F prof⟩

/-- The ordinary low cap for any realized full-cell profile. -/
theorem low_full_capacity (S : Finset Point) {l : ℝ} (lp : 0<l) (law : maxAngle S≤π-l)
    (F : S→Fan) (profile : IsProfile S l F) (n : ℕ) (strip : π/l<(n:ℝ)+1/2)
    (full : ∀ v,cells (F v) l=n) : (∑ v : S,2^digits (F v) l)≤2^n := by
  have cap:=profile_bound S lp (by linarith [maxAngle_nonneg S]) law F profile
  have h : ⌊2*π/l⌋₊<2*n+1 := by
    apply (Nat.floor_lt (by positivity)).mpr
    push_cast
    linarith [show 2*π/l=2*(π/l) by ring]
  have expo : ⌊2*π/l⌋₊≤n+n := by omega
  have rhs : (2:ℕ)^⌊2*π/l⌋₊≤2^n*2^n := by
    rw [←pow_add]
    exact Nat.pow_le_pow_right (by decide) expo
  simp_rw [full,pow_add] at cap
  rw [←Finset.sum_mul] at cap
  exact Nat.le_of_mul_le_mul_right (cap.trans rhs) (by positivity : 0<(2:ℕ)^n)

end R58.Plane
#print axioms R58.Plane.profile_bound
#print axioms R58.Plane.ordinary_mixed_moment
#print axioms R58.Plane.low_full_capacity
