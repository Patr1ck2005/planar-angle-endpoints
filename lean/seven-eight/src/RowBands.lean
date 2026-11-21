import SignedFan
import FullSwitchTriangle

namespace R37.SignedFan
open Real InnerProductGeometry JSP404
open scoped BigOperators

namespace Row

def idx (F : Row) (i : ℕ) : Fin (F.n+1) := ⟨min i F.n,by omega⟩
def u (F : Row) (i : ℕ) : ℝ := F.bearing (F.idx i)
def b (F : Row) (i : ℕ) : Bool := F.sign (F.idx i)
def step (F : Row) (i : ℕ) : ℕ := if F.b i=F.b (i+1) then 0 else 1
def prefixCount (F : Row) (i : ℕ) : ℕ := ∑ j ∈ Finset.range i, F.step j
/-- The next lift of the first line has the opposite sign. -/
def seam (F : Row) : ℕ := if F.b F.n=F.b 0 then 1 else 0
def switches (F : Row) : ℕ := F.prefixCount F.n+F.seam

private theorem pref_succ (F : Row) (i : ℕ) :
    F.prefixCount (i+1)=F.prefixCount i+F.step i := Finset.sum_range_succ _ _

private theorem pref_zero (F : Row) : F.prefixCount 0=0 := by simp [prefixCount]

private theorem pref_mono (F : Row) : Monotone F.prefixCount :=
  monotone_nat_of_le_succ (fun i => by rw [pref_succ]; omega)

private theorem bearings_mono (F : Row) : Monotone F.u := by
  intro i j hij
  apply F.sorted.monotone
  exact min_le_min_right F.n hij

theorem step_budget (F : Row) {lam : ℝ} (legal : F.Legal lam) (i : ℕ) :
    (F.step i : ℝ)*lam ≤ F.u (i+1)-F.u i := by
  have h := legal (F.idx i) (F.idx (i+1))
  rw [angle_oriented (F.bounds _) (F.bounds _)] at h
  change (if F.b i=F.b (i+1) then |F.u i-F.u (i+1)| else π-|F.u i-F.u (i+1)|) ≤ π-lam at h
  have hmono := F.bearings_mono (Nat.le_succ i)
  rw [abs_of_nonpos (sub_nonpos.mpr hmono)] at h
  by_cases he : F.b i=F.b (i+1)
  · simp [step,he,hmono]
  · simp [step,he] at h ⊢
    linarith

theorem seam_budget (F : Row) {lam : ℝ} (legal : F.Legal lam) :
    (F.seam : ℝ)*lam ≤ π-F.u F.n+F.u 0 := by
  have h := legal (F.idx 0) (F.idx F.n)
  rw [angle_oriented (F.bounds _) (F.bounds _)] at h
  change (if F.b 0=F.b F.n then |F.u 0-F.u F.n| else π-|F.u 0-F.u F.n|) ≤ π-lam at h
  rw [abs_of_nonpos (sub_nonpos.mpr (F.bearings_mono (Nat.zero_le _)))] at h
  by_cases he : F.b F.n=F.b 0
  · rw [if_pos he.symm] at h
    simp [seam,he]
    linarith
  · simp [seam,he]
    have h0 := (F.bounds (F.idx 0)).1
    have hn := (F.bounds (F.idx F.n)).2
    change 0≤F.u 0 at h0
    change F.u F.n<π at hn
    linarith

private theorem residual_mono (F : Row) {lam : ℝ} (legal : F.Legal lam) :
    Monotone (fun i => F.u i-(F.prefixCount i : ℝ)*lam) := by
  apply monotone_nat_of_le_succ
  intro i
  change F.u i-(F.prefixCount i:ℝ)*lam ≤ F.u (i+1)-(F.prefixCount (i+1):ℝ)*lam
  rw [pref_succ,Nat.cast_add,add_mul]
  linarith [F.step_budget legal i]

private theorem pref_parity (F : Row) (i : ℕ) :
    F.prefixCount i%2 = if F.b 0=F.b i then 0 else 1 := by
  induction i with
  | zero => simp [pref_zero]
  | succ i ih =>
    rw [pref_succ]
    cases h0 : F.b 0 <;> cases hi : F.b i <;> cases hj : F.b (i+1) <;>
      simp [h0,hi,hj,step] at ih ⊢ <;> omega

theorem switches_odd (F : Row) : F.switches%2=1 := by
  have h := F.pref_parity F.n
  cases h0 : F.b 0 <;> cases hn : F.b F.n <;>
    simp [switches,seam,h0,hn] at h ⊢ <;> omega

theorem total_budget (F : Row) {lam : ℝ} (legal : F.Legal lam) :
    (F.switches : ℝ)*lam ≤ π := by
  have h := F.residual_mono legal (Nat.zero_le F.n)
  simp only [pref_zero,Nat.cast_zero,zero_mul,sub_zero] at h
  simp only [switches,Nat.cast_add,add_mul]
  linarith [F.seam_budget legal]

/-- The increment in switch count along an arbitrary segment of the
projective row gives its length to within the total residual slack,
without assuming a precomputed list of gaps. -/
theorem partial_budget (F : Row) {lam : ℝ} (legal : F.Legal lam) {i j : ℕ}
    (hij : i≤j) (hj : j≤F.n) :
    let t := F.prefixCount j-F.prefixCount i
    (t:ℝ)*lam ≤ F.u j-F.u i ∧
      F.u j-F.u i ≤ (t:ℝ)*lam + (π-(F.switches:ℝ)*lam) := by
  dsimp only
  rw [Nat.cast_sub (F.pref_mono hij),sub_mul]
  have h := F.residual_mono legal hij
  have h₀ := F.residual_mono legal (Nat.zero_le i)
  have h₁ := F.residual_mono legal hj
  simp only [pref_zero,Nat.cast_zero,zero_mul,sub_zero] at h₀
  have wrap := F.seam_budget legal
  simp only [switches,Nat.cast_add,add_mul]
  exact ⟨by linarith,by linarith⟩

/-- A true smaller unoriented angle between two incident rays lies near
an *even* multiple of λ. The opposite-sign branch uses the complement
of the projective interval and hence also counts an even number of
switches, including the sign reversal at the seam. -/
theorem angle_band (F : Row) {lam : ℝ} (hl : 0<lam) (legal : F.Legal lam)
    (i j : Fin (F.n+1)) :
    FullSwitchTriangle.Band F.switches (π/lam)
      (angle (oriented (F.bearing i) (F.sign i)) (oriented (F.bearing j) (F.sign j))/lam) := by
  wlog ho : i≤j generalizing i j
  · rw [angle_comm]
    exact this j i (le_of_not_ge ho)
  have hi : F.idx i.val=i := Fin.ext (min_eq_left (by omega))
  have hj : F.idx j.val=j := Fin.ext (min_eq_left (by omega))
  rw [←hi,←hj,angle_oriented (F.bounds _) (F.bounds _)]
  change FullSwitchTriangle.Band F.switches (π/lam)
    ((if F.b i.val=F.b j.val then |F.u i.val-F.u j.val| else π-|F.u i.val-F.u j.val|)/lam)
  have hij : i.val ≤ j.val := ho
  rw [abs_of_nonpos (sub_nonpos.mpr (F.bearings_mono hij))]
  let d := F.prefixCount j.val-F.prefixCount i.val
  have hd : d≤F.switches := by
    have h := F.pref_mono (show j.val≤F.n by omega)
    dsimp [d,switches];omega
  have hspan := F.partial_budget legal hij (show j.val≤F.n by omega)
  change (d:ℝ)*lam≤F.u j.val-F.u i.val ∧ F.u j.val-F.u i.val≤(d:ℝ)*lam+(π-(F.switches:ℝ)*lam) at hspan
  have hi' := F.pref_parity i.val
  have hj' := F.pref_parity j.val
  have hpre := F.pref_mono hij
  have hs := F.switches_odd
  by_cases he : F.b i.val=F.b j.val
  · rw [if_pos he]
    have even : d%2=0 := by rw [he] at hi'; dsimp [d]; omega
    refine ⟨d/2,?_,?_⟩
    all_goals have de : (d:ℝ)=2*((d/2:ℕ):ℝ) := by exact_mod_cast (show d=2*(d/2) by omega)
    · apply (le_div_iff₀ hl).2
      rw [←de]
      linarith [hspan.1]
    · have dc : (2*((d/2:ℕ):ℝ)+(π/lam-(F.switches:ℝ)))*lam =
          (d:ℝ)*lam+π-(F.switches:ℝ)*lam := by rw [add_mul,sub_mul,div_mul_cancel₀ _ hl.ne',←de];ring
      apply (div_le_iff₀ hl).2
      linarith
  · rw [if_neg he]
    have odd : d%2=1 := by
      cases h0 : F.b 0 <;> cases hi : F.b i.val <;> cases hj : F.b j.val <;>
        simp [h0,hi,hj] at he hi' hj' <;> dsimp [d] <;> omega
    let c := F.switches-d
    have even : c%2=0 := by dsimp [c];omega
    have de : (c:ℝ)=2*((c/2:ℕ):ℝ) := by exact_mod_cast (show c=2*(c/2) by omega)
    have cc : (c:ℝ)=(F.switches:ℝ)-(d:ℝ) := Nat.cast_sub hd
    refine ⟨c/2,?_,?_⟩
    · apply (le_div_iff₀ hl).2
      rw [←de,cc,sub_mul]
      linarith [hspan.2]
    · apply (div_le_iff₀ hl).2
      rw [←de,cc,add_mul,sub_mul,sub_mul,div_mul_cancel₀ _ hl.ne']
      linarith [hspan.1]

end Row
#print axioms Row.angle_band
end R37.SignedFan
