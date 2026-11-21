import AnchoredCloud
noncomputable section
namespace R51.Anchored
open Real JSP404 R49.ChordBins R49.FactorPacking R37.SignedFan InnerProductGeometry

private theorem interval_cover {m : ℕ} (w : ℕ→ℝ) (x : ℝ) (pos : 0<m) (lo : w 0≤x) (hi : x≤w m) :
    ∃ i : Fin m, w i≤x ∧ x≤w (i.val+1) := by
  induction m with
  | zero => omega
  | succ m ih =>
    by_cases left : w m≤x
    · exact ⟨Fin.last m,left,hi⟩
    · have mp : 0<m := by
        by_contra! h
        have eq : m=0 := by omega
        exact left (eq.symm ▸ lo)
      obtain ⟨i,a,b⟩ := ih mp (le_of_not_ge left)
      exact ⟨i.castSucc,a,b⟩

/-- An actual external observer supplies an unoriented wall at w, expressed in a chart cut at t.
The additional translate by π allows the first observed wall to close the last interval. -/
def Wall (S F : Finset Point) (t w η : ℝ) := ∃ p∈S, p∉F ∧ ∃ a : ℝ, ∃ b : Bool,
  (0≤a ∧ a<π) ∧ InCone F p (oriented a b) η ∧ (w=lifted t a ∨ w=lifted t a+π)

private theorem wall_distance {S F : Finset Point} {n : ℕ} (C : Chart F n) (sub : F⊆S)
    {t w η : ℝ} (h : Wall S F t w η) {x : ℝ} (hx : x∈spectrum C) :
    π-maxAngle S-η≤|lifted t x-w| := by
  obtain ⟨p,ps,pf,a,b,ha,cone,hw⟩:=h
  have eq : oriented a b=(1:ℝ) • oriented a b := by simp
  have apart:=cone_cut C sub ps pf ha zero_lt_one eq cone x hx
  obtain ⟨u,v,_,hv⟩ := (mem_spectrum C).mp hx
  have hr : |x-a|≤π := abs_le.mpr ⟨by linarith [(C.range u v).1,ha.2],by linarith [(C.range u v).2,ha.1]⟩
  unfold Apart at apart
  rw [abs_sub_comm a x] at apart
  have both : Apart (π-maxAngle S-η) (lifted t x) (lifted t a) := by
    unfold Apart
    rw [lift_diff hr]
    split_ifs <;> exact ⟨by linarith [apart.1,apart.2],by linarith [apart.1,apart.2]⟩
  rcases hw with rfl|rfl
  · exact both.1
  · linarith [neg_le_abs (lifted t x-(lifted t a+π)),le_abs_self (lifted t x-lifted t a),both.2]

/-- Finite-cloud inequality with independent errors at the observed boundaries.
No exact blowup, additivity, hierarchy, or zero-diameter cluster is assumed. -/
theorem multiple_anchor_capacity {S F : Finset Point} (sub : F⊆S) (two : 2≤F.card)
    {m : ℕ} (nonempty : 0<m) (t : ℝ) (ht : 0≤t ∧ t<π) (w η : ℕ→ℝ) (B : Fin m→ℕ)
    (first : w 0=t) (last : w m=t+π) (wall : ∀ j≤m, Wall S F t (w j) (η j))
    (lp : 0<π-maxAngle S)
    (fit : ∀ j : Fin m, w (j.val+1)-w j+η j+η (j.val+1)<((B j:ℝ)+2)*(π-maxAngle S)) :
    Nat.clog 2 F.card≤∑ j, B j := by
  classical
  let l := π-maxAngle S
  have lim : l≤π := by dsimp [l];linarith [maxAngle_nonneg S]
  have legal : Legal F l := by
    intro a ha b hb c hc ab ac bc
    dsimp [l]; simpa using angle_le_maxAngle (sub ha) (sub hb) (sub hc) ab ac bc
  obtain ⟨n,hn⟩ := exists_nat_gt (π/l)
  have np : (0:ℝ)<n := (div_pos pi_pos lp).trans hn
  have margin : π/(n:ℝ)<l := (div_lt_iff₀ np).mpr (by linarith [(div_lt_iff₀ lp).mp hn])
  let C : Chart F n := Classical.choice (planar two (by exact_mod_cast np : 0<n) margin lim legal)
  obtain ⟨P,subP,count,sep⟩ := selectedLine C t lp legal
  let Q := P.image (lifted t)
  have uniq : Set.InjOn (lifted t) (↑P:Set ℝ) := by
    intro a ha b hb eq
    by_contra ne
    have h:=sep a ha b hb ne
    rw [eq,sub_self,abs_zero] at h
    linarith
  have cq : Q.card=P.card := Finset.card_image_of_injOn uniq
  let box (i : Fin m) := Q.filter (fun x => w i≤x ∧ x≤w (i.val+1))
  have cover : Q⊆Finset.univ.biUnion box := by
    intro x hx
    obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp hx
    obtain ⟨u,v,_,hv⟩:=(mem_spectrum C).mp (subP ha)
    have range := C.range u v
    rw [hv] at range
    have bounds : t≤lifted t a ∧ lifted t a≤t+π := by unfold lifted;split_ifs <;> constructor <;> linarith [ht.1,ht.2,range.1,range.2]
    obtain ⟨i,low,high⟩:=interval_cover w (lifted t a) nonempty (first.symm ▸ bounds.1) (last.symm ▸ bounds.2)
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ ha,low,high⟩⟩
  have each (i : Fin m) : (box i).card≤B i := by
    rcases (box i).eq_empty_or_nonempty with empty|non
    · simp [empty]
    have bounds (x : ℝ) (hx : x∈box i) :
        w i+l-η i≤x ∧ x≤w (i.val+1)-l+η (i.val+1) := by
      obtain ⟨mem,left,right⟩:=Finset.mem_filter.mp hx
      obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp mem
      have h1:=wall_distance C sub (wall i (Nat.le_of_lt i.isLt)) (subP ha)
      have h2:=wall_distance C sub (wall (i.val+1) i.isLt) (subP ha)
      rw [abs_of_nonneg (sub_nonneg.mpr left)] at h1
      rw [abs_of_nonpos (sub_nonpos.mpr right)] at h2
      dsimp [l];constructor <;> linarith
    have packed:=interval_span (box i) lp non _ _ bounds (by
      intro x hx y hy ne
      obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp (Finset.mem_filter.mp hx).1
      obtain ⟨b,hb,rfl⟩:=Finset.mem_image.mp (Finset.mem_filter.mp hy).1
      exact sep _ ha _ hb (fun e=>ne (congrArg _ e)))
    have narrow:=fit i
    change _<((B i:ℝ)+2)*l at narrow
    by_contra! fail
    have cn : (B i:ℝ)+1≤(box i).card := by exact_mod_cast fail
    nlinarith [mul_le_mul_of_nonneg_right cn lp.le]
  calc Nat.clog 2 F.card ≤ Q.card := cq.symm ▸ count
       _ ≤ (Finset.univ.biUnion box).card := Finset.card_le_card cover
       _ ≤ ∑ i, (box i).card := Finset.card_biUnion_le
       _ ≤ ∑ i, B i := Finset.sum_le_sum (fun i _ => each i)

end R51.Anchored
#print axioms R51.Anchored.multiple_anchor_capacity
