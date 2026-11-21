import AnchoredCloud

noncomputable section
namespace R52.TwoAnchor
open Real JSP404 R49.ChordBins R49.FactorPacking R51.Anchored R37.SignedFan InnerProductGeometry

private theorem split_span (Q : Finset ℝ) (non : Q.Nonempty) {l a b c t v : ℝ} (lp : 0<l)
    (outer : ∀ x∈Q, t+a≤x ∧ x≤t+π-a) (hole : ∀ x∈Q, b≤|x-v|)
    (sep : ∀ x∈Q, ∀ y∈Q, x≠y → l≤|x-y|) (count : c≤Q.card) :
    (c-2)*l+2*(a+b)≤π ∨ (c-1)*l+(a+b)≤max (v-t) (t+π-v) := by
  classical
  let L := Q.filter (fun x => x≤v)
  let R := Q.filter (fun x => ¬x≤v)
  have sz : (L.card:ℝ)+R.card=Q.card := by exact_mod_cast Finset.card_filter_add_card_filter_not (s:=Q) (p:=fun x=>x≤v)
  have left (h : L.Nonempty) : (L.card:ℝ)*l≤(v-b)-(t+a)+l := by
    apply interval_span _ lp h
    · intro x hx
      have ⟨mem,le⟩ := Finset.mem_filter.mp hx
      have g:=hole _ mem
      rw [abs_of_nonpos (sub_nonpos.mpr le)] at g
      exact ⟨(outer _ mem).1,by linarith⟩
    · intro x hx y hy d;exact sep _ (Finset.mem_filter.mp hx).1 _ (Finset.mem_filter.mp hy).1 d
  have right (h : R.Nonempty) : (R.card:ℝ)*l≤(t+π-a)-(v+b)+l := by
    apply interval_span _ lp h
    · intro x hx
      have ⟨mem,ge⟩ := Finset.mem_filter.mp hx
      have g:=hole _ mem
      rw [abs_of_nonneg (by linarith : 0≤x-v)] at g
      exact ⟨by linarith,(outer _ mem).2⟩
    · intro x hx y hy d;exact sep _ (Finset.mem_filter.mp hx).1 _ (Finset.mem_filter.mp hy).1 d
  have enlarged := mul_le_mul_of_nonneg_right count lp.le
  rcases L.eq_empty_or_nonempty with el|ln <;> rcases R.eq_empty_or_nonempty with er|rn
  · simp [el,er] at sz
    have qpos := Finset.card_pos.mpr non
    exact False.elim (by exact_mod_cast (show ¬(0:ℝ)<Q.card from by linarith) (by exact_mod_cast qpos))
  · right; rw [el] at sz;simp at sz
    have r:=right rn
    rw [sz] at r
    nlinarith [le_max_right (v-t) (t+π-v)]
  · right; rw [er] at sz;simp at sz
    have h:=left ln
    rw [sz] at h
    nlinarith [le_max_left (v-t) (t+π-v)]
  · left
    nlinarith [left ln,right rn]

theorem two_cuts {F : Finset Point} {n : ℕ} (C : Chart F n) (two : 2≤F.card)
    {l t v g h : ℝ} (lp : 0<l) (ok : Legal F l) (vt : 0≤v ∧ v<π)
    (ct : ∀ x∈spectrum C, Apart g t x) (cv : ∀ x∈spectrum C, Apart h v x) :
    ((Nat.clog 2 F.card : ℝ)-2)*l+2*(g+h)≤π ∨
      ((Nat.clog 2 F.card : ℝ)-1)*l+(g+h)≤max |t-v| (π-|t-v|) := by
  classical
  obtain ⟨P,sub,count,sep⟩ := selectedLine C t lp ok
  let Q := P.image (lifted t)
  have cn : 0<Nat.clog 2 F.card := Nat.clog_pos (by decide) (by omega)
  have non := (Finset.card_pos.mp (cn.trans_le count)).image (lifted t)
  have inj : Set.InjOn (lifted t) (↑P : Set ℝ) := by
    intro a ha b hb eq
    by_contra ne
    have h := sep a ha b hb ne
    rw [eq,sub_self,abs_zero] at h;linarith
  have size : Q.card=P.card := Finset.card_image_of_injOn inj
  have bd := split_span Q non (c:=(Nat.clog 2 F.card:ℝ)) (v:=lifted t v) lp (fun x hx => by
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx;exact safe_lift (ct _ (sub ha))) (fun x hx => by
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨i,j,_,eq⟩ := (mem_spectrum C).mp (sub ha)
    have ra := C.range i j
    rw [eq] at ra
    have av := cv _ (sub ha)
    unfold Apart at av
    rw [abs_sub_comm v a] at av
    rw [lift_diff (abs_le.mpr ⟨by linarith [ra.1,vt.2],by linarith [ra.2,vt.1]⟩)]
    split_ifs <;> linarith [av.1,av.2]) (fun x hx y hy ne => by
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hy
    exact sep _ ha _ hb (fun eq => ne (congrArg _ eq))) (by rw [size];exact_mod_cast count)
  convert bd using 2
  unfold lifted
  split_ifs with e
  · rw [abs_of_nonneg (by linarith : 0≤t-v),max_comm]
    congr 1 <;> ring
  · rw [abs_of_nonpos (by linarith : t-v≤0)]
    congr 1 <;> ring

end R52.TwoAnchor
