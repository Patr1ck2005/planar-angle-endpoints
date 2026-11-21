import WindowAxes

noncomputable section
open scoped Classical
namespace R56.Rounding
open Real JSP404 R49.ChordBins R49.FactorPacking R37.SignedFan R51.Anchored InnerProductGeometry

/-- The same axes serve every exterior observer that satisfies its own viewing-cone test. -/
theorem select_axes {S F : Finset Point} (sub : F⊆S) {a : Point} (am : a∈F)
    {η : ℝ} (ep : 0≤η) (slack : 0<π-maxAngle S-η)
    (anchor : ∃p∈S, p∉F ∧ InCone F p (p-a) η) :
    ∃ v : Fin (Nat.clog 2 F.card)→Point, (∀ i,‖v i‖=1) ∧
      (∀ i j,i≠j → ∀ r s : ℝ, (r= -1 ∨ r=1) → (s= -1 ∨ s=1) →
        angle (r • v i) (s • v j)≤maxAngle S+η) ∧
      ∀ p∈S,p∉F → InCone F p (p-a) η → ∀ i (r : ℝ), (r= -1 ∨ r=1) →
        angle (r • v i) (p-a)≤maxAngle S+η := by
  classical
  by_cases two : 2≤F.card
  · let l:=π-maxAngle S
    let g:=π-maxAngle S-η
    have pos : 0<l := by dsimp [l];linarith
    have lim : l≤π := by dsimp [l];linarith [maxAngle_nonneg S]
    have legal : Legal F l := by
      intro x hx y hy z hz xy xz yz
      simpa [l] using angle_le_maxAngle (sub hx) (sub hy) (sub hz) xy xz yz
    obtain ⟨n,hn⟩:=exists_nat_gt (π/l)
    have np : (0:ℝ)<n := (div_pos pi_pos pos).trans hn
    have margin : π/(n:ℝ)<l := (div_lt_iff₀ np).mpr (by linarith [(div_lt_iff₀ pos).mp hn])
    let C : Chart F n := Classical.choice (planar two (by exact_mod_cast np : 0<n) margin lim legal)
    obtain ⟨p,ps,pf,cone⟩:=anchor
    have pa : p-a≠0 := sub_ne_zero.mpr (fun eq=>pf (eq ▸ am))
    obtain ⟨t,b,r,ht,hr,eq⟩:=signed_polar pa
    have cut:=cone_cut C sub ps pf ht hr eq cone
    obtain ⟨P,subset,count,separated⟩:=selectedLine C t pos legal
    let index (j : Fin (Nat.clog 2 F.card)) : Fin (Fintype.card P) :=
      ⟨j.val,by simpa using j.isLt.trans_le count⟩
    let x (j : Fin (Nat.clog 2 F.card)) : P := (Fintype.equivFin P).symm (index j)
    have spectrum_mem (j) : (x j:ℝ)∈spectrum C := subset (x j).property
    have range (j) : 0≤(x j:ℝ) ∧ (x j:ℝ)<π := by
      obtain ⟨u,v,_,eq⟩:=(mem_spectrum C).mp (spectrum_mem j)
      exact eq ▸ C.range u v
    have diff {i j} (ne : i≠j) : (x i:ℝ)≠(x j:ℝ) := by
      intro e
      have ind := (Fintype.equivFin P).symm.injective (Subtype.ext e : x i=x j)
      exact ne (Fin.ext (congrArg (fun k : Fin (Fintype.card P)=>k.val) ind))
    refine ⟨fun j=>circleDirection (x j),?_,?_,?_⟩
    · exact fun j=>norm_circleDirection (x j)
    · intro i j ne r s hr hs
      have sep:=separated _ (x i).property _ (x j).property (diff ne)
      have a:=safe_lift (cut _ (spectrum_mem i))
      have b:=safe_lift (cut _ (spectrum_mem j))
      have upper : |lifted t (x i)-lifted t (x j)|≤π-g :=
        abs_le.mpr ⟨by dsimp [g];linarith [a.1,b.2],by dsimp [g];linarith [b.1,a.2]⟩
      have ra : |(x i:ℝ)-(x j:ℝ)|≤π :=
        abs_le.mpr ⟨by linarith [(range i).1,(range j).2],by linarith [(range j).1,(range i).2]⟩
      rw [lift_diff ra] at sep upper
      have apart : Apart g (x i) (x j) := by
        have gl : g≤l := by dsimp [g,l];linarith
        split_ifs at sep upper <;> exact ⟨by linarith,by linarith⟩
      have h:=signed_circleDirection_angle_le_of_separation slack.le apart.1 apart.2 r s hr hs
      convert h using 1
      ring
    · intro z zs zf cone j r hr
      have za : z-a≠0 := sub_ne_zero.mpr (fun eq=>zf (eq ▸ am))
      obtain ⟨u,b,y,hu,hy,eq⟩:=signed_polar za
      have apart:=cone_cut C sub zs zf hu hy eq cone _ (spectrum_mem j)
      obtain ⟨e,he,sg⟩ : ∃ e : ℝ,(e= -1 ∨ e=1) ∧ oriented u b=e • circleDirection u := by
        cases b
        · exact ⟨-1,Or.inl rfl,by simp [oriented]⟩
        · exact ⟨1,Or.inr rfl,by simp [oriented]⟩
      rw [eq,angle_smul_right_of_pos _ _ hy,sg]
      unfold Apart at apart
      rw [abs_sub_comm] at apart
      have h:=signed_circleDirection_angle_le_of_separation slack.le apart.1 apart.2 r e hr he
      convert h using 1
      ring
  · have one : F.card≤1 := by omega
    have zero : Nat.clog 2 F.card=0 := by
      have h : Nat.clog 2 F.card≤0 := Nat.clog_le_of_le_pow (by simpa using one)
      omega
    let impossible (i : Fin (Nat.clog 2 F.card)) : False := by have h:=i.isLt;omega
    exact ⟨fun _=>0,fun i=>(impossible i).elim,fun i=>(impossible i).elim,
      fun _ _ _ _ i=>(impossible i).elim⟩

/-- Binary-round every cardinality in one ordinary configuration. The only viewing
requirements concern the external representatives of the selected clouds. -/
theorem alpha_rounded {I : Type*} [Fintype I] {S : Finset Point} (F : I→Finset Point)
    (c : I→Point) (sub : ∀ i,F i⊆S) (mem : ∀ i,c i∈F i) (ext : ∀ i j,i≠j → c j∉F i)
    (other : ∀ i : I,∃j,j≠i) {η : ℝ} (ep : 0≤η) (slack : 0<π-maxAngle S-η)
    (sight : ∀ i j,i≠j → InCone (F i) (c j) (c j-c i) η)
    (size : 3≤∑ i,2^(Nat.clog 2 (F i).card)) :
    alpha (∑ i,2^(Nat.clog 2 (F i).card))≤maxAngle S+η := by
  classical
  have inj : Function.Injective c := by
    intro i j eq
    by_contra ne
    exact ext i j ne (eq ▸ mem i)
  have all_axes (i : I) := select_axes (sub i) (mem i) ep slack (by
    obtain ⟨j,ne⟩:=other i
    exact ⟨c j,sub j (mem j),ext i j ne.symm,sight i j ne.symm⟩)
  choose v unit internal outside using all_axes
  have nv (i : I) (p) : v i p≠0 := by
    intro e
    have h:=unit i p
    rw [e,norm_zero] at h
    exact zero_ne_one h
  let A : R56.Decorated.Axes c (fun i=>Nat.clog 2 (F i).card) (maxAngle S+η) :=
    ⟨v,nv,internal,fun i j ne k r hr=>outside i (c j) (sub j (mem j)) (ext i j ne) (sight i j ne) k r hr⟩
  apply R56.Decorated.alpha_lift inj (by linarith [maxAngle_nonneg S]) size _ A
  intro i j k ij kj
  by_cases eq : i=k
  · subst k
    change angle (c i-c j) (c i-c j)≤_
    rw [angle_self (sub_ne_zero.mpr (inj.ne ij))]
    linarith [maxAngle_nonneg S]
  · linarith [angle_le_maxAngle (sub i (mem i)) (sub j (mem j)) (sub k (mem k))
        (inj.ne ij) (inj.ne eq) (inj.ne kj.symm)]

/-- Finite aperture obstruction at the existing thirty-nine-point root. -/
theorem aperture_thirty_nine {I : Type*} [Fintype I] {S : Finset Point} (F : I→Finset Point)
    (c : I→Point) (sub : ∀ i,F i⊆S) (mem : ∀ i,c i∈F i) (ext : ∀ i j,i≠j → c j∉F i)
    (other : ∀ i : I,∃j,j≠i) {η : ℝ} (ep : 0≤η)
    (sight : ∀ i j,i≠j → InCone (F i) (c j) (c j-c i) η)
    (room : 39≤∑ i,2^(Nat.clog 2 (F i).card)) : 9*π/11≤maxAngle S+η := by
  by_cases slack : 0<π-maxAngle S-η
  · rw [←R43.FiniteStrata.alpha_thirty_nine]
    exact (alpha_mono (by decide : 3≤39) room).trans
      (alpha_rounded F c sub mem ext other ep slack sight (by omega))
  · linarith [pi_pos]

end R56.Rounding
#print axioms R56.Rounding.select_axes
#print axioms R56.Rounding.alpha_rounded
#print axioms R56.Rounding.aperture_thirty_nine
