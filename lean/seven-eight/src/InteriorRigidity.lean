import InteriorThreeChords

noncomputable section
open JSP404 Real InnerProductGeometry R87.Diameter R55.WeightedCollision R91.Interior

namespace R91.Rigid

private theorem no_same_ray {I : Type*} [Fintype I] {c : I → Point} (ci : Function.Injective c)
    (mac : Macro c (2*π/3)) {i j k : I} (ji : j≠i) (ki : k≠i) (jk : j≠k) :
    angle (c j-c i) (c k-c i) ≠ 0 := by
  intro zero
  change EuclideanGeometry.angle (c j) (c i) (c k)=0 at zero
  rcases EuclideanGeometry.angle_eq_zero_iff_eq_and_ne_or_sbtw.mp zero with ⟨eq,_⟩|h|h
  · exact jk (ci eq)
  · have b:=mac i j k ji.symm ki.symm jk
    rw [EuclideanGeometry.angle_eq_pi_iff_sbtw.mpr h] at b
    linarith [pi_pos]
  · have b:=mac i k j ki.symm ji.symm jk.symm
    rw [EuclideanGeometry.angle_eq_pi_iff_sbtw.mpr h] at b
    linarith [pi_pos]

private theorem forbidden_arc {u v : Point} {t a b : ℝ}
    (U : Head u (t+a)) (V : Head v (t+b))
    (lo : 2*π/3 < b-a) (hi : b-a < 4*π/3) :
    2*π/3 < angle u v := by
  by_cases crosses : π ≤ b-a
  · rw [wrap_angle U V crosses (by linarith [pi_pos])]
    linarith
  · have ab : |(t+a)-(t+b)| = b-a := by
      rw [abs_of_nonpos (by linarith [pi_pos])]
      ring
    rw [head_angle U V (by rw [ab]; linarith),ab]
    exact lo

private theorem offset {u v : Point} {t a : ℝ} (U : Head u t)
    (V : Head v (t+a)) (lo : -π ≤ a) (hi : a ≤ π) :
    angle u v = |a| := by
  have d : |t-(t+a)|=|a| := by rw [show t-(t+a) = -a by ring,abs_neg]
  rw [head_angle U V (by rw [d];exact abs_le.mpr ⟨lo,hi⟩),d]

private theorem same_head {u v : Point} {t : ℝ} (U : Head u t) (V : Head v t) :
    angle u v=0 := by simpa using head_angle U V (by simp [pi_pos.le])

private theorem signed_cases {a b : ℝ} (e : |a|=b) : a = -b ∨ a=b := by
  rcases le_total 0 a with h|h
  · right; simpa [abs_of_nonneg h] using e
  · left; rw [abs_of_nonpos h] at e; linarith

/-- The only rays meeting all three equal 120-degree caps coincide with one of the triple. -/
theorem exhaust_rays (u : Fin 3 → Point) (zero : ∀ k, u k≠0)
    (equal : ∀ a b, a≠b → angle (u a) (u b)=2*π/3) {w : Point} (wz : w≠0)
    (cap : ∀k, angle (u k) w ≤ 2*π/3) :
    ∃k, angle (u k) w=0 := by
  by_contra! different
  obtain ⟨t,U⟩:=head_exists (zero 0)
  obtain ⟨a,al,ah,A⟩:=full_head (u 1) (zero 1) t
  obtain ⟨b,bl,bh,B⟩:=full_head (u 2) (zero 2) t
  obtain ⟨s,sl,sh,S⟩:=full_head w wz t
  have ea : |a|=2*π/3 := (offset U A al ah).symm.trans (equal 0 1 (by decide))
  have eb : |b|=2*π/3 := (offset U B bl bh).symm.trans (equal 0 2 (by decide))
  have ne : a≠b := by
    rintro rfl
    have E:=equal 1 2 (by decide)
    linarith only [E,same_head A B,pi_pos]
  have h : ∃ k l : Fin 3, Head (u k) (t+-(2*π/3)) ∧ Head (u l) (t+2*π/3) := by
    rcases signed_cases ea with x|x <;> rcases signed_cases eb with y|y
    · exact (ne (x.trans y.symm)).elim
    · exact ⟨1,2,x ▸ A,y ▸ B⟩
    · exact ⟨2,1,y ▸ B,x ▸ A⟩
    · exact (ne (x.trans y.symm)).elim
  obtain ⟨k,l,L,R⟩:=h
  have cs := cap 0
  rw [offset U S sl sh] at cs
  have bounds:=abs_le.mp cs
  have nonzero : s ≠ 0 := by
    rintro rfl
    exact different 0 (same_head U (by simpa using S))
  have neLeft : s ≠ -(2*π/3) := by
    rintro rfl
    exact different k (same_head L S)
  have neRight : s ≠ 2*π/3 := by
    rintro rfl
    exact different l (same_head R S)
  rcases lt_or_gt_of_ne nonzero with neg|pos
  · have F:=forbidden_arc S R (by linarith) (by linarith [lt_of_le_of_ne bounds.1 (Ne.symm neLeft)])
    rw [angle_comm] at F
    exact (not_lt_of_ge (cap l)) F
  · have F:=forbidden_arc L S (by linarith) (by linarith [lt_of_le_of_ne bounds.2 neRight])
    exact (not_lt_of_ge (cap k)) F

/-- With an enclosed site and a global 120-degree macro cap the support has exactly four sites. -/
theorem four_sites {I : Type*} [Fintype I] {c : I → Point} (ci : Function.Injective c)
    {i : I} (inside : c i∈convexHull ℝ (c '' {a | a≠i}))
    (mac : Macro c (2*π/3)) : Fintype.card I=4 := by
  classical
  have mac' : Macro c (π-π/3) := by rwa [show π-π/3=2*π/3 by ring]
  obtain ⟨h,off,both⟩:=three_chords ci inside (δ:=π/3) (by positivity) mac'
  let u (k : Fin 3) := c (h k)-c i
  have nonz (k : Fin 3) : u k≠0 := sub_ne_zero.mpr (ci.ne (off k))
  have eq (a b : Fin 3) (ne : a≠b) : angle (u a) (u b)=2*π/3 := by
    change EuclideanGeometry.angle (c (h a)) (c i) (c (h b))=2*π/3
    obtain ⟨l,r⟩:=both a b ne
    linarith
  have covers (j : I) : j=i ∨ ∃ k, j=h k := by
    by_contra! missing
    obtain ⟨ji,all⟩:=missing
    have cap (k : Fin 3) : angle (u k) (c j-c i) ≤ 2*π/3 :=
      mac _ _ _ (off k) (all k).symm ji.symm
    obtain ⟨k,zero⟩:=exhaust_rays u nonz eq (sub_ne_zero.mpr (ci.ne ji)) cap
    exact no_same_ray ci mac (off k) ji (all k).symm zero
  have cover : (Finset.univ : Finset I)={i,h 0,h 1,h 2} := by
    ext j
    simp only [Finset.mem_univ,true_iff,Finset.mem_insert,Finset.mem_singleton]
    rcases covers j with e|⟨k,e⟩
    · exact Or.inl e
    · fin_cases k <;> simp_all
  have e01 := h.injective.ne (show (0 : Fin 3) ≠ 1 by decide)
  have e02 := h.injective.ne (show (0 : Fin 3) ≠ 2 by decide)
  have e12 := h.injective.ne (show (1 : Fin 3) ≠ 2 by decide)
  change (Finset.univ : Finset I).card=4
  rw [cover]
  simp [Ne.symm (off 0),Ne.symm (off 1),Ne.symm (off 2),e01,e02,e12]

end R91.Rigid

#print axioms R91.Rigid.exhaust_rays
#print axioms R91.Rigid.four_sites
