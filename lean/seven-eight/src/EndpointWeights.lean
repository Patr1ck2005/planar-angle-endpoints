import WeightedApexFans
import EnclosedAngle

noncomputable section
namespace R96.Endpoint
open JSP404 Real InnerProductGeometry R54.GapTest R55.WeightedCollision R92.Tight

/-- At 120 degrees, two microscopic axes would leave just one projective
line for all external chords. Three distinct centers already preclude this. -/
theorem weight_le_two {I : Type*} [Fintype I] {c : I→Point} (ci : Function.Injective c)
    {w : I→ℕ} (many : 3≤Fintype.card I) (A : Admissible w c (2*π/3)) (i : I) :
    dim w i≤1 ∧ w i≤2 := by
  classical
  obtain ⟨_,mac,v,unit,inter,out⟩:=A
  have bound : dim w i≤1:=by
    by_contra! big
    let b : Fin (dim w i):=⟨0,by omega⟩
    let k : Fin (dim w i):=⟨1,big⟩
    have bk : b≠k:=by intro eq;have h:=congrArg Fin.val eq;norm_num [b,k] at h
    have nz (j : Fin (dim w i)) : v i j≠0:=by intro z;simpa [z] using unit i j
    obtain ⟨t,_,_,ref⟩:=polar _ (nz b)
    obtain ⟨z,zl,zh,Z⟩:=R95.Heavy.window ref (nz k)
      (fun r hr=>by simpa using inter i b k bk r 1 hr (Or.inr rfl))
    let J:={j : I // j≠i}
    let u (j : J):=c j.val-c i
    choose a lo hi H using fun j : J=>R95.Heavy.window ref (sub_ne_zero.mpr (ci.ne j.property))
      (fun r hr=>out i j j.property.symm b r hr)
    have sep (j : J) : π/3≤|z-a j|:=apart Z (H j)
      (abs_le.mpr ⟨by linarith [hi j,pi_pos],by linarith [lo j,pi_pos]⟩)
      (fun r hr=>by linarith only [out i j j.property.symm k r hr])
    have eq (j h : J) : a j=a h:=by
      have sj:=sep j
      have sh:=sep h
      rcases le_total z (a j) with x|x <;> rcases le_total z (a h) with y|y <;>
        first | (rw [abs_of_nonpos (by linarith only [x])] at sj) | (rw [abs_of_nonneg (by linarith only [x])] at sj)
      all_goals first | (rw [abs_of_nonpos (by linarith only [y])] at sh) | (rw [abs_of_nonneg (by linarith only [y])] at sh)
      all_goals linarith [lo j,hi j,lo h,hi h,pi_pos]
    have num : Fintype.card J=Fintype.card I-1:=by simp [J,Fintype.card_subtype_compl]
    let : Nontrivial J:=Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨j,h,jh⟩:=exists_pair_ne J
    exact R93.Interior.different_axes ci (by linarith [pi_pos] : 2*π/3<π) mac j.property h.property
      (fun e=>jh (Subtype.ext e)) (same_of_bearing (eq j h ▸ H j) (H h))
  refine ⟨bound,(Nat.le_pow_clog (by decide : 1<2) (w i)).trans ?_⟩
  change 2^(dim w i)≤2
  exact (Nat.pow_le_pow_right (by decide : 0<2) bound).trans_eq (pow_one _)

/-- Direct attainable-cap version for ordinary weighted profiles. -/
theorem attainable_weight_le_two {I : Type*} [Fintype I] {c : I→Point} (ci : Function.Injective c)
    {w : I→ℕ} (wp : ∀i,0<w i) (many : 3≤Fintype.card I) (hit : 2*π/3∈attainable w c) :
    ∀i,dim w i≤1 ∧ w i≤2 := by
  let : Nontrivial I:=Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  exact weight_le_two ci many ((R54.Profile.fixed_profile wp (fun j=>exists_ne j) ci).mp hit)

/-- An enclosed endpoint site has unit weight, without a prior site-count
assumption beyond nontriviality. -/
theorem enclosed_unit {I : Type*} [Fintype I] [Nontrivial I] {c : I→Point} (ci : Function.Injective c)
    {w : I→ℕ} (wp : ∀j,0<w j) (hit : 2*π/3∈attainable w c) (i : I)
    (inside : c i∈convexHull ℝ (c '' {a | a≠i})) : w i=1 := by
  have cap:=R89.Interior.enclosed_angle ci wp hit i inside
  have den : 0<(dim w i:ℝ)+3:=by positivity
  have lower : ((dim w i:ℝ)+3)*(π/3)≤π:=by
    apply (le_div_iff₀' den).mp
    linarith only [cap]
  have zero : dim w i=0:=by
    by_contra ne
    have dpos : 0<(dim w i:ℝ):=by exact_mod_cast Nat.pos_of_ne_zero ne
    nlinarith only [lower,mul_pos dpos pi_pos]
  have le:=Nat.le_pow_clog (by decide : 1<2) (w i)
  change w i≤2^(dim w i) at le
  rw [zero,pow_zero] at le
  have:=wp i
  omega

end R96.Endpoint
#print axioms R96.Endpoint.weight_le_two
#print axioms R96.Endpoint.enclosed_unit
#print axioms R96.Endpoint.attainable_weight_le_two
