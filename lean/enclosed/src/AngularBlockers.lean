import DeletionBudget

noncomputable section
namespace R85.CriticalMass
open Real JSP404 R54.GapTest R55.WeightedCollision R56.Windows Finset R62.Contraction R65.Retention InnerProductGeometry

/-- A genuine trial axis kit. Both signs of its axes are available. -/
def InternalTrial {d : ℕ} (u : Fin d→Point) (θ : ℝ) : Prop :=
  (∀p,u p≠0) ∧ ∀p q,p≠q → ∀s : ℝ,s= -1 ∨ s=1 → angle (s • u p) (u q)≤θ

def Compatible {d : ℕ} (u : Fin d→Point) (θ : ℝ) (chord : Point) : Prop :=
  ∀p,∀s : ℝ,s= -1 ∨ s=1 → angle (s • u p) chord≤θ

/-- Exact sites obstructing the proposed axis kit, determined only by physical chords. -/
def blockers {m d : ℕ} (c : Fin m→Point) (θ : ℝ) (j : Fin m) (u : Fin d→Point) : Finset (Fin m) := by
  classical
  exact univ.filter fun i=>i≠j ∧ ¬Compatible u θ (c i-c j)

theorem trial_fits {I : Type*} {c : I→Point} {s : I→ℕ} (Q : ∀i,Row (s i))
    (back : Witnessed Q c) {θ : ℝ} (below : θ<π) (j : I) {d : ℕ} (u : Fin d→Point)
    (kit : InternalTrial u θ) (clear : ∀i,j≠i → Compatible u θ (c i-c j)) :
    d≤score Q j (π-θ) := by
  let R:=Q j
  choose a low high line using fun p=>lifted_polar (u p) (kit.1 p) (R.w 0)
  have span {x y:ℝ} (xl:R.w 0≤x) (xh:x≤R.w 0+π) (yl:R.w 0≤y) (yh:y≤R.w 0+π) :
      |x-y|≤π := abs_le.mpr ⟨by linarith,by linarith⟩
  apply packing R (sub_pos.mpr below) a (fun p=>⟨low p,by rw [R.period];exact high p⟩)
  · intro p q ne
    apply apart (line p) (line q) (span (low p) (high p) (low q) (high q))
    simpa only [sub_sub_cancel] using kit.2 p q ne
  · intro p z iz
    obtain ⟨i,ne,chord⟩:=back j z iz
    apply apart (line p) chord (span (low p) (high p) (R.ordered (Nat.zero_le z) iz)
        ((R.ordered iz le_rfl).trans_eq R.period))
    simpa only [sub_sub_cancel] using clear i ne p

variable {m : ℕ} {c : Fin m→Point} {θ : ℝ} {s : Fin m→ℕ} (R : ∀i,Row (s i))

/-- Any actual proposal for r additional axes encounters at least the displayed
total dyadic mass in its angular blockers, provided two sites survive its removal. -/
theorem blocker_mass {B v : ℕ} (ci : Function.Injective c) (full : capacity R θ=B+v)
    (crit : Critical c (B+1) θ) (below : θ<π) (front : Represents R c) (back : Witnessed R c)
    (j : Fin m) {r : ℕ} (rp : 0<r) (u : Fin (score R j (π-θ)+r)→Point)
    (kit : InternalTrial u θ) (two : 2≤(univ \ blockers c θ j u).card) :
    v+(2^r-1)*mass R θ j≤∑i∈blockers c θ j u,mass R θ i := by
  classical
  let D:=blockers c θ j u
  let G:=univ \ D
  have good (i : Fin m) (ok : i∉D) (ne : j≠i) : Compatible u θ (c i-c j) := by
    by_contra! h
    exact ok (mem_filter.mpr ⟨mem_univ _,ne.symm,h⟩)
  have non : D.Nonempty := by
    by_contra! empty
    have absurd:=trial_fits R back below j u kit (fun i ne=>good i (by simp [empty]) ne)
    omega
  have proper : G.card<m := by
    change (univ \ D).card<m
    rw [card_sdiff_of_subset (subset_univ _),card_univ,Fintype.card_fin]
    have p:=card_pos.mpr non
    have lim : D.card≤m := by simpa using card_le_univ D
    omega
  let o:=G.orderIsoOfFin (k:=G.card) rfl
  let e : Fin G.card↪Fin m:=⟨fun a=>(o a).val,fun _ _ he=>o.injective (Subtype.ext he)⟩
  have dj : j∉D := by simp [D,blockers]
  have gj : j∈G := mem_sdiff.mpr ⟨mem_univ _,dj⟩
  let j':=o.symm ⟨j,gj⟩
  have center : e j'=j := congrArg Subtype.val (o.apply_symm_apply ⟨j,gj⟩)
  have image : univ.map e=G := by
    ext i
    constructor
    · rintro mem;obtain ⟨q,_,rfl⟩:=mem_map.mp mem;exact (o q).prop
    · intro mem;exact mem_map.mpr ⟨o.symm ⟨i,mem⟩,mem_univ _,congrArg Subtype.val (o.apply_symm_apply ⟨i,mem⟩)⟩
  have which : removed e=D := by ext i;simp [removed,image,G]
  let : Nontrivial (Fin G.card) := Fintype.one_lt_card_iff_nontrivial.mp (by rw [Fintype.card_fin];exact two)
  obtain ⟨p,Q,fwd,rev⟩:=actual_rows (c∘e) (ci.comp e.injective)
  have clear (a : Fin G.card) (ne : j'≠a) : Compatible u θ ((c∘e) a-(c∘e) j') := by
    change Compatible u θ (c (e a)-c (e j'))
    rw [center]
    exact good (e a) (mem_sdiff.mp (o a).prop).2 (center ▸ e.injective.ne ne)
  have fit:=trial_fits Q rev below j' u kit clear
  have raise : score R (e j') (π-θ)+r≤score Q j' (π-θ) := by rwa [center]
  have charge:=single_charge R full crit below front two proper e Q fwd rev j' r raise
  simpa only [center,which] using charge

end R85.CriticalMass
#print axioms R85.CriticalMass.trial_fits
#print axioms R85.CriticalMass.blocker_mass
