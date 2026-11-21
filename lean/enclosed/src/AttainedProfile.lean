import NormalizedDiagrams

noncomputable section
namespace R57.Compact
open JSP404 R54.Profile Filter Topology

/-- Relabel an arbitrary finite map by its distinct values and the multiplicities
of their fibers. The equivalence preserves the limiting value of each label. -/
theorem relabel {N : ℕ} (L : Fin N→Point) (two : ∃ a b,L a≠L b) :
    ∃ m : ℕ, 2≤m ∧ ∃ c : Fin m→Point, Function.Injective c ∧
      ∃ w : Fin m→ℕ, (∀ i,0<w i) ∧ (∑ i,w i)=N ∧
      ∃ E : Labels w ≃ Fin N, ∀ x,L (E x)=c x.1 := by
  classical
  let C := Finset.univ.image L
  let label (x : Fin N) : C := ⟨L x,Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  let D := (Fintype.equivFin C).symm
  let m:=Fintype.card C
  let c (i : Fin m) : Point:=D i
  let tag (x : Fin N) : Fin m:=D.symm (label x)
  have proj (x : Fin N) : c (tag x)=L x := congrArg Subtype.val (D.apply_symm_apply (label x))
  have cinj : Function.Injective c := fun _ _ e=>D.injective (Subtype.ext e)
  have count : 2≤m := by
    obtain ⟨a,b,ne⟩:=two
    by_contra! small
    have ab : tag a=tag b := Fin.ext (by have h:=(tag a).isLt;have z:=(tag b).isLt;omega)
    exact ne ((proj a).symm.trans ((congrArg c ab).trans (proj b)))
  have hit (i : Fin m) : ∃ a,tag a=i := by
    obtain ⟨a,_,e⟩:=Finset.mem_image.mp (D i).property
    exact ⟨a,cinj ((proj a).trans e)⟩
  let w (i : Fin m) := Fintype.card {a // tag a=i}
  let F (i : Fin m) : Fin (w i) ≃ {a // tag a=i} := (Fintype.equivFin _).symm
  let E : Labels w ≃ Fin N := (Equiv.sigmaCongrRight F).trans (Equiv.sigmaFiberEquiv tag)
  have pos (i : Fin m) : 0<w i := by
    obtain ⟨a,ha⟩:=hit i
    exact Fintype.card_pos_iff.mpr ⟨⟨a,ha⟩⟩
  have sum : (∑ i,w i)=N := by
    have card:=Fintype.card_congr E
    change Fintype.card (Sigma (fun i=>Fin (w i)))=Fintype.card (Fin N) at card
    rw [Fintype.card_sigma,Fintype.card_fin] at card
    simpa only [Fintype.card_fin] using card
  refine ⟨m,count,c,cinj,w,pos,sum,E,?_⟩
  rintro ⟨i,j⟩
  exact (proj ((F i j).val)).symm.trans (congrArg c (F i j).property)

/-- Distinct centers of diameter one and their strictly positive multiplicities.
The labeled approximation predicate is exactly R54.Profile.Realizable. -/
def UnitProfile (N : ℕ) (θ : ℝ) : Prop :=
    ∃ m : ℕ, 2≤m ∧ ∃ c : Fin m→Point, Function.Injective c ∧
      (∀ i,dist (c i) 0≤1) ∧ (∀ i j,dist (c i) (c j)≤1) ∧
      (∃ i j,dist (c i) (c j)=1) ∧
      ∃ w : Fin m→ℕ, (∀ i,0<w i) ∧ (∑ i,w i)=N ∧ Realizable w c θ

theorem profile_of_limit {N : ℕ} {θ : ℝ} {L : Fin N→Point}
    (bound : ∀ i,dist (L i) 0≤1) (upper : ∀ i j,dist (L i) (L j)≤1)
    (pair : ∃ a b,dist (L a) (L b)=1)
    (near : ∀ e : ℝ,0<e → ∃ f : Fin N→Point, Function.Injective f ∧
      (∀ i,dist (f i) (L i)<e) ∧ maxAngle (diagram f)<θ+e) : UnitProfile N θ := by
  classical
  obtain ⟨a,b,diam⟩:=pair
  have ne : L a≠L b := by intro e; rw [e,dist_self] at diam;norm_num at diam
  obtain ⟨m,two,c,inj,w,pos,sum,E,eq⟩:=relabel L ⟨a,b,ne⟩
  let point (i : Fin m) : Fin N := E ⟨i,⟨0,pos i⟩⟩
  have rep (i : Fin m) : L (point i)=c i := eq ⟨i,⟨0,pos i⟩⟩
  have inv (x : Fin N) : L x=c (E.symm x).1 := by simpa using eq (E.symm x)
  refine ⟨m,two,c,inj,fun i=>(rep i) ▸ bound _,fun i j=>?_,?_,w,pos,sum,?_⟩
  · rw [←rep i,←rep j];exact upper _ _
  · exact ⟨(E.symm a).1,(E.symm b).1,by rw [←inv a,←inv b];exact diam⟩
  · intro e ep
    obtain ⟨f,fi,close,cap⟩:=near e ep
    let g (x : Labels w) := f (E x)
    have diagrams : diagram g=diagram f := by
      ext p
      constructor
      · rintro h
        obtain ⟨x,_,rfl⟩:=Finset.mem_image.mp h
        exact Finset.mem_image_of_mem _ (Finset.mem_univ (E x))
      · rintro h
        obtain ⟨x,_,rfl⟩:=Finset.mem_image.mp h
        exact Finset.mem_image.mpr ⟨E.symm x,Finset.mem_univ _,by simp [g]⟩
    exact ⟨g,fi.comp E.injective,fun x=>eq x ▸ close (E x),diagrams ▸ cap⟩

/-- A prescribed sequence furnishes a fixed profile at its limiting angle. -/
theorem profile_of_sequence {N : ℕ} (hn : 3≤N) (S : ℕ→Finset Point)
    (card : ∀ n,(S n).card=N) {θ : ℝ}
    (angles : Filter.Tendsto (fun n=>maxAngle (S n)) Filter.atTop (nhds θ)) : UnitProfile N θ := by
  obtain ⟨f,inj,_,same,k,mono,L,lb,lu,pair,coord⟩:=compact_subsequence hn S card
  apply profile_of_limit lb lu pair
  intro e ep
  have ang := (angles.comp mono.tendsto_atTop).eventually_lt tendsto_const_nhds (lt_add_of_pos_right θ ep)
  have all := Filter.eventually_all.mpr (fun i=>Metric.tendsto_nhds.mp (coord i) e ep)
  obtain ⟨n,hc,ha⟩:=(all.and ang).exists
  exact ⟨f (k n),inj _,hc,(same _).symm ▸ ha⟩

/-- The ordinary infimum always has a fixed labeled macroprofile. -/
theorem attained_profile {N : ℕ} (hn : 3≤N) :
    ∃ m : ℕ, 2≤m ∧ ∃ c : Fin m→Point, Function.Injective c ∧
      (∀ i,dist (c i) 0≤1) ∧ (∀ i j,dist (c i) (c j)≤1) ∧
      (∃ i j,dist (c i) (c j)=1) ∧
      ∃ w : Fin m→ℕ, (∀ i,0<w i) ∧ (∑ i,w i)=N ∧ Realizable w c (alpha N) := by
  obtain ⟨L,bound,upper,pair,near⟩:=compact_limit hn
  exact profile_of_limit bound upper pair near

end R57.Compact
#print axioms R57.Compact.relabel
#print axioms R57.Compact.profile_of_sequence
#print axioms R57.Compact.attained_profile
