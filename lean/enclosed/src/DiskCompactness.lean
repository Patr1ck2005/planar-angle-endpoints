import ProfilePacking

noncomputable section
namespace R69.Stability
open JSP404 R54.Profile R55.WeightedCollision Filter Topology

/-- Disk centers are arbitrary plane points and can be outside the configuration. -/
def Disks (b : ℕ) (S : Finset Point) (r : ℝ) : Prop :=
  ∃c : Fin b→Point,∀x∈S,∃i,dist x (c i)≤r

theorem packing_excludes_disks {n b : ℕ} (more : b<n) {S : Finset Point} {r d : ℝ}
    (room : 2*r≤d) (pack : Separated n S d) : ¬Disks b S r := by
  rintro ⟨c,cover⟩
  obtain ⟨z,mem,apart⟩:=pack
  choose a near using fun j=>cover (z j) (mem j)
  have inj : Function.Injective a := by
    intro i j eq
    by_contra ne
    have h:=dist_triangle (z i) (c (a j)) (z j)
    rw [dist_comm (c (a j)) (z j),←eq] at h
    have hi:=near i
    have hj:=near j
    rw [←eq] at hj
    linarith [apart i j ne]
  have count:=Fintype.card_le_of_injective a inj
  simp only [Fintype.card_fin] at count
  omega

def PackingLaw (N b : ℕ) (B : ℝ) : Prop :=
  ∀ε : ℝ,0<ε → ∃δ : ℝ,0<δ ∧ ∀S : Finset Point,S.card=N → maxAngle S≤B-ε →
    Separated (b+1) S (δ*Metric.diam (S:Set Point))

def DiskLaw (N b : ℕ) (B : ℝ) : Prop :=
  ∀ε : ℝ,0<ε → ∃δ : ℝ,0<δ ∧ ∀S : Finset Point,S.card=N → maxAngle S≤B-ε →
    ∀m≤b,¬Disks m S (δ*Metric.diam (S:Set Point))

theorem disk_of_packing {N b : ℕ} {B : ℝ} (law : PackingLaw N b B) : DiskLaw N b B := by
  intro ε ep
  obtain ⟨δ,dp,main⟩:=law ε ep
  exact ⟨δ/2,by positivity,fun S card angle m small=>packing_excludes_disks (by omega : m<b+1)
    (by ring_nf;exact le_rfl) (main S card angle)⟩

/-- A violation on m distinct sites produces ordinary positive-diameter samples at
every small tolerance, covered by m disks of arbitrarily small relative radius. -/
theorem sites_of_disks {N b : ℕ} {B : ℝ} (law : DiskLaw N b B) : SiteLaw N b B := by
  intro m two small c ci w wp mass θ att
  by_contra! bad
  let ε:=(B-θ)/2
  have ep : 0<ε := by dsimp [ε];linarith
  obtain ⟨δ,dp,no⟩:=law ε ep
  let i : Fin m:=⟨0,by omega⟩
  let j : Fin m:=⟨1,by omega⟩
  have ne : i≠j:=by intro h;have v:=congrArg Fin.val h;norm_num [i,j] at v
  let D:=dist (c i) (c j)
  have Dp : 0<D:=dist_pos.mpr (ci.ne ne)
  let η:=min ε (min (D/4) (δ*D/4))
  have ηp : 0<η:=lt_min ep (lt_min (by positivity) (by positivity))
  have lim1 : η≤ε:=min_le_left _ _
  have lim2 : η≤D/4:=(min_le_right _ _).trans (min_le_left _ _)
  have lim3 : η≤δ*D/4:=(min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨f,fi,near,angle⟩:=att η ηp
  let S:=diagram f
  have card : S.card=N := by
    change (Finset.univ.image f).card=N
    rw [Finset.card_image_of_injective _ fi,Finset.card_univ,Fintype.card_sigma]
    simpa using mass
  have cap : maxAngle S≤B-ε:=by
    change maxAngle S<θ+η at angle
    dsimp [ε] at lim1 ⊢
    linarith
  let pick (z : Fin m) : Label w:=⟨z,⟨0,wp z⟩⟩
  have mem (z : Fin m) : f (pick z)∈S:=Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have distS : dist (f (pick i)) (f (pick j))≤Metric.diam (S:Set Point) :=
    Metric.dist_le_diam_of_mem S.finite_toSet.isBounded (mem i) (mem j)
  have d1:=dist_triangle (c i) (f (pick i)) (c j)
  have d2:=dist_triangle (f (pick i)) (f (pick j)) (c j)
  have near1 : dist (c i) (f (pick i))<η:=by rw [dist_comm];exact near _
  have near2 : dist (f (pick j)) (c j)<η:=near _
  have size : D/2≤Metric.diam (S:Set Point):=by
    change D≤_ at d1
    linarith only [d1,d2,near1,near2,lim2,distS]
  have radius : η≤δ*Metric.diam (S:Set Point):=by
    have step:=mul_le_mul_of_nonneg_left size dp.le
    nlinarith only [step,lim3,mul_pos dp Dp]
  apply no S card cap m small
  refine ⟨c,?_⟩
  intro x hx
  obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hx
  exact ⟨a.1,(near a).le.trans radius⟩

/-- Exact compactness characterization at fixed ordinary cardinality. -/
theorem site_iff_packing {N b : ℕ} (ge : 3≤N) (B : ℝ) :
    SiteLaw N b B ↔ PackingLaw N b B :=
  ⟨fun h _ ep=>uniform_packing ge h ep,fun h=>sites_of_disks (disk_of_packing h)⟩

theorem site_iff_disks {N b : ℕ} (ge : 3≤N) (B : ℝ) :
    SiteLaw N b B ↔ DiskLaw N b B :=
  ⟨fun h=>disk_of_packing ((site_iff_packing ge B).mp h),sites_of_disks⟩

/-- A vanishing relative-radius cover by b arbitrary moving disks forces the
asymptotic angle lower bound, even if some centers coincide or are unused. -/
theorem vanishing_disks {N b : ℕ} (ge : 3≤N) {B : ℝ} (law : SiteLaw N b B)
    (S : ℕ→Finset Point) (card : ∀n,(S n).card=N) (r : ℕ→ℝ)
    (van : Tendsto r atTop (𝓝 0)) (cover : ∀n,Disks b (S n) (r n*Metric.diam (S n:Set Point))) :
    ∀ε : ℝ,0<ε → ∀ᶠ n in atTop,B-ε<maxAngle (S n) := by
  intro ε ep
  obtain ⟨δ,dp,exclude⟩:=(site_iff_disks ge B).mp law ε ep
  filter_upwards [van.eventually_lt tendsto_const_nhds dp] with n lt
  by_contra! angle
  apply exclude (S n) (card n) angle b le_rfl
  obtain ⟨c,hit⟩:=cover n
  refine ⟨c,?_⟩
  intro x hx
  obtain ⟨i,inside⟩:=hit x hx
  exact ⟨i,inside.trans (mul_le_mul_of_nonneg_right lt.le Metric.diam_nonneg)⟩

#print axioms site_iff_packing
#print axioms site_iff_disks
#print axioms vanishing_disks
end R69.Stability
