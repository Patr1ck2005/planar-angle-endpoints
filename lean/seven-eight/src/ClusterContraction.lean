import FixedCenterGap
import FiniteGapScore
import ProfileSamples

noncomputable section
namespace R62.Contraction
open Real JSP404 Filter Topology R51.Anchored R54.Profile R54.GapTest
open R55.WeightedCollision R56.Windows InnerProductGeometry

/-- Lift a viewing direction from the physical centers to nearby ordinary labeled samples. -/
private theorem wall_limit {I : Type*} [Fintype I] {c : I → Point} (ci : Function.Injective c)
    {w : I → ℕ} (pos : ∀ i, 0 < w i) (U : Finset I)
    {f : ℕ → Labels w → Point} (inj : ∀ n, Function.Injective (f n))
    (lim : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (c x.1)))
    {t W η e : ℝ} (ep : 0 < e)
    (wall : Wall (Finset.univ.image c) (U.image c) t W η) :
    ∀ᶠ n in atTop, Wall (diagram (f n)) ((U.sigma (fun i => (Finset.univ : Finset (Fin (w i))))).image (f n))
      t W (η+e) := by
  classical
  obtain ⟨p,ps,pf,a,b,ra,cone,hW⟩ := wall
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp ps
  have jout : j ∉ U := fun h => pf (Finset.mem_image_of_mem c h)
  let v := R37.SignedFan.oriented a b
  have vn : v ≠ 0 := by
    intro z
    have h : ‖v‖=1 := by cases b <;> simp [v,R37.SignedFan.oriented,norm_circleDirection]
    simp [z] at h
  have seen (x : Labels w) : ∀ᶠ n in atTop, x.1 ∈ U →
      angle v (f n (rep pos j)-f n x) ≤ η+e := by
    by_cases mem : x.1 ∈ U
    · have ne : j ≠ x.1 := fun h => jout (h ▸ mem)
      have bound := cone (c x.1) (Finset.mem_image_of_mem c mem)
      have l := angle_lim vn (sub_ne_zero.mpr (ci.ne ne)) tendsto_const_nhds
        ((lim (rep pos j)).sub (lim x))
      have h : angle v (c j-c x.1)<η+e := by change angle v (c j-c x.1)≤η at bound; linarith
      exact (l.eventually_lt tendsto_const_nhds h).mono (fun _ hn _ => hn.le)
    · exact Eventually.of_forall (fun _ hx => (mem hx).elim)
  filter_upwards [Filter.eventually_all.mpr seen] with n hn
  refine ⟨f n (rep pos j),Finset.mem_image_of_mem _ (Finset.mem_univ _),?_,a,b,ra,?_,hW⟩
  · intro hx
    obtain ⟨x,hx,eq⟩ := Finset.mem_image.mp hx
    have ex := inj n eq
    apply jout
    have xm := (Finset.mem_sigma.mp hx).1
    simpa [ex,rep] using xm
  · intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    exact hn x (Finset.mem_sigma.mp hx).1

/-- A cluster of arbitrary attainable fibers, counted with its full label multiplicities.
The walls and cone apertures are measured on the ordinary center set itself. -/
theorem weighted_cluster {I : Type*} [Fintype I] {w : I → ℕ} {c : I → Point}
    (ci : Function.Injective c) (pos : ∀ i, 0 < w i) {θ : ℝ} (att : θ ∈ attainable w c)
    (U : Finset I) {m : ℕ} (mp : 0 < m) (t : ℝ) (ht : 0 ≤ t ∧ t < π)
    (W η : ℕ → ℝ) (B : Fin m → ℕ) (first : W 0=t) (last : W m=t+π)
    (wall : ∀ j≤m, Wall (Finset.univ.image c) (U.image c) t (W j) (η j))
    (below : θ<π)
    (fit : ∀ j : Fin m, W (j.val+1)-W j+η j+η (j.val+1) < ((B j:ℝ)+2)*(π-θ)) :
    ∑ i ∈ U,w i ≤ 2^(∑ j,B j) := by
  classical
  let d (n : ℕ) : ℝ := 1/((n:ℝ)+1)
  have dp (n : ℕ) : 0<d n := by dsimp [d]; positivity
  have dz : Tendsto d atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have room (j : Fin m) : ∀ᶠ n in atTop,
      W (j.val+1)-W j+(η j+d n)+(η (j.val+1)+d n) <
        ((B j:ℝ)+2)*(π-θ-d n) := by
    have left : Tendsto (fun n => W (j.val+1)-W j+(η j+d n)+(η (j.val+1)+d n)) atTop
        (𝓝 (W (j.val+1)-W j+η j+η (j.val+1))) := by
      simpa using (tendsto_const_nhds.add (tendsto_const_nhds.add dz)).add (tendsto_const_nhds.add dz)
    have right : Tendsto (fun n => ((B j:ℝ)+2)*(π-θ-d n)) atTop (𝓝 (((B j:ℝ)+2)*(π-θ))) := by
      simpa using tendsto_const_nhds.mul (tendsto_const_nhds.sub dz)
    exact left.eventually_lt right (fit j)
  obtain ⟨k,good,small⟩ := ((Filter.eventually_all.mpr room).and
    (dz.eventually_lt tendsto_const_nhds (sub_pos.mpr below))).exists
  choose f inj near cap using fun n => att (d n) (dp n)
  have lim (x : Labels w) : Tendsto (fun n=>f n x) atTop (𝓝 (c x.1)) :=
    tendsto_iff_dist_tendsto_zero.mpr (squeeze_zero (fun _ => dist_nonneg) (fun n=>(near n x).le) dz)
  let L := U.sigma (fun i => (Finset.univ : Finset (Fin (w i))))
  have card (n : ℕ) : (L.image (f n)).card = ∑ i ∈ U,w i := by
    rw [Finset.card_image_of_injective _ (inj n)]
    simp [L,Finset.card_sigma]
  have wlim (j : Fin (m+1)) := wall_limit ci pos U inj lim (dp k) (wall j (by omega))
  obtain ⟨n,all,sn⟩ := ((Filter.eventually_all.mpr wlim).and
    (dz.eventually_lt tendsto_const_nhds (dp k))).exists
  have cp : maxAngle (diagram (f n)) < θ+d k := by
    have h:=cap n
    change maxAngle (diagram (f n)) < θ+d n at h
    linarith
  have sub : L.image (f n) ⊆ diagram (f n) := by
    intro x hx
    obtain ⟨y,_,rfl⟩:=Finset.mem_image.mp hx
    exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  by_cases two : 2≤(L.image (f n)).card
  · have cnt := multiple_anchor_capacity sub two mp t ht W (fun j => η j+d k) B first last
      (fun j hj => all (⟨j,by omega⟩ : Fin (m+1))) (by linarith) (fun j => by
        exact (good j).trans_le (mul_le_mul_of_nonneg_left (by linarith) (by positivity)))
    rw [←card n]
    exact (Nat.clog_le_iff_le_pow (by decide : 1<2)).mp cnt
  · rw [←card n]
    exact le_trans (by omega : (L.image (f n)).card≤1) (Nat.one_le_pow _ _ (by decide))

end R62.Contraction
#print axioms R62.Contraction.weighted_cluster

