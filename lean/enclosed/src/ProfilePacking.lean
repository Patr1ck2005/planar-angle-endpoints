import AttainedProfile
import CollisionSpectrum

noncomputable section
namespace R69.Stability
open JSP404 R54.Profile R55.WeightedCollision R57.Compact Filter Topology

/-- Lower bound on the scores realizable by at most b distinct macrocenters with
positive multiplicities of total N. Diameter normalization always leaves two centers. -/
def SiteLaw (N b : ℕ) (B : ℝ) : Prop :=
  ∀ (m : ℕ),2≤m → m≤b → ∀(c : Fin m→Point),Function.Injective c →
    ∀(w : Fin m→ℕ),(∀i,0<w i) → (∑i,w i)=N → ∀θ∈attainable w c,B≤θ

def Separated (q : ℕ) (S : Finset Point) (d : ℝ) : Prop :=
  ∃ z : Fin q→Point,(∀i,z i∈S) ∧ ∀i j,i≠j → d<dist (z i) (z j)

private theorem relabel_diagram {I J : Type*} [Fintype I] [Fintype J] (E : I≃J) (f : J→Point) :
    diagram (f ∘ E)=diagram f := by
  ext y
  simp only [diagram,Finset.mem_image,Finset.mem_univ,true_and,Function.comp_apply]
  exact ⟨fun ⟨i,h⟩=>⟨E i,h⟩,fun ⟨j,h⟩=>⟨E.symm j,by simpa using h⟩⟩

/-- Pull a packing back to an ordinary set through the actual similarity, keeping
track of the original diameter even if the selected normalization varies. -/
private theorem pullback {N q : ℕ} {S : Finset Point} {f : Fin N→Point}
    (sim : SimilarImage S f) (upper : ∀i j,dist (f i) (f j)≤2)
    {r : ℝ} (rp : 0≤r) (z : Fin q→Fin N) (pack : ∀i j,i≠j → 2*r<dist (f (z i)) (f (z j))) :
    Separated q S (r*Metric.diam (S:Set Point)) := by
  obtain ⟨o,_,D,dp,img⟩:=sim
  let T (x : Point):=D⁻¹ • (x-o)
  have scale (x y : Point) : D*dist (T x) (T y)=dist x y := by
    dsimp [T]
    rw [dist_eq_norm,←smul_sub,show (x-o)-(y-o)=x-y by abel,norm_smul,Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr dp),←mul_assoc,mul_inv_cancel₀ dp.ne',one_mul,dist_eq_norm]
  have fw (i : Fin N) : ∃x∈S,T x=f i := by
    have h : f i∈diagram f := Finset.mem_image_of_mem _ (Finset.mem_univ _)
    rw [img] at h;exact Finset.mem_image.mp h
  have bw (x : Point) (hx : x∈S) : ∃i,f i=T x := by
    have h : T x∈diagram f := by rw [img];exact Finset.mem_image_of_mem _ hx
    obtain ⟨i,_,hi⟩:=Finset.mem_image.mp h
    exact ⟨i,hi⟩
  have size : Metric.diam (S:Set Point)≤2*D := by
    apply Metric.diam_le_of_forall_dist_le (by positivity)
    intro x hx y hy
    obtain ⟨i,hi⟩:=bw x hx
    obtain ⟨j,hj⟩:=bw y hy
    have h:=mul_le_mul_of_nonneg_left (upper i j) dp.le
    rwa [hi,hj,scale,mul_comm D] at h
  choose v mem back using fw
  refine ⟨v ∘ z,fun i=>mem _,fun i j ij=>?_⟩
  calc r*Metric.diam (S:Set Point)≤r*(2*D) := mul_le_mul_of_nonneg_left size rp
       _ = D*(2*r) := by ring
       _ < D*dist (f (z i)) (f (z j)) := mul_lt_mul_of_pos_left (pack i j ij) dp
       _ = dist (v (z i)) (v (z j)) := by rw [←back,←back,scale]

/-- Every fixed positive angular deficit below a b-site lower bound gives a uniform
positive relative diameter scale at which an ordinary N-point set packs b+1 points. -/
theorem uniform_packing {N b : ℕ} (ge : 3≤N) {B : ℝ} (law : SiteLaw N b B)
    {ε : ℝ} (ep : 0<ε) :
    ∃δ : ℝ,0<δ ∧ ∀S : Finset Point,S.card=N → maxAngle S≤B-ε →
      Separated (b+1) S (δ*Metric.diam (S:Set Point)) := by
  classical
  by_contra! fail
  let d (n : ℕ) : ℝ:=1/((n:ℝ)+1)
  have dp (n) : 0<d n := by dsimp [d];positivity
  have dz : Tendsto d atTop (𝓝 0):=tendsto_one_div_add_atTop_nhds_zero_nat
  choose S card angle notPack using fun n=>fail (d n) (dp n)
  obtain ⟨f,inj,sim,same,k,mono,L,_,lu,pair,conv⟩:=compact_subsequence ge S card
  obtain ⟨a,b',far⟩:=pair
  have diff : L a≠L b' := by intro e;rw [e,dist_self] at far;norm_num at far
  obtain ⟨m,two,c,ci,w,wp,sz,E,fib⟩:=relabel L ⟨a,b',diff⟩
  have hit : B-ε ∈ attainable w c := by
    intro t tp
    have closeness (i : Fin N) : ∀ᶠ n in atTop,dist (f (k n) i) (L i)<t := Metric.tendsto_nhds.mp (conv i) t tp
    obtain ⟨n,close⟩:=(eventually_all.mpr closeness).exists
    refine ⟨f (k n) ∘ E,(inj _).comp E.injective,fun x=>?_,?_⟩
    · change dist (f _ (E x)) (c x.1)<t
      rw [←fib];exact close _
    · change maxAngle (diagram (f (k n) ∘ E))<B-ε+t
      rw [relabel_diagram,same]
      exact (angle _).trans_lt (lt_add_of_pos_right _ tp)
  have enough : b+1≤m := by
    by_contra! small
    have lower:=law m two (by omega) c ci w wp sz _ hit
    linarith
  let cidx (j : Fin (b+1)) : Fin m:=Fin.castLE enough j
  let z (j : Fin (b+1)) : Fin N:=E ⟨cidx j,⟨0,wp _⟩⟩
  have center (j) : L (z j)=c (cidx j):=fib _
  have zero : Tendsto (fun n=>2*d (k n)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x:=(2:ℝ))).mul (dz.comp mono.tendsto_atTop)
  have pairs (i j : Fin (b+1)) : ∀ᶠ n in atTop,i≠j → 2*d (k n)<dist (f (k n) (z i)) (f (k n) (z j)) := by
    by_cases ne : i=j
    · exact Eventually.of_forall (fun _ h=>(h ne).elim)
    have sep : 0<dist (L (z i)) (L (z j)) := by
      rw [center,center,dist_pos]
      exact ci.ne (fun e=>ne (Fin.ext (congrArg (fun a : Fin m=>a.val) e)))
    exact (zero.eventually_lt ((conv _).dist (conv _)) sep).mono (fun _ h _=>h)
  have up (i j : Fin N) : ∀ᶠ n in atTop,dist (f (k n) i) (f (k n) j)≤2 :=
    (((conv i).dist (conv j)).eventually_lt tendsto_const_nhds ((lu i j).trans_lt (by norm_num : (1:ℝ)<2))).mono
      (fun _ h=>h.le)
  have all1:=eventually_all.mpr (fun i=>eventually_all.mpr (up i))
  have all2:=eventually_all.mpr (fun i=>eventually_all.mpr (pairs i))
  obtain ⟨n,upper,good⟩:=(all1.and all2).exists
  exact notPack (k n) (pullback (sim _) upper (dp _).le z good)

#print axioms uniform_packing
end R69.Stability
