import OriginalGapMinimum
import ShapeDeletion
noncomputable section
namespace R65.Retention
open Real JSP404 R54.GapTest R55.WeightedCollision R56.Windows Finset

/-- Choose the required number of extra labels from the disjoint finite fibers. -/
private theorem fill {I : Type*} [Fintype I] (lo hi : I→ℕ) (fits : ∀i,lo i≤hi i)
    (N : ℕ) (lb : (∑i,lo i)≤N) (ub : N≤∑i,hi i) :
    ∃u : I→ℕ,(∀i,lo i≤u i) ∧ (∀i,u i≤hi i) ∧ (∑i,u i)=N := by
  classical
  let avail : Finset (I×ℕ):=univ.biUnion (fun i=>({i}:Finset I) ×ˢ range (hi i-lo i))
  have mem (i : I) (a : ℕ) : (i,a)∈avail ↔ a<hi i-lo i := by simp [avail]
  have fiber (i : I) : avail.filter (fun z=>z.1=i)=({i}:Finset I) ×ˢ range (hi i-lo i) := by
    ext ⟨j,a⟩
    simp only [mem_filter,mem,mem_product,mem_singleton,mem_range]
    aesop
  have cardA : avail.card=∑i,(hi i-lo i) := by
    rw [card_eq_sum_card_fiberwise (f:=Prod.fst) (t:=univ) (fun _ _=>mem_univ _)]
    simp [fiber]
  have cap : (∑i,hi i)=(∑i,lo i)+(∑i,(hi i-lo i)) := by
    rw [←sum_add_distrib]
    exact sum_congr rfl (fun i _=>by have:=fits i;omega)
  obtain ⟨T,sub,cardT⟩:=exists_subset_card_eq (s:=avail) (show N-(∑i,lo i)≤avail.card by omega)
  let count (i : I):=(T.filter (fun z=>z.1=i)).card
  have sumT : T.card=∑i,count i := card_eq_sum_card_fiberwise (t:=univ) (fun _ _=>mem_univ _)
  refine ⟨fun i=>lo i+count i,fun i=>Nat.le_add_right _ _,?_,?_⟩
  · intro i
    have cmp:=card_le_card (filter_subset_filter (p:=fun z : I×ℕ=>z.1=i) sub)
    rw [fiber] at cmp
    simp only [card_product,card_singleton,one_mul,card_range] at cmp
    change lo i+(T.filter _).card≤hi i
    have:=fits i
    omega
  · rw [sum_add_distrib,←sumT,cardT];omega

def capacity {I : Type*} [Fintype I] {m : I→ℕ} (R : ∀i,Row (m i)) (θ : ℝ) : ℕ :=
  ∑i,2^(score R i (π-θ))

theorem fits_iff {I : Type*} [Fintype I] [Nontrivial I] {c : I→Point} (ci : Function.Injective c)
    {m : I→ℕ} (R : ∀i,Row (m i)) (front : Represents R c) (back : Witnessed R c)
    {θ : ℝ} (pos : 0≤θ) (below : θ<π) (legal : Macro c θ)
    {w : I→ℕ} (wp : ∀i,0<w i) :
    θ∈attainable w c ↔ ∀i,w i≤2^(score R i (π-θ)) := by
  rw [fixed_centers_iff R ci front back wp θ,or_iff_right below.not_ge]
  simp only [pos,legal,true_and,dim,Nat.clog_le_iff_le_pow (by decide : 1<2)]

theorem allocation_iff {I : Type*} [Fintype I] [Nontrivial I] {c : I→Point} (ci : Function.Injective c)
    {m : I→ℕ} (R : ∀i,Row (m i)) (front : Represents R c) (back : Witnessed R c)
    {θ : ℝ} (pos : 0≤θ) (below : θ<π) (legal : Macro c θ)
    (lo : I→ℕ) (positive : ∀i,0<lo i) (fits : ∀i,lo i≤2^(score R i (π-θ))) (N : ℕ) :
    (∃u : I→ℕ,(∀i,lo i≤u i) ∧ (∑i,u i)=N ∧ θ∈attainable u c) ↔
      (∑i,lo i)≤N ∧ N≤capacity R θ := by
  constructor
  · rintro ⟨u,low,rfl,hit⟩
    have top:=(fits_iff ci R front back pos below legal (fun i=>(positive i).trans_le (low i))).mp hit
    exact ⟨sum_le_sum (fun i _=>low i),sum_le_sum (fun i _=>top i)⟩
  · rintro ⟨lb,ub⟩
    obtain ⟨u,low,up,mass⟩:=fill lo _ fits N lb ub
    exact ⟨u,low,mass,(fits_iff ci R front back pos below legal (fun i=>(positive i).trans_le (low i))).mpr up⟩

theorem positive_mass_iff {I : Type*} [Fintype I] [Nontrivial I] {c : I→Point} (ci : Function.Injective c)
    {m : I→ℕ} (R : ∀i,Row (m i)) (front : Represents R c) (back : Witnessed R c)
    {θ : ℝ} (pos : 0≤θ) (below : θ<π) (legal : Macro c θ) (N : ℕ) :
    (∃u : I→ℕ,(∀i,0<u i) ∧ (∑i,u i)=N ∧ θ∈attainable u c) ↔
    Fintype.card I≤N ∧ N≤capacity R θ := by
  simpa only [Nat.one_le_iff_ne_zero, Nat.pos_iff_ne_zero,Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one] using
    allocation_iff ci R front back pos below legal (fun _=>1) (fun _=>by decide)
      (fun _=>Nat.two_pow_pos _) N

theorem retained_mass_iff {I J : Type*} [Fintype I] [Fintype J] [Nontrivial I] [Nontrivial J]
    {c : I→Point} (ci : Function.Injective c) {w : I→ℕ} (wp : ∀i,0<w i) {θ : ℝ} (below : θ<π)
    (original : θ∈attainable w c) (e : J↪I) {m : J→ℕ} (R : ∀i,Row (m i))
    (front : Represents R (c∘e)) (back : Witnessed R (c∘e)) :
    (∃u : J→ℕ,(∀i,w (e i)≤u i) ∧ (∑i,u i)=∑i,w i ∧ θ∈attainable u (c∘e)) ↔
      (∑i,w i)≤capacity R θ := by
  have hit:=R58.CircleModel.restrict_attainable original e e.injective
  have ci':=ci.comp e.injective
  have laws:=(R54.Profile.fixed_profile (fun i=>wp (e i)) (fun i=>exists_ne i) ci').mp hit
  have fits:=(fits_iff ci' R front back laws.1 below laws.2.1 (fun i=>wp (e i))).mp hit
  have within : (∑i,w (e i))≤∑i,w i := by
    calc (∑i,w (e i)) = ∑i∈univ.map e,w i := (sum_map _ _ _).symm
         _ ≤ ∑i,w i := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _=>Nat.zero_le _)
  exact (allocation_iff ci' R front back laws.1 below laws.2.1 _ (fun i=>wp (e i)) fits _).trans
    (and_iff_right within)

/-- For an arbitrary retention of actual centers the wall lists exist. The same
lists work for all new totals, including a redistribution preserving old weights. -/
theorem actual_retention {I J : Type*} [Fintype I] [Fintype J] [Nontrivial I] [Nontrivial J]
    {c : I→Point} (ci : Function.Injective c) {w : I→ℕ} (wp : ∀i,0<w i)
    {θ : ℝ} (below : θ<π) (hit : θ∈attainable w c) (e : J↪I) :
    ∃m : J→ℕ,∃R : ∀i,Row (m i),Represents R (c∘e) ∧ Witnessed R (c∘e) ∧
      (∀M : ℕ,(∃u : J→ℕ,(∀i,0<u i) ∧ (∑i,u i)=M ∧ θ∈attainable u (c∘e)) ↔
        Fintype.card J≤M ∧ M≤capacity R θ) ∧
      ((∃u : J→ℕ,(∀i,w (e i)≤u i) ∧ (∑i,u i)=∑i,w i ∧ θ∈attainable u (c∘e)) ↔
        (∑i,w i)≤capacity R θ) := by
  obtain ⟨m,R,front,back⟩:=actual_rows (c∘e) (ci.comp e.injective)
  have restricted:=R58.CircleModel.restrict_attainable hit e e.injective
  have law:=(R54.Profile.fixed_profile (fun i=>wp (e i)) (fun i=>exists_ne i) (ci.comp e.injective)).mp restricted
  exact ⟨m,R,front,back,positive_mass_iff (ci.comp e.injective) R front back law.1 below law.2.1,
    retained_mass_iff ci wp below hit e R front back⟩

#print axioms actual_retention
#print axioms positive_mass_iff
#print axioms retained_mass_iff
end R65.Retention