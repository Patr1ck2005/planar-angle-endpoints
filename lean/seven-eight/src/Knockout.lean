import JSP404.Basic
import Mathlib.Geometry.Euclidean.Triangle

noncomputable section
open scoped Classical
namespace R58.Knockout
open Finset Real JSP404

variable {V C : Type*} [PseudoMetricSpace V] [DecidableEq V] [DecidableEq C]

def colors (S : Finset V) (c : V→V→C) (v : V) := (S.erase v).image (c v)

def Short (S : Finset V) (c : V→V→C) : Prop :=
  ∀ v∈S,∀ a∈S,∀ b∈S,v≠a → v≠b → a≠b → c v a=c v b → dist a b<dist v a

omit [PseudoMetricSpace V] in
private theorem color_mono {T S : Finset V} (sub : T⊆S) (c : V→V→C) (v : V) :
    colors T c v⊆colors S c v :=
  Finset.image_subset_image (Finset.erase_subset_erase v sub)

/-- In a closest pair each endpoint's color at the opposite endpoint is private. -/
theorem closest_drops {S : Finset V} {c : V→V→C} (short : Short S c) {a b : V}
    (ha : a∈S) (hb : b∈S) (ab : a≠b)
    (least : ∀ i∈S,∀ j∈S,i≠j → dist a b≤dist i j) :
    (colors (S.erase a) c b).card+1≤(colors S c b).card := by
  classical
  have missing : c b a∉colors (S.erase a) c b := by
    intro mem
    obtain ⟨x,hx,eq⟩:=Finset.mem_image.mp mem
    obtain ⟨xb,xa,hxs⟩ : x≠b ∧ x≠a ∧ x∈S :=
      ⟨(Finset.mem_erase.mp hx).1,(Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1,
        Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)⟩
    have less:=short b hb a ha x hxs ab.symm xb.symm xa.symm eq.symm
    rw [dist_comm b a] at less
    exact (not_lt_of_ge (least a ha x hxs xa.symm)) less
  have orig : c b a∈colors S c b := Finset.mem_image_of_mem _ (Finset.mem_erase.mpr ⟨ab,ha⟩)
  have sub : insert (c b a) (colors (S.erase a) c b)⊆colors S c b :=
    Finset.insert_subset orig (color_mono (Finset.erase_subset _ _) _ _)
  simpa [missing] using Finset.card_le_card sub

/-- Arbitrarily weighted finite configurations admit a sequence of closest-pair
deletions. The lighter load is absorbed by the heavier endpoint. -/
theorem capacity (S : Finset V) (c : V→V→C) (short : Short S c)
    (n : ℕ) (w : V→ℕ) (room : ∀v∈S,w v+(colors S c v).card≤n) :
    (∑ v∈S,2^w v)≤2^n := by
  classical
  induction S using Finset.strongInductionOn generalizing w with
  | _ S ih =>
    by_cases large : 1<S.card
    · obtain ⟨u,hu,v,hv,uv⟩:=Finset.one_lt_card.mp large
      let edges:=(S×ˢS).filter (fun z : V×V=>z.1≠z.2)
      have inhabited : edges.Nonempty := ⟨(u,v),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hu,hv⟩,uv⟩⟩
      obtain ⟨z,hz,small⟩:=Finset.exists_min_image edges (fun t=>dist t.1 t.2) inhabited
      obtain ⟨p,q⟩:=z
      obtain ⟨hpq,ne⟩:=Finset.mem_filter.mp hz
      obtain ⟨hp,hq⟩:=Finset.mem_product.mp hpq
      have least (a) (ha : a∈S) (b) (hb : b∈S) (ne : a≠b) : dist p q≤dist a b :=
        small (a,b) (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha,hb⟩,ne⟩)
      have step (a b : V) (ha : a∈S) (hb : b∈S) (ab : a≠b) (light : w a≤w b)
          (near : ∀ i∈S,∀ j∈S,i≠j → dist a b≤dist i j) : (∑ i∈S,2^w i)≤2^n := by
        let T:=S.erase a
        have sub : T⊆S := Finset.erase_subset _ _
        have bt : b∈T := Finset.mem_erase.mpr ⟨ab.symm,hb⟩
        let W (i : V):=if i=b then w i+1 else w i
        have r (i) (hi : i∈T) : W i+(colors T c i).card≤n := by
          by_cases eq : i=b
          · subst i
            have drop:=closest_drops short ha hb ab near
            simp only [W,ite_true]
            change (colors T c b).card+1≤_ at drop
            have old:=room b hb
            omega
          · have le:=Finset.card_le_card (color_mono sub c i)
            have orig:=room i (sub hi)
            simp [W,eq]
            omega
        have induct := ih T (Finset.erase_ssubset ha) (fun i hi x hx y hy=>
          short i (sub hi) x (sub hx) y (sub hy)) W r
        have update (i) : (2:ℕ)^W i=2^w i+(if i=b then 2^w b else 0) := by
          by_cases e : i=b
          · subst i;simp [W,pow_succ];omega
          · simp [W,e]
        simp_rw [update] at induct
        simp [Finset.sum_add_distrib,bt] at induct
        have split := Finset.sum_erase_add S (fun i=>(2:ℕ)^w i) ha
        change (∑ i∈T,2^w i)+2^w a=_ at split
        have cmp : (2:ℕ)^w a≤2^w b := Nat.pow_le_pow_right (by decide) light
        omega
      by_cases order : w p≤w q
      · exact step p q hp hq ne order least
      · apply step q p hq hp ne.symm (by omega)
        simpa only [dist_comm q p] using least
    · rcases S.eq_empty_or_nonempty with rfl|non
      · simp
      · obtain ⟨i,hi⟩:=non
        have eq : S={i} := Finset.eq_singleton_iff_unique_mem.mpr ⟨hi,fun j hj=>
          (Finset.card_le_one.mp (by omega) j hj i hi)⟩
        rw [eq,Finset.sum_singleton]
        have le:=room i hi
        exact Nat.pow_le_pow_right (by decide) (by omega)

end R58.Knockout
#print axioms R58.Knockout.capacity
