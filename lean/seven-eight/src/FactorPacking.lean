import ChordBins
import Mathlib.Data.Nat.Log

noncomputable section
namespace R49.FactorPacking
open Real
abbrev Apart (l a b : ℝ) := l≤|a-b| ∧ |a-b|≤π-l

def lifted (t a : ℝ) : ℝ := if a<t then a+π else a
def signAt (t a : ℝ) (b : Bool) := if a<t then !b else b

theorem greedy {α : Type*} [DecidableEq α] (D : Finset α) (f : α → ℝ) {l : ℝ} (pos : 0<l) :
    ∃ P : Finset α, P⊆D ∧ (∀ x∈D, ∃ a∈P, f a≤f x ∧ f x<f a+l) ∧
    ∀ a∈P, ∀ b∈P, a≠b → l≤|f a-f b| := by
  classical
  induction D using Finset.strongInductionOn with
  | _ D ih =>
    rcases D.eq_empty_or_nonempty with rfl|ne
    · exact ⟨∅,by simp,by simp,by simp⟩
    obtain ⟨a,ha,lo⟩ := D.exists_min_image f ne
    let E := D.filter (fun b => f a+l≤f b)
    have sub : E⊆D := Finset.filter_subset _ _
    have miss : a∉E := by simp [E,not_le.mpr (by linarith : f a<f a+l)]
    have ss : E⊂D := Finset.ssubset_iff_subset_ne.mpr ⟨sub,fun eq => miss (eq ▸ ha)⟩
    obtain ⟨Q,sq,cq,pq⟩ := ih E ss
    refine ⟨insert a Q,Finset.insert_subset ha (sq.trans sub),?_,?_⟩
    · intro b hb
      by_cases right : f a+l≤f b
      · obtain ⟨q,hq,x,y⟩ := cq b (Finset.mem_filter.mpr ⟨hb,right⟩)
        exact ⟨q,Finset.mem_insert_of_mem hq,x,y⟩
      · exact ⟨a,Finset.mem_insert_self _ _,lo b hb,lt_of_not_ge right⟩
    · intro b hb c hc diff
      rcases Finset.mem_insert.mp hb with eqb|hb'
      · subst b
        have hc' : c∈Q := (Finset.mem_insert.mp hc).resolve_left (Ne.symm diff)
        have x := (Finset.mem_filter.mp (sq hc')).2
        rw [abs_of_nonpos (by linarith : f a-f c≤0)];linarith
      · rcases Finset.mem_insert.mp hc with eqc|hc'
        · subst c
          have x := (Finset.mem_filter.mp (sq hb')).2
          rw [abs_of_nonneg (by linarith : 0≤f b-f a)];linarith
        · exact pq b hb' c hc' diff

private theorem span (D : Finset ℝ) {l : ℝ} (lp : 0<l) (ne : D.Nonempty) (lo hi : ℝ)
    (bounds : ∀ x∈D, lo≤x ∧ x≤hi)
    (sep : ∀ a∈D, ∀ b∈D, a≠b → l≤|a-b|) : (D.card:ℝ)*l≤hi-lo+l := by
  classical
  induction D using Finset.strongInductionOn generalizing lo with
  | _ D ih =>
    let a := D.min' ne
    have ha : a∈D := D.min'_mem _
    have drop := Finset.erase_ssubset ha
    have size := Finset.card_erase_add_one ha
    have eq : ((D.erase a).card:ℝ)+1=D.card := by exact_mod_cast size
    rcases (D.erase a).eq_empty_or_nonempty with empty|non
    · rw [empty] at eq; simp only [Finset.card_empty,Nat.cast_zero,zero_add] at eq
      nlinarith [(bounds a ha).1,(bounds a ha).2]
    · have next := ih (D.erase a) drop non (a+l) (fun x hx => by
        have mem := (Finset.mem_erase.mp hx).2
        have apart := sep x mem a ha (Finset.mem_erase.mp hx).1
        rw [abs_of_nonneg (sub_nonneg.mpr (D.min'_le _ mem))] at apart
        exact ⟨by linarith,(bounds x mem).2⟩)
        (fun x hx y hy h => sep x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy) h)
      nlinarith [(bounds a ha).1]

theorem circle (D : Finset ℝ) {l : ℝ} (lp : 0<l) (lim : l≤π)
    (sep : ∀ a∈D, ∀ b∈D, a≠b → Apart l a b) : (D.card:ℝ)*l≤π := by
  classical
  rcases D.eq_empty_or_nonempty with rfl|ne
  · simp [pi_pos.le]
  let a := D.min' ne
  let b := D.max' ne
  have ha : a∈D := D.min'_mem _
  have hb : b∈D := D.max'_mem _
  have h := span D lp ne a b (fun x hx => ⟨D.min'_le _ hx,D.le_max' _ hx⟩)
    (fun x hx y hy diff => (sep x hx y hy diff).1)
  by_cases eq : a=b
  · linarith
  · have up := (sep b hb a ha (Ne.symm eq)).2
    linarith [le_abs_self (b-a)]

theorem safe_lift {l t a : ℝ} (h : Apart l t a) :
    t+l≤lifted t a ∧ lifted t a≤t+π-l := by
  unfold lifted
  unfold Apart at h
  split_ifs with e
  · rw [abs_of_nonneg (by linarith : 0≤t-a)] at h;constructor <;> linarith [h.1,h.2]
  · rw [abs_of_nonpos (by linarith : t-a≤0)] at h;constructor <;> linarith [h.1,h.2]

theorem lift_diff {t a b : ℝ} (range : |a-b|≤π) :
    |lifted t a-lifted t b| = if (a<t ↔ b<t) then |a-b| else π-|a-b| := by
  by_cases x : a<t <;> by_cases y : b<t <;> simp [lifted,x,y] <;>
    first | (rw [abs_of_nonneg (by linarith [(abs_le.mp range).1] : 0≤a+π-b),
      abs_of_nonpos (by linarith : a-b≤0)];ring)
          | (rw [abs_of_nonpos (by linarith [(abs_le.mp range).2] : a-(b+π)≤0),
      abs_of_nonneg (by linarith : 0≤a-b)];ring)

theorem unlift {l t a b : ℝ} (range : |a-b|≤π) (sl : Apart l t a) (sr : Apart l t b) (lp : 0<l)
    (sep : l≤|lifted t a-lifted t b|) : Apart l a b := by
  obtain ⟨la,ua⟩ := safe_lift sl
  obtain ⟨lb,ub⟩ := safe_lift sr
  have up : |lifted t a-lifted t b|≤π-l := abs_le.mpr ⟨by linarith,by linarith⟩
  rw [lift_diff range] at sep up
  split_ifs at sep up <;> exact ⟨by linarith,by linarith⟩

end R49.FactorPacking
