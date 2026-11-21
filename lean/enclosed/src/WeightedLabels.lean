import SendovInner
import Mathlib.Data.Nat.Log

noncomputable section
namespace R55.WeightedCollision
open Filter Topology Real JSP404

variable {I : Type*} [Fintype I]
abbrev Label (w : I→ℕ) := (i : I) × Fin (w i)
abbrev dim (w : I→ℕ) (i : I) := Nat.clog 2 (w i)
def representative {w : I→ℕ} (hw : ∀ i, 0<w i) (i : I) : Label w := ⟨i,⟨0,hw i⟩⟩
def points {w : I→ℕ} (f : Label w→Point) : Finset Point := Finset.univ.image f

/-- The score spectrum for the prescribed finite weights and fixed distinct centers. -/
def attainable (w : I→ℕ) (c : I→Point) : Set ℝ :=
  {θ | ∀ ε : ℝ, 0<ε → ∃ f : Label w→Point, Function.Injective f ∧
    (∀ a, dist (f a) (c a.1)<ε) ∧ maxAngle (points f)<θ+ε}

theorem inject_words {n d : ℕ} (hn : 0<n) (size : n≤2^d) :
    ∃ e : Fin n ↪ BinaryWord d, e ⟨0,hn⟩ = (fun _=>false) := by
  classical
  obtain ⟨g⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card (Fin n)≤Fintype.card (BinaryWord d) by simpa [BinaryWord] using size)
  let flip := Equiv.swap (g ⟨0,hn⟩) (fun _=>false)
  exact ⟨g.trans flip.toEmbedding,Equiv.swap_apply_left _ _⟩

/-- Label both the entire fiber and its distinguished center before realization. -/
theorem insert_labels (w h : I→ℕ) (hw : ∀ i, 0<w i) (fits : ∀ i, w i≤2^(h i)) :
    ∃ E : Label w→ClusterWord h, Function.Injective E ∧ (∀ a, (E a).1=a.1) ∧
      (∀ i, E (representative hw i)=⟨i,fun _=>false⟩) := by
  classical
  choose e hz using fun i=>inject_words (hw i) (fits i)
  let E : Label w→ClusterWord h := fun a=>⟨a.1,e a.1 a.2⟩
  refine ⟨E,?_,fun _=>rfl,fun i=>?_⟩
  · rintro ⟨i,x⟩ ⟨j,y⟩ he
    obtain rfl : i=j := congrArg Sigma.fst he
    exact congrArg (Sigma.mk i) ((e i).injective (Sigma.mk.inj_iff.mp he).2.eq)
  · exact congrArg (Sigma.mk i) (hz i)

theorem card {w : I→ℕ} {f : Label w→Point} (hf : Function.Injective f) :
    (points f).card=∑ i,w i := by
  rw [points,Finset.card_image_of_injective _ hf,Finset.card_univ]
  simp [Label,Fintype.card_sigma]

theorem fiber_card {w : I→ℕ} {f : Label w→Point} (hf : Function.Injective f) (i : I) :
    (Finset.univ.image (fun x : Fin (w i)=>f ⟨i,x⟩)).card=w i := by
  have hi : Function.Injective (fun x : Fin (w i)=>f ⟨i,x⟩) := by
    intro x y e
    exact (Sigma.mk.inj_iff.mp (hf e)).2.eq
  simp [Finset.card_image_of_injective _ hi]

#print axioms insert_labels
#print axioms fiber_card
end R55.WeightedCollision
