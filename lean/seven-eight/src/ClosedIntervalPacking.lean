import FiveDyadicDeficit
noncomputable section
namespace R70.EqualPacking
open Finset

def Separated (S : Finset ℝ) (l : ℝ) := ∀ x∈S,∀y∈S,x<y → l≤y-x

/-- At critical density a closed interval realizes one lattice, with both endpoints fixed. -/
theorem lattice (S : Finset ℝ) {k : ℕ} (card : S.card=k+1) {a b l : ℝ}
    (within : ∀x∈S,a≤x ∧ x≤b) (wide : b-a≤k*l) (space : Separated S l) :
    b=a+k*l ∧ S=univ.image (fun i:Fin (k+1)=>a+i.val*l) := by
  classical
  let f:=S.orderEmbOfFin card
  have mem (i:Fin (k+1)) : f i∈S:=S.orderEmbOfFin_mem card i
  let u (i:Fin (k+1)):=f i-i.val*l
  have mon : Monotone u := by
    apply Fin.monotone_iff_le_succ.mpr
    intro j
    have h:=space _ (mem j.castSucc) _ (mem j.succ) (f.strictMono Fin.castSucc_lt_succ)
    dsimp [u]
    push_cast
    linarith
  have lo := (within _ (mem 0)).1
  have hi := (within _ (mem (Fin.last k))).2
  have vals (i:Fin (k+1)) : f i=a+i.val*l := by
    have l0:=mon (Fin.zero_le i)
    have h0:=mon (Fin.le_last i)
    dsimp [u] at l0 h0
    norm_num at l0
    linarith
  constructor
  · have h:=vals (Fin.last k)
    dsimp only [Fin.val_last] at h
    linarith
  · have sub : univ.image (fun i:Fin (k+1)=>a+i.val*l) ⊆ S := by
      rintro _ x;obtain ⟨i,_,rfl⟩:=mem_image.mp x
      rw [←vals];exact mem i
    symm
    apply eq_of_subset_of_card_le sub
    have inj : Function.Injective (fun i:Fin (k+1)=>a+i.val*l) := by
      intro i j eq
      exact f.injective ((vals i).trans (eq.trans (vals j).symm))
    simp [card,card_image_of_injective _ inj]

theorem insert_sep (S : Finset ℝ) {x l : ℝ} (sp:Separated S l) (away:∀z∈S,l≤|z-x|) :
    Separated (insert x S) l := by
  intro p hp q hq pq
  rcases mem_insert.mp hp with rfl|hp <;> rcases mem_insert.mp hq with rfl|hq
  · exact (lt_irrefl _ pq).elim
  · simpa [abs_of_pos (sub_pos.mpr pq)] using away q hq
  · rename_i hpS
    simpa [abs_of_neg (sub_neg.mpr pq)] using away p hpS
  · exact sp p hp q hq pq

private theorem new_point (S:Finset ℝ) {x l:ℝ} (lp:0<l) (away:∀z∈S,l≤|z-x|) : x∉S := by
  intro hx
  have h:=away x hx
  simp at h;linarith

/-- For k axes in width k*l, any remaining bearing separated from all axes is unique. -/
theorem one_opening (S:Finset ℝ) {k:ℕ} (card:S.card=k) {a b l x y:ℝ}
    (lp:0<l) (wide:b-a≤k*l) (sp:Separated S l) (within:∀z∈S,a≤z ∧ z≤b)
    (hx:a≤x ∧ x≤b) (hy:a≤y ∧ y≤b) (ax:∀z∈S,l≤|z-x|) (ay:∀z∈S,l≤|z-y|) : x=y := by
  classical
  have row (v:ℝ) (hv:a≤v ∧ v≤b) (av:∀z∈S,l≤|z-v|) :
      insert v S=univ.image (fun i:Fin (k+1)=>a+i.val*l) := by
    apply (lattice _ (by simp [new_point S lp av,card]) (fun z hz=>?_) wide (insert_sep S sp av)).2
    rcases mem_insert.mp hz with rfl|h
    · exact hv
    · exact within _ h
  have same:insert x S=insert y S:=(row x hx ax).trans (row y hy ay).symm
  have memx:x∈insert y S:=same ▸ mem_insert_self x S
  exact (mem_insert.mp memx).resolve_right (new_point S lp ax)

/-- Positive-width equality needs both endpoints, and one exterior chord cannot supply both. -/
theorem interior_obstruction (S:Finset ℝ) {k:ℕ} (card:S.card=k) (kp:0<k) {a b l x:ℝ}
    (lp:0<l) (wide:b-a≤k*l) (sp:Separated S l) (within:∀z∈S,a<z ∧ z<b)
    (hx:a≤x ∧ x≤b) (ax:∀z∈S,l≤|z-x|) : False := by
  classical
  obtain ⟨endpt,full⟩:=lattice (insert x S) (by simp [new_point S lp ax,card]) (a:=a) (b:=b)
    (fun z hz=>by rcases mem_insert.mp hz with rfl|h;exact hx;exact ⟨(within _ h).1.le,(within _ h).2.le⟩)
    wide (insert_sep S sp ax)
  have first:a∈insert x S:=by rw [full];exact mem_image.mpr ⟨0,mem_univ _,by simp⟩
  have last:b∈insert x S:=by rw [full];exact mem_image.mpr ⟨Fin.last k,mem_univ _,by simpa using endpt.symm⟩
  have fa:a=x:=(mem_insert.mp first).resolve_right (fun h=>(lt_irrefl _ (within _ h).1))
  have fb:b=x:=(mem_insert.mp last).resolve_right (fun h=>(lt_irrefl _ (within _ h).2))
  have pos:0<(k:ℝ)*l:=mul_pos (by exact_mod_cast kp) lp
  linarith
end R70.EqualPacking
#print axioms R70.EqualPacking.lattice
#print axioms R70.EqualPacking.one_opening
#print axioms R70.EqualPacking.interior_obstruction
