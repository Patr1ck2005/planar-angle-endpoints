import PhysicalFiveBearings
noncomputable section
namespace R67.Board
open Real JSP404 R55.WeightedCollision R54.GapTest R56.Windows
def ends : Fin 10 → Fin 5 × Fin 5 :=
  ![(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]
theorem endpoints : ∀ e,(ends e).1<(ends e).2 := by decide
def incident (i : Fin 5) (e : Fin 10) : Prop := i=(ends e).1 ∨ i=(ends e).2
instance (i : Fin 5) (e : Fin 10) : Decidable (incident i e) := inferInstanceAs (Decidable (_ ∨ _))
theorem four_incidents : ∀i : Fin 5,(Finset.univ.filter (incident i)).card=4 := by decide

def bearing {c : Fin 5→Point} (C : Chart c) (e : Fin 10) := C.u (ends e).1 (ends e).2
theorem bearing_bounds {c : Fin 5→Point} (C : Chart c) (e : Fin 10) : 0≤bearing C e ∧ bearing C e<π :=
  C.bounded _ _ (endpoints e)
theorem incident_witness {c : Fin 5→Point} (C : Chart c) (e : Fin 10) (i : Fin 5) (inc : incident i e) :
    ∃j,i≠j ∧ Bearing (c j-c i) (bearing C e) := by
  obtain ⟨r,pos,eq⟩:=C.represents _ _ (endpoints e)
  rcases inc with rfl|rfl
  · exact ⟨_,(endpoints e).ne,r,pos,1,Or.inr rfl,by simpa [bearing] using eq⟩
  · refine ⟨_,(endpoints e).ne.symm,r,pos,-1,Or.inl rfl,?_⟩
    rw [←neg_sub (c (ends e).2) (c (ends e).1),eq];simp [bearing]

theorem sort_scalar {n : ℕ} (x : Fin n→ℝ) : ∃e : Equiv.Perm (Fin n),Monotone (x ∘ e) := by
  let p (i : Fin n) : Point := !₂[(i.val:ℝ),x i]
  have inj : Function.Injective p := by
    intro i j eq;have v:=congrArg (fun p : Point=>p 0) eq
    change (i.val:ℝ)=j.val at v
    exact Fin.ext (by exact_mod_cast v)
  obtain ⟨e,h⟩:=order_points p inj
  refine ⟨e,fun i j le=>?_⟩
  rcases lt_or_eq_of_le le with lt|rfl
  · rcases h i j lt with a|⟨a,_⟩
    · exact a.le
    · exact a.le
  · rfl

def slotSet (order : Equiv.Perm (Fin 10)) (i : Fin 5) :=
  (Finset.univ.filter (incident i)).map order.symm.toEmbedding
def slots (order : Equiv.Perm (Fin 10)) (i : Fin 5) : Fin 4 ↪o Fin 10 :=
  (slotSet order i).orderEmbOfFin (by simp [slotSet,four_incidents])
theorem slot_inc (o : Equiv.Perm (Fin 10)) (i : Fin 5) (j : Fin 4) : incident i (o (slots o i j)) := by
  have h : slots o i j∈slotSet o i := Finset.orderEmbOfFin_mem _ _ _
  obtain ⟨e,he,eq⟩:=Finset.mem_map.mp h
  change o.symm e=slots o i j at eq
  rw [←eq,Equiv.apply_symm_apply]
  exact (Finset.mem_filter.mp he).2

def wall (a : Fin 4→ℝ) (j : ℕ) := if h:j<4 then a ⟨j,h⟩ else a 0+π
def row (a : Fin 4→ℝ) (asc : Monotone a) (bd : ∀j,0≤a j ∧ a j<π) : Row 4 where
  w:=wall a
  ordered:=by
    intro j k jk _
    by_cases h : k<4
    · have jh : j<4:=lt_of_le_of_lt jk h
      simp only [wall,dite_eq_left h,dite_eq_left jh]
      exact asc (show (⟨j,jh⟩ : Fin 4)≤⟨k,h⟩ from jk)
    · by_cases jh : j<4
      · simp only [wall,dite_eq_right h,dite_eq_left jh]
        linarith [(bd ⟨j,jh⟩).2,(bd 0).1]
      · simp [wall,h,jh]
  period:=by simp [wall]

/-- Local digit capacity expressed in the four incident positions of a common
permutation of all ten edges. The final arc wraps once. -/
def slotCost (o : Equiv.Perm (Fin 10)) (x : Fin 10→ℝ) (T : ℝ) (i : Fin 5) : ℕ :=
  ∑ j : Fin 4, (⌊(if h:j.val+1<4 then x (slots o i ⟨j.val+1,h⟩)
    else x (slots o i 0)+T)-x (slots o i j)⌋₊-1)

theorem physical_row_budget {c : Fin 5→Point} (C : Chart c) (o : Equiv.Perm (Fin 10))
    (asc : Monotone (bearing C ∘ o)) {w : Fin 5→ℕ} {θ : ℝ}
    (hit : Admissible w c θ) (lt : θ<π) (i : Fin 5) :
    Nat.clog 2 (w i)≤slotCost o (fun t=>bearing C (o t)/(π-θ)) (π/(π-θ)) i := by
  let a (i : Fin 5) (j : Fin 4):=bearing C (o (slots o i j))
  let R (i : Fin 5):=row (a i) (asc.comp (slots o i).monotone) (fun j=>bearing_bounds C _)
  have wit : Witnessed R c := by
    intro v j _
    by_cases h : j<4
    · simpa only [R,row,wall,dite_eq_left h,a] using incident_witness C _ v (slot_inc o v ⟨j,h⟩)
    · obtain ⟨k,ne,b⟩:=incident_witness C _ v (slot_inc o v 0)
      refine ⟨k,ne,?_⟩;simpa only [R,row,wall,dite_eq_right h,a] using bearing_closes b
  have legal : Admissible w c (π-(π-θ)) := by simpa using hit
  have hi:=admissible_bound R (sub_pos.mpr lt) wit legal i
  change Nat.clog 2 (w i)≤∑ j : Fin 4,(⌊(wall (a i) (j.val+1)-wall (a i) j.val)/(π-θ)⌋₊-1) at hi
  convert hi using 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : j.val+1<4 <;> simp [wall,h,j.isLt,a,sub_div,add_div]
#print axioms sort_scalar
#print axioms slot_inc
#print axioms physical_row_budget
end R67.Board
