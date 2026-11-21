import PackedFarkas
namespace R67.Five
open R67.Farkas R67.Packed

abbrev Word := List ℕ
abbrev Arc := List ℕ

def ends : List (ℕ×ℕ) := [(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]
def triples : List (List ℕ) :=
  [[0,1,4],[0,2,5],[0,3,6],[1,2,7],[1,3,8],[2,3,9],[4,5,7],[4,6,8],[5,6,9],[7,8,9]]

def incident (w : Word) (v j : ℕ) : Bool :=
  let e:=ends.getD (w.getD j 10) (5,5)
  v==e.1 || v==e.2

def arc (positions : List ℕ) (a : ℕ) : Arc :=
  let s:=positions.getD a 0
  let t:=positions.getD ((a+1)%positions.length) 0
  (List.range ((t+10-s)%10)).map (fun i=>(s+i)%10)

def rowArc (w : Word) (v a : ℕ) : Arc :=
  arc ((List.range 10).filter (incident w v)) a

def complement (ar : Arc) : Arc := (List.range 10).filter (fun i=>!ar.contains i)

def triComplements (w : Word) : List Arc := triples.flatMap (fun tri=>
  let positions:=(List.range 10).filter (fun i=>tri.contains (w.getD i 10))
  (List.range 3).map (fun a=>complement (arc positions a)))

def marked (u : ℕ) := (List.range 5).filter (·!=u)
def vertex (u j : ℕ) := (marked u).getD (j/4) 5
def ar (w : Word) (u j : ℕ) := rowArc w (vertex u j) (j%4)
def weight (v h : ℕ) : ℕ := if v=h then 1 else 0
def goal (h : ℕ) : ℕ := if h=5 then 5 else 6
def terms (a : Arc) (z : ℤ) := a.map (fun j=>(j,z))
def triRule (a : Arc) : Lin := aff (-1) (terms a 1)
def capRule (j : ℕ) : Lin := aff 2 [(j,-1)]
def kRule : Lin := aff 30 [(26,-1)]
def arcRule (j : ℕ) (a : Arc) : Lin :=
  let Q : ℤ := 2*(a.length:ℤ)-1
  aff 0 ((10+j,-(Q+1))::terms a Q)
def positive (j : ℕ) (a : Arc) : Lin := aff (-1) ((10+j,-1)::terms a 1)
def rowRule (z : ℤ) (b h v : ℕ) : Lin :=
  aff (z*(weight v h:ℤ)) ((26,z)::terms ((List.range 4).map (fun a=>10+4*b+a)) (-z))
def target (h : ℕ) : Lin := aff (-(goal h:ℤ)) ((26,-2)::terms (List.range 10) 2)
def basis : List Lin := (List.range 28).map (fun i=>unitAt i 1)

def model (w : Word) (u h : ℕ) : Data where
  base := (triComplements w).map triRule ++ (List.range 10).map capRule ++ [kRule] ++
    (List.range 16).map (fun j=>arcRule j (ar w u j)) ++
    (List.range 4).flatMap (fun b=>[rowRule 1 b h ((marked u).getD b 5),
      rowRule (-1) b h ((marked u).getD b 5)]) ++ basis
  target := target h
  active := fun j=>positive j (ar w u j)

def certify (w : Word) (u h : ℕ) (c : Cert) : Bool :=
  let d:=model w u h
  (d.base.all (fun a=>decide (norm a≤256))) &&
  decide (norm d.target≤256) && (List.range 16).all (fun j=>decide (norm (d.active j)≤256)) &&
  quick (pack d.target) (pack ∘ d.active) (d.base.map pack) c

def Proved (w : Word) (u h : ℕ) : Prop := ∃ c, certify w u h c=true

theorem run {w : Word} {u h : ℕ} (cert : Proved w u h) {x : ℕ→ℝ} (hx : ∀ k,0≤x k) (x0 : x 0=1)
    (integ : ∀j,j≤16 → ∃ n : ℕ,x ((10+j)+1)=n)
    (on : ∀ j,j<16 → 0<x ((10+j)+1) → 0≤val x ((model w u h).active j))
    (base : Good x (model w u h).base) : 0≤val x (target h) := by
  obtain ⟨c,hc⟩:=cert
  simp only [certify,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq,List.mem_range] at hc
  exact Packed.sound _ hx x0 integ on hc.1.1.2 hc.1.2 _ base hc.1.1.1 c hc.2

end R67.Five
#print axioms R67.Five.run
