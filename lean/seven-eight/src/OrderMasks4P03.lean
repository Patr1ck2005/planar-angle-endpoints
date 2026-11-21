import OrderMaskCore
namespace R67.OrderOrbit
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000
def sub4561230 : Cert := (.node [(7,(.node [(8,(.node [(9,(.leaf ⟨0,5,6,true⟩))]))])),(9,(.node [(8,(.node [(7,(.leaf ⟨1,5,6,true⟩))]))]))])
theorem ok4561230 : checkedLeaves maskTest 3 sub4561230=true := by decide +kernel
def sub4561237 : Cert := (.node [(0,(.node [(8,(.node [(9,(.leaf ⟨9,9,7,false⟩))]))])),(8,(.node [(0,(.node [(9,(.leaf ⟨9,47,2,true⟩))])),(9,(.node [(0,(.leaf ⟨0,24,1,false⟩))]))]))])
theorem ok4561237 : checkedLeaves maskTest 3 sub4561237=true := by decide +kernel
def sub4561239 : Cert := (.node [(0,(.node [(8,(.node [(7,(.leaf ⟨12,9,7,false⟩))]))])),(8,(.node [(0,(.node [(7,(.leaf ⟨12,47,2,true⟩))])),(7,(.node [(0,(.leaf ⟨1,24,1,false⟩))]))]))])
theorem ok4561239 : checkedLeaves maskTest 3 sub4561239=true := by decide +kernel
def sub456127 : Cert := (.node [(3,(.node [(0,(.node [(8,(.node [(9,(.leaf ⟨11,47,2,true⟩))]))])),(8,(.node [(0,(.node [(9,(.leaf ⟨7,47,2,true⟩))])),(9,(.node [(0,(.leaf ⟨0,47,2,true⟩))]))]))]))])
theorem ok456127 : checkedLeaves maskTest 4 sub456127=true := by decide +kernel
def sub45619 : Cert := (.node [(3,(.node [(2,(.node [(0,(.node [(8,(.node [(7,(.leaf ⟨12,3,7,true⟩))]))])),(8,(.node [(0,(.node [(7,(.leaf ⟨13,47,2,true⟩))])),(7,(.node [(0,(.leaf ⟨2,24,1,false⟩))]))]))])),(8,(.node [(2,(.node [(0,(.node [(7,(.leaf ⟨10,109,6,true⟩))])),(7,(.node [(0,(.leaf ⟨3,24,1,false⟩))]))]))]))]))])
theorem ok45619 : checkedLeaves maskTest 5 sub45619=true := by decide +kernel
def sub45672 : Cert := (.node [(1,(.node [(3,(.node [(0,(.node [(8,(.node [(9,(.leaf ⟨4,15,6,false⟩))]))])),(8,(.node [(0,(.node [(9,(.leaf ⟨8,47,2,true⟩))])),(9,(.node [(0,(.leaf ⟨1,47,2,true⟩))]))]))]))])),(8,(.node [(3,(.node [(1,(.node [(0,(.node [(9,(.leaf ⟨10,47,2,true⟩))])),(9,(.node [(0,(.leaf ⟨2,47,2,true⟩))]))])),(9,(.node [(1,(.node [(0,(.leaf ⟨4,24,1,false⟩))]))]))]))]))])
theorem ok45672 : checkedLeaves maskTest 5 sub45672=true := by decide +kernel
def sub45678 : Cert := (.node [(2,(.node [(3,(.node [(1,(.node [(0,(.node [(9,(.leaf ⟨3,17,5,false⟩))])),(9,(.node [(0,(.leaf ⟨3,47,2,true⟩))]))])),(9,(.node [(1,(.node [(0,(.leaf ⟨5,24,1,false⟩))]))]))]))])),(9,(.node [(3,(.node [(2,(.node [(1,(.node [(0,(.leaf ⟨6,24,1,false⟩))]))]))]))]))])
theorem ok45678 : checkedLeaves maskTest 5 sub45678=true := by decide +kernel
def sub45691 : Cert := (.node [(3,(.node [(2,(.node [(0,(.node [(8,(.node [(7,(.leaf ⟨1,11,6,false⟩))]))])),(8,(.node [(0,(.node [(7,(.leaf ⟨8,11,6,false⟩))])),(7,(.node [(0,(.leaf ⟨4,47,2,true⟩))]))]))])),(8,(.node [(2,(.node [(0,(.node [(7,(.leaf ⟨14,47,2,true⟩))])),(7,(.node [(0,(.leaf ⟨5,47,2,true⟩))]))]))]))]))])
theorem ok45691 : checkedLeaves maskTest 5 sub45691=true := by decide +kernel
def sub45698 : Cert := (.node [(3,(.node [(1,(.node [(2,(.node [(0,(.node [(7,(.leaf ⟨6,21,5,false⟩))])),(7,(.node [(0,(.leaf ⟨6,47,2,true⟩))]))]))])),(7,(.node [(2,(.node [(1,(.node [(0,(.leaf ⟨6,107,8,false⟩))]))]))]))])),(7,(.node [(3,(.node [(2,(.node [(1,(.node [(0,(.leaf ⟨6,0,9,true⟩))]))]))]))]))])
theorem ok45698 : checkedLeaves maskTest 5 sub45698=true := by decide +kernel
end R67.OrderOrbit
