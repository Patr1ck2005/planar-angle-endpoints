import OrderMaskCore
namespace R67.OrderOrbit
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000
def sub45120 : Cert := (.node [(3,(.node [(6,(.node [(7,(.node [(8,(.node [(9,(.leaf ⟨5,19,5,true⟩))]))])),(9,(.node [(8,(.node [(7,(.leaf ⟨6,19,5,true⟩))]))]))])),(7,(.node [(6,(.node [(8,(.node [(9,(.leaf ⟨3,8,8,false⟩))]))]))]))])),(7,(.node [(3,(.node [(6,(.node [(8,(.node [(9,(.leaf ⟨3,119,9,true⟩))]))]))]))]))])
theorem ok45120 : checkedLeaves maskTest 5 sub45120=true := by decide +kernel
def sub4512630 : Cert := (.node [(7,(.node [(8,(.node [(9,(.leaf ⟨15,5,6,true⟩))]))])),(9,(.node [(8,(.node [(7,(.leaf ⟨14,71,2,false⟩))]))]))])
theorem ok4512630 : checkedLeaves maskTest 3 sub4512630=true := by decide +kernel
def sub4512637 : Cert := (.node [(0,(.node [(8,(.node [(9,(.leaf ⟨17,8,8,false⟩))]))])),(8,(.node [(0,(.node [(9,(.leaf ⟨16,103,6,false⟩))])),(9,(.node [(0,(.leaf ⟨11,24,1,false⟩))]))]))])
theorem ok4512637 : checkedLeaves maskTest 3 sub4512637=true := by decide +kernel
def sub4512639 : Cert := (.node [(0,(.node [(8,(.node [(7,(.leaf ⟨10,103,6,false⟩))]))])),(8,(.node [(0,(.node [(7,(.leaf ⟨2,103,6,false⟩))])),(7,(.node [(0,(.leaf ⟨4,112,7,true⟩))]))]))])
theorem ok4512639 : checkedLeaves maskTest 3 sub4512639=true := by decide +kernel
def sub451267 : Cert := (.node [(3,(.node [(0,(.node [(8,(.node [(9,(.leaf ⟨17,119,9,true⟩))]))])),(8,(.node [(0,(.node [(9,(.leaf ⟨19,8,8,false⟩))])),(9,(.node [(0,(.leaf ⟨9,118,8,true⟩))]))]))]))])
theorem ok451267 : checkedLeaves maskTest 4 sub451267=true := by decide +kernel
def sub45127 : Cert := (.node [(0,(.node [(3,(.node [(6,(.node [(8,(.node [(9,(.leaf ⟨5,96,4,false⟩))]))]))]))])),(6,(.node [(3,(.node [(0,(.node [(8,(.node [(9,(.leaf ⟨15,102,5,false⟩))]))])),(8,(.node [(0,(.node [(9,(.leaf ⟨7,102,5,false⟩))])),(9,(.node [(0,(.leaf ⟨0,102,5,false⟩))]))]))]))]))])
theorem ok45127 : checkedLeaves maskTest 5 sub45127=true := by decide +kernel
def sub4516230 : Cert := (.node [(7,(.node [(8,(.node [(9,(.leaf ⟨7,5,6,true⟩))]))])),(9,(.node [(8,(.node [(7,(.leaf ⟨8,5,6,true⟩))]))]))])
theorem ok4516230 : checkedLeaves maskTest 3 sub4516230=true := by decide +kernel
def sub4516237 : Cert := (.node [(0,(.node [(8,(.node [(9,(.leaf ⟨19,119,9,true⟩))]))])),(8,(.node [(0,(.node [(9,(.leaf ⟨19,64,4,false⟩))])),(9,(.node [(0,(.leaf ⟨7,24,1,false⟩))]))]))])
theorem ok4516237 : checkedLeaves maskTest 3 sub4516237=true := by decide +kernel
def sub4516239 : Cert := (.node [(0,(.node [(8,(.node [(7,(.leaf ⟨13,71,2,false⟩))]))])),(8,(.node [(0,(.node [(7,(.leaf ⟨13,112,7,true⟩))])),(7,(.node [(0,(.leaf ⟨8,24,1,false⟩))]))]))])
theorem ok4516239 : checkedLeaves maskTest 3 sub4516239=true := by decide +kernel
def sub451627 : Cert := (.node [(3,(.node [(0,(.node [(8,(.node [(9,(.leaf ⟨16,4,7,true⟩))]))])),(8,(.node [(0,(.node [(9,(.leaf ⟨19,85,5,true⟩))])),(9,(.node [(0,(.leaf ⟨9,24,1,false⟩))]))]))]))])
theorem ok451627 : checkedLeaves maskTest 4 sub451627=true := by decide +kernel
def sub45169 : Cert := (.node [(3,(.node [(2,(.node [(0,(.node [(8,(.node [(7,(.leaf ⟨12,71,2,false⟩))]))])),(8,(.node [(0,(.node [(7,(.leaf ⟨13,106,7,false⟩))])),(7,(.node [(0,(.leaf ⟨10,24,1,false⟩))]))]))])),(8,(.node [(2,(.node [(0,(.node [(7,(.leaf ⟨2,109,6,true⟩))])),(7,(.node [(0,(.leaf ⟨3,109,6,true⟩))]))]))]))]))])
theorem ok45169 : checkedLeaves maskTest 5 sub45169=true := by decide +kernel
end R67.OrderOrbit
