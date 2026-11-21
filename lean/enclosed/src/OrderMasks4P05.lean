import OrderMaskCore
namespace R67.OrderOrbit
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000
def sub49165 : Cert := (.node [(3,(.node [(2,(.node [(0,(.node [(8,(.node [(7,(.leaf ⟨9,71,2,false⟩))]))])),(8,(.node [(0,(.node [(7,(.leaf ⟨19,40,4,true⟩))])),(7,(.node [(0,(.leaf ⟨17,70,3,false⟩))]))]))])),(8,(.node [(2,(.node [(0,(.node [(7,(.leaf ⟨16,109,6,true⟩))])),(7,(.node [(0,(.leaf ⟨17,109,6,true⟩))]))]))]))]))])
theorem ok49165 : checkedLeaves maskTest 5 sub49165=true := by decide +kernel
def sub496130 : Cert := (.node [(2,(.node [(5,(.node [(8,(.node [(7,(.leaf ⟨4,13,6,true⟩))]))])),(8,(.node [(5,(.node [(7,(.leaf ⟨2,10,7,false⟩))]))]))])),(8,(.node [(2,(.node [(5,(.node [(7,(.leaf ⟨10,10,7,false⟩))]))]))]))])
theorem ok496130 : checkedLeaves maskTest 4 sub496130=true := by decide +kernel
def sub496135 : Cert := (.node [(2,(.node [(0,(.node [(8,(.node [(7,(.leaf ⟨11,71,2,false⟩))]))])),(8,(.node [(0,(.node [(7,(.leaf ⟨16,10,7,false⟩))])),(7,(.node [(0,(.leaf ⟨18,10,7,false⟩))]))]))])),(8,(.node [(2,(.node [(0,(.node [(7,(.leaf ⟨17,117,9,false⟩))])),(7,(.node [(0,(.leaf ⟨16,117,9,false⟩))]))]))]))])
theorem ok496135 : checkedLeaves maskTest 4 sub496135=true := by decide +kernel
def sub496138 : Cert := (.node [(0,(.node [(2,(.node [(5,(.node [(7,(.leaf ⟨14,72,3,false⟩))]))]))])),(5,(.node [(2,(.node [(0,(.node [(7,(.leaf ⟨15,108,5,true⟩))])),(7,(.node [(0,(.leaf ⟨11,78,4,false⟩))]))]))]))])
theorem ok496138 : checkedLeaves maskTest 4 sub496138=true := by decide +kernel
def sub49615 : Cert := (.node [(3,(.node [(2,(.node [(0,(.node [(8,(.node [(7,(.leaf ⟨9,3,7,true⟩))]))])),(8,(.node [(0,(.node [(7,(.leaf ⟨19,117,9,false⟩))])),(7,(.node [(0,(.leaf ⟨16,24,1,false⟩))]))]))])),(8,(.node [(2,(.node [(0,(.node [(7,(.leaf ⟨17,2,8,true⟩))])),(7,(.node [(0,(.leaf ⟨17,24,1,false⟩))]))]))]))]))])
theorem ok49615 : checkedLeaves maskTest 5 sub49615=true := by decide +kernel
def sub49651 : Cert := (.node [(3,(.node [(2,(.node [(0,(.node [(8,(.node [(7,(.leaf ⟨0,11,6,false⟩))]))])),(8,(.node [(0,(.node [(7,(.leaf ⟨7,11,6,false⟩))])),(7,(.node [(0,(.leaf ⟨11,11,6,false⟩))]))]))])),(8,(.node [(2,(.node [(0,(.node [(7,(.leaf ⟨15,11,6,false⟩))])),(7,(.node [(0,(.leaf ⟨15,41,3,true⟩))]))]))]))]))])
theorem ok49651 : checkedLeaves maskTest 5 sub49651=true := by decide +kernel
def sub49658 : Cert := (.node [(3,(.node [(1,(.node [(2,(.node [(0,(.node [(7,(.leaf ⟨5,21,5,false⟩))])),(7,(.node [(0,(.leaf ⟨14,21,5,false⟩))]))]))])),(7,(.node [(2,(.node [(1,(.node [(0,(.leaf ⟨14,0,9,true⟩))]))]))]))])),(7,(.node [(3,(.node [(2,(.node [(1,(.node [(0,(.leaf ⟨5,0,9,true⟩))]))]))]))]))])
theorem ok49658 : checkedLeaves maskTest 5 sub49658=true := by decide +kernel
def sub49683 : Cert := (.node [(1,(.node [(0,(.node [(2,(.node [(5,(.node [(7,(.leaf ⟨6,98,4,true⟩))]))]))])),(5,(.node [(2,(.node [(0,(.node [(7,(.leaf ⟨5,98,4,true⟩))])),(7,(.node [(0,(.leaf ⟨4,98,4,true⟩))]))]))]))])),(5,(.node [(1,(.node [(2,(.node [(0,(.node [(7,(.leaf ⟨3,117,9,false⟩))])),(7,(.node [(0,(.leaf ⟨2,117,9,false⟩))]))]))])),(7,(.node [(2,(.node [(1,(.node [(0,(.leaf ⟨1,117,9,false⟩))]))]))]))]))])
theorem ok49683 : checkedLeaves maskTest 5 sub49683=true := by decide +kernel
end R67.OrderOrbit
