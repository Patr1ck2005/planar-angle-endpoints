import OrderMaskCore
namespace R67.OrderOrbit
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000
def sub01423 : Cert := (.node [(5,(.node [(6,(.node [(7,(.node [(8,(.node [(9,(.leaf ⟨15,0,0,false⟩))]))])),(9,(.node [(8,(.node [(7,(.leaf ⟨14,113,8,true⟩))]))]))])),(7,(.node [(6,(.node [(8,(.node [(9,(.leaf ⟨11,119,9,true⟩))]))]))]))])),(9,(.node [(6,(.node [(5,(.node [(8,(.node [(7,(.leaf ⟨14,100,6,false⟩))]))])),(8,(.node [(5,(.node [(7,(.leaf ⟨5,100,6,false⟩))]))]))]))]))])
theorem ok01423 : checkedLeaves maskTest 5 sub01423=true := by decide +kernel
def sub01425 : Cert := (.node [(3,(.node [(6,(.node [(7,(.node [(8,(.node [(9,(.leaf ⟨15,119,9,true⟩))]))])),(9,(.node [(8,(.node [(7,(.leaf ⟨5,113,8,true⟩))]))]))])),(7,(.node [(6,(.node [(8,(.node [(9,(.leaf ⟨7,119,9,true⟩))]))]))]))])),(7,(.node [(3,(.node [(6,(.node [(8,(.node [(9,(.leaf ⟨0,119,9,true⟩))]))]))]))]))])
theorem ok01425 : checkedLeaves maskTest 5 sub01425=true := by decide +kernel
def sub0149 : Cert := (.node [(3,(.node [(2,(.node [(6,(.node [(5,(.node [(8,(.node [(7,(.leaf ⟨15,54,2,true⟩))]))])),(8,(.node [(5,(.node [(7,(.leaf ⟨15,114,7,false⟩))]))]))]))])),(6,(.node [(2,(.node [(5,(.node [(8,(.node [(7,(.leaf ⟨11,114,7,false⟩))]))])),(8,(.node [(5,(.node [(7,(.leaf ⟨7,114,7,false⟩))]))]))])),(8,(.node [(2,(.node [(5,(.node [(7,(.leaf ⟨0,114,7,false⟩))]))]))]))]))]))])
theorem ok0149 : checkedLeaves maskTest 6 sub0149=true := by decide +kernel
def sub01932 : Cert := (.node [(4,(.node [(6,(.node [(5,(.node [(8,(.node [(7,(.leaf ⟨11,35,5,false⟩))]))])),(8,(.node [(5,(.node [(7,(.leaf ⟨15,17,4,true⟩))]))]))]))])),(8,(.node [(6,(.node [(4,(.node [(5,(.node [(7,(.leaf ⟨14,45,4,false⟩))]))])),(7,(.node [(5,(.node [(4,(.leaf ⟨14,24,0,true⟩))]))]))])),(7,(.node [(6,(.node [(5,(.node [(4,(.leaf ⟨5,24,0,true⟩))]))]))]))]))])
theorem ok01932 : checkedLeaves maskTest 5 sub01932=true := by decide +kernel
def sub01934 : Cert := (.node [(2,(.node [(6,(.node [(5,(.node [(8,(.node [(7,(.leaf ⟨16,0,0,false⟩))]))])),(8,(.node [(5,(.node [(7,(.leaf ⟨17,0,0,false⟩))]))]))]))])),(6,(.node [(2,(.node [(5,(.node [(8,(.node [(7,(.leaf ⟨18,0,0,false⟩))]))])),(8,(.node [(5,(.node [(7,(.leaf ⟨16,115,8,false⟩))]))]))])),(8,(.node [(2,(.node [(5,(.node [(7,(.leaf ⟨11,72,3,false⟩))]))]))]))]))])
theorem ok01934 : checkedLeaves maskTest 5 sub01934=true := by decide +kernel
def sub01938 : Cert := (.node [(2,(.node [(6,(.node [(4,(.node [(5,(.node [(7,(.leaf ⟨10,115,8,false⟩))]))])),(7,(.node [(5,(.node [(4,(.leaf ⟨8,115,8,false⟩))]))]))])),(7,(.node [(6,(.node [(5,(.node [(4,(.leaf ⟨4,24,0,true⟩))]))]))]))])),(6,(.node [(2,(.node [(4,(.node [(5,(.node [(7,(.leaf ⟨2,115,8,false⟩))]))])),(7,(.node [(5,(.node [(4,(.leaf ⟨1,115,8,false⟩))]))]))])),(4,(.node [(2,(.node [(5,(.node [(7,(.leaf ⟨4,104,5,true⟩))]))]))]))]))])
theorem ok01938 : checkedLeaves maskTest 5 sub01938=true := by decide +kernel
def sub0194 : Cert := (.node [(3,(.node [(2,(.node [(6,(.node [(5,(.node [(8,(.node [(7,(.leaf ⟨17,71,2,false⟩))]))])),(8,(.node [(5,(.node [(7,(.leaf ⟨17,111,7,true⟩))]))]))]))])),(6,(.node [(2,(.node [(5,(.node [(8,(.node [(7,(.leaf ⟨16,71,2,false⟩))]))])),(8,(.node [(5,(.node [(7,(.leaf ⟨19,0,0,false⟩))]))]))])),(8,(.node [(2,(.node [(5,(.node [(7,(.leaf ⟨9,110,6,true⟩))]))]))]))]))]))])
theorem ok0194 : checkedLeaves maskTest 6 sub0194=true := by decide +kernel
end R67.OrderOrbit
