import OrderMaskCore
namespace R67.OrderOrbit
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000
def sub90837 : Cert := (.node [(2,(.node [(1,(.node [(6,(.node [(5,(.node [(4,(.leaf ⟨7,47,3,false⟩))]))]))])),(6,(.node [(1,(.node [(5,(.node [(4,(.leaf ⟨19,85,6,false⟩))]))])),(5,(.node [(1,(.node [(4,(.leaf ⟨16,46,4,false⟩))]))]))]))])),(6,(.node [(2,(.node [(1,(.node [(5,(.node [(4,(.leaf ⟨19,8,7,true⟩))]))])),(5,(.node [(1,(.node [(4,(.leaf ⟨19,48,2,false⟩))]))]))]))]))])
theorem ok90837 : checkedLeaves maskTest 5 sub90837=true := by decide +kernel
def sub9087 : Cert := (.node [(3,(.node [(2,(.node [(1,(.node [(6,(.node [(5,(.node [(4,(.leaf ⟨9,47,3,false⟩))]))]))])),(6,(.node [(1,(.node [(5,(.node [(4,(.leaf ⟨19,64,3,true⟩))]))])),(5,(.node [(1,(.node [(4,(.leaf ⟨17,46,4,false⟩))]))]))]))])),(6,(.node [(2,(.node [(1,(.node [(5,(.node [(4,(.leaf ⟨16,103,5,true⟩))]))])),(5,(.node [(1,(.node [(4,(.leaf ⟨17,103,5,true⟩))]))]))]))]))]))])
theorem ok9087 : checkedLeaves maskTest 6 sub9087=true := by decide +kernel
def sub9410 : Cert := (.node [(3,(.node [(2,(.node [(6,(.node [(5,(.node [(8,(.node [(7,(.leaf ⟨5,7,8,false⟩))]))])),(8,(.node [(5,(.node [(7,(.leaf ⟨4,7,8,false⟩))]))]))]))])),(6,(.node [(2,(.node [(5,(.node [(8,(.node [(7,(.leaf ⟨14,7,8,false⟩))]))])),(8,(.node [(5,(.node [(7,(.leaf ⟨8,95,0,true⟩))]))]))])),(8,(.node [(2,(.node [(5,(.node [(7,(.leaf ⟨1,95,0,true⟩))]))]))]))]))]))])
theorem ok9410 : checkedLeaves maskTest 6 sub9410=true := by decide +kernel
def sub941630 : Cert := (.node [(2,(.node [(5,(.node [(8,(.node [(7,(.leaf ⟨14,13,6,true⟩))]))])),(8,(.node [(5,(.node [(7,(.leaf ⟨10,95,0,true⟩))]))]))])),(8,(.node [(2,(.node [(5,(.node [(7,(.leaf ⟨2,95,0,true⟩))]))]))]))])
theorem ok941630 : checkedLeaves maskTest 4 sub941630=true := by decide +kernel
def sub941635 : Cert := (.node [(2,(.node [(0,(.node [(8,(.node [(7,(.leaf ⟨15,71,2,false⟩))]))])),(8,(.node [(0,(.node [(7,(.leaf ⟨17,49,2,true⟩))])),(7,(.node [(0,(.leaf ⟨17,79,5,false⟩))]))]))])),(8,(.node [(2,(.node [(0,(.node [(7,(.leaf ⟨16,95,0,true⟩))])),(7,(.node [(0,(.leaf ⟨19,49,2,true⟩))]))]))]))])
theorem ok941635 : checkedLeaves maskTest 4 sub941635=true := by decide +kernel
def sub941638 : Cert := (.node [(0,(.node [(2,(.node [(5,(.node [(7,(.leaf ⟨4,72,3,false⟩))]))]))])),(5,(.node [(2,(.node [(0,(.node [(7,(.leaf ⟨11,108,5,true⟩))])),(7,(.node [(0,(.leaf ⟨9,78,4,false⟩))]))]))]))])
theorem ok941638 : checkedLeaves maskTest 4 sub941638=true := by decide +kernel
def sub94165 : Cert := (.node [(3,(.node [(2,(.node [(0,(.node [(8,(.node [(7,(.leaf ⟨11,3,7,true⟩))]))])),(8,(.node [(0,(.node [(7,(.leaf ⟨16,49,2,true⟩))])),(7,(.node [(0,(.leaf ⟨17,40,4,true⟩))]))]))])),(8,(.node [(2,(.node [(0,(.node [(7,(.leaf ⟨18,2,8,true⟩))])),(7,(.node [(0,(.leaf ⟨16,40,4,true⟩))]))]))]))]))])
theorem ok94165 : checkedLeaves maskTest 5 sub94165=true := by decide +kernel
def sub946130 : Cert := (.node [(2,(.node [(5,(.node [(8,(.node [(7,(.leaf ⟨5,13,6,true⟩))]))])),(8,(.node [(5,(.node [(7,(.leaf ⟨3,10,7,false⟩))]))]))])),(8,(.node [(2,(.node [(5,(.node [(7,(.leaf ⟨3,95,0,true⟩))]))]))]))])
theorem ok946130 : checkedLeaves maskTest 4 sub946130=true := by decide +kernel
end R67.OrderOrbit
