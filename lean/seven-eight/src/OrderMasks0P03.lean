import OrderMaskCore
namespace R67.OrderOrbit
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000
def sub078231 : Cert := (.node [(5,(.node [(6,(.node [(4,(.node [(9,(.leaf ⟨9,41,4,false⟩))])),(9,(.node [(4,(.leaf ⟨11,11,5,true⟩))]))]))])),(9,(.node [(6,(.node [(5,(.node [(4,(.leaf ⟨4,47,3,false⟩))]))]))]))])
theorem ok078231 : checkedLeaves maskTest 4 sub078231=true := by decide +kernel
def sub078235 : Cert := (.node [(1,(.node [(6,(.node [(4,(.node [(9,(.leaf ⟨19,70,2,true⟩))])),(9,(.node [(4,(.leaf ⟨16,24,0,true⟩))]))]))])),(6,(.node [(1,(.node [(4,(.node [(9,(.leaf ⟨17,40,5,false⟩))])),(9,(.node [(4,(.leaf ⟨17,70,2,true⟩))]))])),(9,(.node [(1,(.node [(4,(.leaf ⟨15,48,2,false⟩))]))]))]))])
theorem ok078235 : checkedLeaves maskTest 4 sub078235=true := by decide +kernel
def sub078239 : Cert := (.node [(1,(.node [(6,(.node [(5,(.node [(4,(.leaf ⟨2,24,0,true⟩))]))]))])),(6,(.node [(1,(.node [(5,(.node [(4,(.leaf ⟨10,24,0,true⟩))]))])),(5,(.node [(1,(.node [(4,(.leaf ⟨14,106,6,true⟩))]))]))]))])
theorem ok078239 : checkedLeaves maskTest 4 sub078239=true := by decide +kernel
def sub07825 : Cert := (.node [(3,(.node [(1,(.node [(6,(.node [(4,(.node [(9,(.leaf ⟨16,79,4,true⟩))])),(9,(.node [(4,(.leaf ⟨18,10,6,true⟩))]))]))])),(6,(.node [(1,(.node [(4,(.node [(9,(.leaf ⟨17,79,4,true⟩))])),(9,(.node [(4,(.leaf ⟨16,70,2,true⟩))]))])),(9,(.node [(1,(.node [(4,(.leaf ⟨11,116,7,true⟩))]))]))]))]))])
theorem ok07825 : checkedLeaves maskTest 5 sub07825=true := by decide +kernel
def sub0789 : Cert := (.node [(3,(.node [(2,(.node [(1,(.node [(6,(.node [(5,(.node [(4,(.leaf ⟨1,24,0,true⟩))]))]))])),(6,(.node [(1,(.node [(5,(.node [(4,(.leaf ⟨8,24,0,true⟩))]))])),(5,(.node [(1,(.node [(4,(.leaf ⟨14,112,8,false⟩))]))]))]))])),(6,(.node [(2,(.node [(1,(.node [(5,(.node [(4,(.leaf ⟨4,112,8,false⟩))]))])),(5,(.node [(1,(.node [(4,(.leaf ⟨5,112,8,false⟩))]))]))]))]))]))])
theorem ok0789 : checkedLeaves maskTest 6 sub0789=true := by decide +kernel
def sub09132 : Cert := (.node [(4,(.node [(6,(.node [(5,(.node [(8,(.node [(7,(.leaf ⟨9,17,4,true⟩))]))])),(8,(.node [(5,(.node [(7,(.leaf ⟨7,17,4,true⟩))]))]))]))])),(8,(.node [(6,(.node [(4,(.node [(5,(.node [(7,(.leaf ⟨8,17,4,true⟩))]))])),(7,(.node [(5,(.node [(4,(.leaf ⟨10,17,4,true⟩))]))]))])),(7,(.node [(6,(.node [(5,(.node [(4,(.leaf ⟨3,47,3,false⟩))]))]))]))]))])
theorem ok09132 : checkedLeaves maskTest 5 sub09132=true := by decide +kernel
def sub09134 : Cert := (.node [(2,(.node [(6,(.node [(5,(.node [(8,(.node [(7,(.leaf ⟨19,71,2,false⟩))]))])),(8,(.node [(5,(.node [(7,(.leaf ⟨19,111,7,true⟩))]))]))]))])),(6,(.node [(2,(.node [(5,(.node [(8,(.node [(7,(.leaf ⟨16,73,4,false⟩))]))])),(8,(.node [(5,(.node [(7,(.leaf ⟨19,34,6,false⟩))]))]))])),(8,(.node [(2,(.node [(5,(.node [(7,(.leaf ⟨7,72,3,false⟩))]))]))]))]))])
theorem ok09134 : checkedLeaves maskTest 5 sub09134=true := by decide +kernel
end R67.OrderOrbit
