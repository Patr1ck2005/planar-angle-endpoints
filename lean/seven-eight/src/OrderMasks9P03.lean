import OrderMaskCore
namespace R67.OrderOrbit
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000
def sub98031 : Cert := (.node [(2,(.node [(6,(.node [(4,(.node [(5,(.node [(7,(.leaf ⟨1,4,8,false⟩))]))])),(7,(.node [(5,(.node [(4,(.leaf ⟨2,4,8,false⟩))]))]))])),(7,(.node [(6,(.node [(5,(.node [(4,(.leaf ⟨4,15,5,true⟩))]))]))]))])),(6,(.node [(2,(.node [(4,(.node [(5,(.node [(7,(.leaf ⟨8,4,8,false⟩))]))])),(7,(.node [(5,(.node [(4,(.leaf ⟨10,4,8,false⟩))]))]))])),(4,(.node [(2,(.node [(5,(.node [(7,(.leaf ⟨4,95,0,true⟩))]))]))]))]))])
theorem ok98031 : checkedLeaves maskTest 5 sub98031=true := by decide +kernel
def sub98036 : Cert := (.node [(1,(.node [(2,(.node [(4,(.node [(5,(.node [(7,(.leaf ⟨14,95,0,true⟩))]))])),(7,(.node [(5,(.node [(4,(.leaf ⟨14,74,4,false⟩))]))]))])),(4,(.node [(2,(.node [(5,(.node [(7,(.leaf ⟨5,95,0,true⟩))]))]))]))])),(7,(.node [(2,(.node [(1,(.node [(5,(.node [(4,(.leaf ⟨15,102,4,true⟩))]))])),(5,(.node [(1,(.node [(4,(.leaf ⟨11,84,5,false⟩))]))]))]))]))])
theorem ok98036 : checkedLeaves maskTest 5 sub98036=true := by decide +kernel
def sub98037 : Cert := (.node [(2,(.node [(1,(.node [(6,(.node [(5,(.node [(4,(.leaf ⟨11,47,3,false⟩))]))]))])),(6,(.node [(1,(.node [(5,(.node [(4,(.leaf ⟨16,4,8,false⟩))]))])),(5,(.node [(1,(.node [(4,(.leaf ⟨18,4,8,false⟩))]))]))]))])),(6,(.node [(2,(.node [(1,(.node [(5,(.node [(4,(.leaf ⟨17,119,0,false⟩))]))])),(5,(.node [(1,(.node [(4,(.leaf ⟨16,119,0,false⟩))]))]))]))]))])
theorem ok98037 : checkedLeaves maskTest 5 sub98037=true := by decide +kernel
def sub9807 : Cert := (.node [(3,(.node [(2,(.node [(1,(.node [(6,(.node [(5,(.node [(4,(.leaf ⟨9,9,6,true⟩))]))]))])),(6,(.node [(1,(.node [(5,(.node [(4,(.leaf ⟨19,119,0,false⟩))]))])),(5,(.node [(1,(.node [(4,(.leaf ⟨16,48,2,false⟩))]))]))]))])),(6,(.node [(2,(.node [(1,(.node [(5,(.node [(4,(.leaf ⟨17,8,7,true⟩))]))])),(5,(.node [(1,(.node [(4,(.leaf ⟨17,48,2,false⟩))]))]))]))]))]))])
theorem ok9807 : checkedLeaves maskTest 6 sub9807=true := by decide +kernel
def sub98630 : Cert := (.node [(1,(.node [(2,(.node [(4,(.node [(5,(.node [(7,(.leaf ⟨6,18,7,false⟩))]))])),(7,(.node [(5,(.node [(4,(.leaf ⟨6,96,3,true⟩))]))]))])),(4,(.node [(2,(.node [(5,(.node [(7,(.leaf ⟨6,95,0,true⟩))]))]))]))])),(7,(.node [(2,(.node [(1,(.node [(5,(.node [(4,(.leaf ⟨5,96,3,true⟩))]))])),(5,(.node [(1,(.node [(4,(.leaf ⟨4,96,3,true⟩))]))]))]))]))])
theorem ok98630 : checkedLeaves maskTest 5 sub98630=true := by decide +kernel
def sub98634 : Cert := (.node [(1,(.node [(0,(.node [(2,(.node [(5,(.node [(7,(.leaf ⟨6,119,0,false⟩))]))]))])),(5,(.node [(2,(.node [(0,(.node [(7,(.leaf ⟨5,119,0,false⟩))])),(7,(.node [(0,(.leaf ⟨3,96,3,true⟩))]))]))]))])),(5,(.node [(1,(.node [(2,(.node [(0,(.node [(7,(.leaf ⟨4,119,0,false⟩))])),(7,(.node [(0,(.leaf ⟨2,96,3,true⟩))]))]))])),(7,(.node [(2,(.node [(1,(.node [(0,(.leaf ⟨1,96,3,true⟩))]))]))]))]))])
theorem ok98634 : checkedLeaves maskTest 5 sub98634=true := by decide +kernel
end R67.OrderOrbit
