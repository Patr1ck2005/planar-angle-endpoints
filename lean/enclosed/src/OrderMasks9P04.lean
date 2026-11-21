import OrderMaskCore
namespace R67.OrderOrbit
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000
def sub98637 : Cert := (.node [(0,(.node [(2,(.node [(1,(.node [(5,(.node [(4,(.leaf ⟨3,119,0,false⟩))]))])),(5,(.node [(1,(.node [(4,(.leaf ⟨2,119,0,false⟩))]))]))]))])),(5,(.node [(2,(.node [(0,(.node [(1,(.node [(4,(.leaf ⟨1,119,0,false⟩))]))])),(4,(.node [(1,(.node [(0,(.leaf ⟨0,119,0,false⟩))]))]))])),(4,(.node [(2,(.node [(1,(.node [(0,(.leaf ⟨0,96,3,true⟩))]))]))]))]))])
theorem ok98637 : checkedLeaves maskTest 5 sub98637=true := by decide +kernel
def sub98643 : Cert := (.node [(1,(.node [(0,(.node [(2,(.node [(5,(.node [(7,(.leaf ⟨6,12,7,true⟩))]))]))])),(5,(.node [(2,(.node [(0,(.node [(7,(.leaf ⟨14,119,0,false⟩))])),(7,(.node [(0,(.leaf ⟨10,78,4,false⟩))]))]))]))])),(5,(.node [(1,(.node [(2,(.node [(0,(.node [(7,(.leaf ⟨8,2,8,true⟩))])),(7,(.node [(0,(.leaf ⟨13,119,0,false⟩))]))]))])),(7,(.node [(2,(.node [(1,(.node [(0,(.leaf ⟨12,119,0,false⟩))]))]))]))]))])
theorem ok98643 : checkedLeaves maskTest 5 sub98643=true := by decide +kernel
def sub98645 : Cert := (.node [(3,(.node [(1,(.node [(2,(.node [(0,(.node [(7,(.leaf ⟨1,2,8,true⟩))])),(7,(.node [(0,(.leaf ⟨12,21,5,false⟩))]))]))])),(7,(.node [(2,(.node [(1,(.node [(0,(.leaf ⟨12,0,9,true⟩))]))]))]))])),(7,(.node [(3,(.node [(2,(.node [(1,(.node [(0,(.leaf ⟨1,23,4,false⟩))]))]))]))]))])
theorem ok98645 : checkedLeaves maskTest 5 sub98645=true := by decide +kernel
def sub98673 : Cert := (.node [(0,(.node [(2,(.node [(1,(.node [(5,(.node [(4,(.leaf ⟨3,8,7,true⟩))]))])),(5,(.node [(1,(.node [(4,(.leaf ⟨10,119,0,false⟩))]))]))]))])),(5,(.node [(2,(.node [(0,(.node [(1,(.node [(4,(.leaf ⟨8,119,0,false⟩))]))])),(4,(.node [(1,(.node [(0,(.leaf ⟨7,119,0,false⟩))]))]))])),(4,(.node [(2,(.node [(1,(.node [(0,(.leaf ⟨9,119,0,false⟩))]))]))]))]))])
theorem ok98673 : checkedLeaves maskTest 5 sub98673=true := by decide +kernel
def sub98675 : Cert := (.node [(3,(.node [(2,(.node [(0,(.node [(1,(.node [(4,(.leaf ⟨4,6,8,true⟩))]))])),(4,(.node [(1,(.node [(0,(.leaf ⟨11,119,0,false⟩))]))]))])),(4,(.node [(2,(.node [(1,(.node [(0,(.leaf ⟨9,0,9,true⟩))]))]))]))])),(4,(.node [(3,(.node [(2,(.node [(1,(.node [(0,(.leaf ⟨0,23,4,false⟩))]))]))]))]))])
theorem ok98675 : checkedLeaves maskTest 5 sub98675=true := by decide +kernel
def sub9870 : Cert := (.node [(3,(.node [(2,(.node [(1,(.node [(6,(.node [(5,(.node [(4,(.leaf ⟨0,5,7,false⟩))]))]))])),(6,(.node [(1,(.node [(5,(.node [(4,(.leaf ⟨7,5,7,false⟩))]))])),(5,(.node [(1,(.node [(4,(.leaf ⟨11,5,7,false⟩))]))]))]))])),(6,(.node [(2,(.node [(1,(.node [(5,(.node [(4,(.leaf ⟨15,5,7,false⟩))]))])),(5,(.node [(1,(.node [(4,(.leaf ⟨15,65,2,true⟩))]))]))]))]))]))])
theorem ok9870 : checkedLeaves maskTest 6 sub9870=true := by decide +kernel
def sub98763 : Cert := (.node [(0,(.node [(2,(.node [(1,(.node [(5,(.node [(4,(.leaf ⟨5,19,6,false⟩))]))])),(5,(.node [(1,(.node [(4,(.leaf ⟨14,19,6,false⟩))]))]))]))])),(5,(.node [(2,(.node [(0,(.node [(1,(.node [(4,(.leaf ⟨14,6,8,true⟩))]))])),(4,(.node [(1,(.node [(0,(.leaf ⟨15,119,0,false⟩))]))]))])),(4,(.node [(2,(.node [(1,(.node [(0,(.leaf ⟨11,0,9,true⟩))]))]))]))]))])
theorem ok98763 : checkedLeaves maskTest 5 sub98763=true := by decide +kernel
end R67.OrderOrbit
