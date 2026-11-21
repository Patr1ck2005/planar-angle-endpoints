import OrderMaskCore
namespace R67.OrderOrbit
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000
def sub946135 : Cert := (.node [(2,(.node [(0,(.node [(8,(.node [(7,(.leaf ⟨15,3,7,true⟩))]))])),(8,(.node [(0,(.node [(7,(.leaf ⟨17,10,7,false⟩))])),(7,(.node [(0,(.leaf ⟨16,79,5,false⟩))]))]))])),(8,(.node [(2,(.node [(0,(.node [(7,(.leaf ⟨17,95,0,true⟩))])),(7,(.node [(0,(.leaf ⟨19,10,7,false⟩))]))]))]))])
theorem ok946135 : checkedLeaves maskTest 4 sub946135=true := by decide +kernel
def sub946138 : Cert := (.node [(0,(.node [(2,(.node [(5,(.node [(7,(.leaf ⟨5,72,3,false⟩))]))]))])),(5,(.node [(2,(.node [(0,(.node [(7,(.leaf ⟨15,78,4,false⟩))])),(7,(.node [(0,(.leaf ⟨7,78,4,false⟩))]))]))]))])
theorem ok946138 : checkedLeaves maskTest 4 sub946138=true := by decide +kernel
def sub94615 : Cert := (.node [(3,(.node [(2,(.node [(0,(.node [(8,(.node [(7,(.leaf ⟨7,3,7,true⟩))]))])),(8,(.node [(0,(.node [(7,(.leaf ⟨19,95,0,true⟩))])),(7,(.node [(0,(.leaf ⟨19,70,3,false⟩))]))]))])),(8,(.node [(2,(.node [(0,(.node [(7,(.leaf ⟨16,2,8,true⟩))])),(7,(.node [(0,(.leaf ⟨19,109,6,true⟩))]))]))]))]))])
theorem ok94615 : checkedLeaves maskTest 5 sub94615=true := by decide +kernel
def sub94651 : Cert := (.node [(3,(.node [(2,(.node [(0,(.node [(8,(.node [(7,(.leaf ⟨0,3,7,true⟩))]))])),(8,(.node [(0,(.node [(7,(.leaf ⟨9,11,6,false⟩))])),(7,(.node [(0,(.leaf ⟨9,41,3,true⟩))]))]))])),(8,(.node [(2,(.node [(0,(.node [(7,(.leaf ⟨11,41,3,true⟩))])),(7,(.node [(0,(.leaf ⟨7,41,3,true⟩))]))]))]))]))])
theorem ok94651 : checkedLeaves maskTest 5 sub94651=true := by decide +kernel
def sub94658 : Cert := (.node [(3,(.node [(1,(.node [(2,(.node [(0,(.node [(7,(.leaf ⟨4,21,5,false⟩))])),(7,(.node [(0,(.leaf ⟨8,41,3,true⟩))]))]))])),(7,(.node [(2,(.node [(1,(.node [(0,(.leaf ⟨10,41,3,true⟩))]))]))]))])),(7,(.node [(3,(.node [(2,(.node [(1,(.node [(0,(.leaf ⟨3,23,4,false⟩))]))]))]))]))])
theorem ok94658 : checkedLeaves maskTest 5 sub94658=true := by decide +kernel
def sub94683 : Cert := (.node [(1,(.node [(0,(.node [(2,(.node [(5,(.node [(7,(.leaf ⟨6,72,3,false⟩))]))]))])),(5,(.node [(2,(.node [(0,(.node [(7,(.leaf ⟨14,98,4,true⟩))])),(7,(.node [(0,(.leaf ⟨8,78,4,false⟩))]))]))]))])),(5,(.node [(1,(.node [(2,(.node [(0,(.node [(7,(.leaf ⟨10,2,8,true⟩))])),(7,(.node [(0,(.leaf ⟨13,98,4,true⟩))]))]))])),(7,(.node [(2,(.node [(1,(.node [(0,(.leaf ⟨12,98,4,true⟩))]))]))]))]))])
theorem ok94683 : checkedLeaves maskTest 5 sub94683=true := by decide +kernel
def sub94685 : Cert := (.node [(3,(.node [(1,(.node [(2,(.node [(0,(.node [(7,(.leaf ⟨2,2,8,true⟩))])),(7,(.node [(0,(.leaf ⟨13,21,5,false⟩))]))]))])),(7,(.node [(2,(.node [(1,(.node [(0,(.leaf ⟨13,0,9,true⟩))]))]))]))])),(7,(.node [(3,(.node [(2,(.node [(1,(.node [(0,(.leaf ⟨2,23,4,false⟩))]))]))]))]))])
theorem ok94685 : checkedLeaves maskTest 5 sub94685=true := by decide +kernel
end R67.OrderOrbit
