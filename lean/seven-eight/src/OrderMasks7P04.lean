import OrderMaskCore
namespace R67.OrderOrbit
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000
def sub758624 : Cert := (.node [(3,(.node [(1,(.node [(0,(.node [(9,(.leaf ⟨9,1,8,true⟩))])),(9,(.node [(0,(.leaf ⟨19,111,8,false⟩))]))])),(9,(.node [(1,(.node [(0,(.leaf ⟨17,0,9,true⟩))]))]))]))])
theorem ok758624 : checkedLeaves maskTest 4 sub758624=true := by decide +kernel
def sub75864 : Cert := (.node [(2,(.node [(3,(.node [(1,(.node [(0,(.node [(9,(.leaf ⟨0,17,5,false⟩))])),(9,(.node [(0,(.leaf ⟨7,17,5,false⟩))]))])),(9,(.node [(1,(.node [(0,(.leaf ⟨15,17,5,false⟩))]))]))]))])),(9,(.node [(3,(.node [(2,(.node [(1,(.node [(0,(.leaf ⟨5,23,4,false⟩))]))]))]))]))])
theorem ok75864 : checkedLeaves maskTest 5 sub75864=true := by decide +kernel
def sub75869 : Cert := (.node [(3,(.node [(2,(.node [(0,(.node [(1,(.node [(4,(.leaf ⟨6,100,5,true⟩))]))])),(4,(.node [(1,(.node [(0,(.leaf ⟨5,100,5,true⟩))]))]))])),(4,(.node [(2,(.node [(1,(.node [(0,(.leaf ⟨3,111,8,false⟩))]))]))]))])),(4,(.node [(3,(.node [(2,(.node [(1,(.node [(0,(.leaf ⟨3,0,9,true⟩))]))]))]))]))])
theorem ok75869 : checkedLeaves maskTest 5 sub75869=true := by decide +kernel
def sub780231 : Cert := (.node [(5,(.node [(6,(.node [(4,(.node [(9,(.leaf ⟨0,3,8,false⟩))])),(9,(.node [(4,(.leaf ⟨0,11,5,true⟩))]))]))])),(9,(.node [(6,(.node [(5,(.node [(4,(.leaf ⟨1,11,5,true⟩))]))]))]))])
theorem ok780231 : checkedLeaves maskTest 4 sub780231=true := by decide +kernel
def sub780235 : Cert := (.node [(1,(.node [(6,(.node [(4,(.node [(9,(.leaf ⟨7,3,8,false⟩))])),(9,(.node [(4,(.leaf ⟨9,3,8,false⟩))]))]))])),(6,(.node [(1,(.node [(4,(.node [(9,(.leaf ⟨11,3,8,false⟩))])),(9,(.node [(4,(.leaf ⟨9,71,1,true⟩))]))])),(9,(.node [(1,(.node [(4,(.leaf ⟨0,48,2,false⟩))]))]))]))])
theorem ok780235 : checkedLeaves maskTest 4 sub780235=true := by decide +kernel
def sub780239 : Cert := (.node [(1,(.node [(6,(.node [(5,(.node [(4,(.leaf ⟨12,3,8,false⟩))]))]))])),(6,(.node [(1,(.node [(5,(.node [(4,(.leaf ⟨12,71,1,true⟩))]))])),(5,(.node [(1,(.node [(4,(.leaf ⟨1,48,2,false⟩))]))]))]))])
theorem ok780239 : checkedLeaves maskTest 4 sub780239=true := by decide +kernel
def sub78025 : Cert := (.node [(3,(.node [(1,(.node [(6,(.node [(4,(.node [(9,(.leaf ⟨15,3,8,false⟩))])),(9,(.node [(4,(.leaf ⟨11,71,1,true⟩))]))]))])),(6,(.node [(1,(.node [(4,(.node [(9,(.leaf ⟨15,71,1,true⟩))])),(9,(.node [(4,(.leaf ⟨7,71,1,true⟩))]))])),(9,(.node [(1,(.node [(4,(.leaf ⟨0,71,1,true⟩))]))]))]))]))])
theorem ok78025 : checkedLeaves maskTest 5 sub78025=true := by decide +kernel
def sub7809 : Cert := (.node [(3,(.node [(2,(.node [(1,(.node [(6,(.node [(5,(.node [(4,(.leaf ⟨12,9,6,true⟩))]))]))])),(6,(.node [(1,(.node [(5,(.node [(4,(.leaf ⟨13,71,1,true⟩))]))])),(5,(.node [(1,(.node [(4,(.leaf ⟨2,48,2,false⟩))]))]))]))])),(6,(.node [(2,(.node [(1,(.node [(5,(.node [(4,(.leaf ⟨10,103,5,true⟩))]))])),(5,(.node [(1,(.node [(4,(.leaf ⟨3,48,2,false⟩))]))]))]))]))]))])
theorem ok7809 : checkedLeaves maskTest 6 sub7809=true := by decide +kernel
end R67.OrderOrbit
