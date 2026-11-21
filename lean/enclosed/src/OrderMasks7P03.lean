import OrderMaskCore
namespace R67.OrderOrbit
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000
def sub75462 : Cert := (.node [(1,(.node [(3,(.node [(0,(.node [(8,(.node [(9,(.leaf ⟨1,4,7,true⟩))]))])),(8,(.node [(0,(.node [(9,(.leaf ⟨12,15,6,false⟩))])),(9,(.node [(0,(.leaf ⟨12,45,3,true⟩))]))]))]))])),(8,(.node [(3,(.node [(1,(.node [(0,(.node [(9,(.leaf ⟨12,1,8,true⟩))])),(9,(.node [(0,(.leaf ⟨13,45,3,true⟩))]))])),(9,(.node [(1,(.node [(0,(.leaf ⟨10,115,7,true⟩))]))]))]))]))])
theorem ok75462 : checkedLeaves maskTest 5 sub75462=true := by decide +kernel
def sub75468 : Cert := (.node [(2,(.node [(3,(.node [(1,(.node [(0,(.node [(9,(.leaf ⟨1,17,5,false⟩))])),(9,(.node [(0,(.leaf ⟨8,17,5,false⟩))]))])),(9,(.node [(1,(.node [(0,(.leaf ⟨14,45,3,true⟩))]))]))]))])),(9,(.node [(3,(.node [(2,(.node [(1,(.node [(0,(.leaf ⟨6,23,4,false⟩))]))]))]))]))])
theorem ok75468 : checkedLeaves maskTest 5 sub75468=true := by decide +kernel
def sub75820 : Cert := (.node [(3,(.node [(1,(.node [(6,(.node [(4,(.node [(9,(.leaf ⟨3,10,6,true⟩))])),(9,(.node [(4,(.leaf ⟨2,10,6,true⟩))]))]))])),(6,(.node [(1,(.node [(4,(.node [(9,(.leaf ⟨10,95,1,false⟩))])),(9,(.node [(4,(.leaf ⟨13,13,7,false⟩))]))])),(9,(.node [(1,(.node [(4,(.leaf ⟨12,48,2,false⟩))]))]))]))]))])
theorem ok75820 : checkedLeaves maskTest 5 sub75820=true := by decide +kernel
def sub7582630 : Cert := (.node [(1,(.node [(4,(.node [(9,(.leaf ⟨8,95,1,false⟩))])),(9,(.node [(4,(.leaf ⟨13,7,7,true⟩))]))])),(9,(.node [(1,(.node [(4,(.leaf ⟨13,48,2,false⟩))]))]))])
theorem ok7582630 : checkedLeaves maskTest 3 sub7582630=true := by decide +kernel
def sub7582634 : Cert := (.node [(1,(.node [(0,(.node [(9,(.leaf ⟨7,95,1,false⟩))])),(9,(.node [(0,(.leaf ⟨19,55,4,false⟩))]))])),(9,(.node [(1,(.node [(0,(.leaf ⟨19,0,9,true⟩))]))]))])
theorem ok7582634 : checkedLeaves maskTest 3 sub7582634=true := by decide +kernel
def sub7582639 : Cert := (.node [(0,(.node [(1,(.node [(4,(.leaf ⟨8,114,6,true⟩))]))])),(4,(.node [(1,(.node [(0,(.leaf ⟨7,114,6,true⟩))]))]))])
theorem ok7582639 : checkedLeaves maskTest 3 sub7582639=true := by decide +kernel
def sub758264 : Cert := (.node [(3,(.node [(1,(.node [(0,(.node [(9,(.leaf ⟨9,95,1,false⟩))])),(9,(.node [(0,(.leaf ⟨19,34,5,true⟩))]))])),(9,(.node [(1,(.node [(0,(.leaf ⟨16,115,7,true⟩))]))]))]))])
theorem ok758264 : checkedLeaves maskTest 4 sub758264=true := by decide +kernel
def sub7586230 : Cert := (.node [(1,(.node [(4,(.node [(9,(.leaf ⟨4,7,7,true⟩))])),(9,(.node [(4,(.leaf ⟨2,16,6,false⟩))]))])),(9,(.node [(1,(.node [(4,(.leaf ⟨10,16,6,false⟩))]))]))])
theorem ok7586230 : checkedLeaves maskTest 3 sub7586230=true := by decide +kernel
def sub7586234 : Cert := (.node [(1,(.node [(0,(.node [(9,(.leaf ⟨11,95,1,false⟩))])),(9,(.node [(0,(.leaf ⟨16,16,6,false⟩))]))])),(9,(.node [(1,(.node [(0,(.leaf ⟨17,111,8,false⟩))]))]))])
theorem ok7586234 : checkedLeaves maskTest 3 sub7586234=true := by decide +kernel
def sub7586239 : Cert := (.node [(0,(.node [(1,(.node [(4,(.leaf ⟨14,48,2,false⟩))]))])),(4,(.node [(1,(.node [(0,(.leaf ⟨15,114,6,true⟩))]))]))])
theorem ok7586239 : checkedLeaves maskTest 3 sub7586239=true := by decide +kernel
end R67.OrderOrbit
