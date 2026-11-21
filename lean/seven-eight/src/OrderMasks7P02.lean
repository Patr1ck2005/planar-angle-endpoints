import OrderMaskCore
namespace R67.OrderOrbit
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000
def sub75246 : Cert := (.node [(1,(.node [(3,(.node [(0,(.node [(8,(.node [(9,(.leaf ⟨4,95,1,false⟩))]))])),(8,(.node [(0,(.node [(9,(.leaf ⟨2,72,2,true⟩))])),(9,(.node [(0,(.leaf ⟨10,72,2,true⟩))]))]))]))])),(8,(.node [(3,(.node [(1,(.node [(0,(.node [(9,(.leaf ⟨1,72,2,true⟩))])),(9,(.node [(0,(.leaf ⟨8,72,2,true⟩))]))])),(9,(.node [(1,(.node [(0,(.leaf ⟨4,104,6,false⟩))]))]))]))]))])
theorem ok75246 : checkedLeaves maskTest 5 sub75246=true := by decide +kernel
def sub75280 : Cert := (.node [(3,(.node [(1,(.node [(6,(.node [(4,(.node [(9,(.leaf ⟨3,95,1,false⟩))])),(9,(.node [(4,(.leaf ⟨10,10,6,true⟩))]))]))])),(6,(.node [(1,(.node [(4,(.node [(9,(.leaf ⟨2,95,1,false⟩))])),(9,(.node [(4,(.leaf ⟨13,72,2,true⟩))]))])),(9,(.node [(1,(.node [(4,(.leaf ⟨12,116,7,true⟩))]))]))]))]))])
theorem ok75280 : checkedLeaves maskTest 5 sub75280=true := by decide +kernel
def sub7528630 : Cert := (.node [(1,(.node [(4,(.node [(9,(.leaf ⟨1,95,1,false⟩))])),(9,(.node [(4,(.leaf ⟨12,72,2,true⟩))]))])),(9,(.node [(1,(.node [(4,(.leaf ⟨12,110,7,false⟩))]))]))])
theorem ok7528630 : checkedLeaves maskTest 3 sub7528630=true := by decide +kernel
def sub7528634 : Cert := (.node [(1,(.node [(0,(.node [(9,(.leaf ⟨0,95,1,false⟩))])),(9,(.node [(0,(.leaf ⟨9,72,2,true⟩))]))])),(9,(.node [(1,(.node [(0,(.leaf ⟨9,110,7,false⟩))]))]))])
theorem ok7528634 : checkedLeaves maskTest 3 sub7528634=true := by decide +kernel
def sub7528639 : Cert := (.node [(0,(.node [(1,(.node [(4,(.leaf ⟨1,114,6,true⟩))]))])),(4,(.node [(1,(.node [(0,(.leaf ⟨0,114,6,true⟩))]))]))])
theorem ok7528639 : checkedLeaves maskTest 3 sub7528639=true := by decide +kernel
def sub752864 : Cert := (.node [(3,(.node [(1,(.node [(0,(.node [(9,(.leaf ⟨0,72,2,true⟩))])),(9,(.node [(0,(.leaf ⟨7,72,2,true⟩))]))])),(9,(.node [(1,(.node [(0,(.leaf ⟨11,72,2,true⟩))]))]))]))])
theorem ok752864 : checkedLeaves maskTest 4 sub752864=true := by decide +kernel
def sub75421 : Cert := (.node [(0,(.node [(3,(.node [(6,(.node [(8,(.node [(9,(.leaf ⟨6,18,6,true⟩))]))]))]))])),(6,(.node [(3,(.node [(0,(.node [(8,(.node [(9,(.leaf ⟨14,95,1,false⟩))]))])),(8,(.node [(0,(.node [(9,(.leaf ⟨10,102,5,false⟩))])),(9,(.node [(0,(.leaf ⟨2,102,5,false⟩))]))]))]))]))])
theorem ok75421 : checkedLeaves maskTest 5 sub75421=true := by decide +kernel
def sub75426 : Cert := (.node [(1,(.node [(3,(.node [(0,(.node [(8,(.node [(9,(.leaf ⟨8,4,7,true⟩))]))])),(8,(.node [(0,(.node [(9,(.leaf ⟨13,95,1,false⟩))])),(9,(.node [(0,(.leaf ⟨13,118,8,true⟩))]))]))]))])),(8,(.node [(3,(.node [(1,(.node [(0,(.node [(9,(.leaf ⟨12,95,1,false⟩))])),(9,(.node [(0,(.leaf ⟨13,104,6,false⟩))]))])),(9,(.node [(1,(.node [(0,(.leaf ⟨2,115,7,true⟩))]))]))]))]))])
theorem ok75426 : checkedLeaves maskTest 5 sub75426=true := by decide +kernel
end R67.OrderOrbit
