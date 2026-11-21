import OrderMaskCore
namespace R67.OrderOrbit
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000
def sub01234 : Cert := (.node [(5,(.node [(6,(.node [(7,(.node [(8,(.node [(9,(.leaf ⟨0,0,0,false⟩))]))])),(9,(.node [(8,(.node [(7,(.leaf ⟨1,0,0,false⟩))]))]))])),(7,(.node [(6,(.node [(8,(.node [(9,(.leaf ⟨0,23,3,true⟩))]))]))]))])),(9,(.node [(6,(.node [(5,(.node [(8,(.node [(7,(.leaf ⟨2,0,0,false⟩))]))])),(8,(.node [(5,(.node [(7,(.leaf ⟨3,0,0,false⟩))]))]))]))]))])
theorem ok01234 : checkedLeaves maskTest 5 sub01234=true := by decide +kernel
def sub01237 : Cert := (.node [(5,(.node [(4,(.node [(6,(.node [(8,(.node [(9,(.leaf ⟨1,23,3,true⟩))]))]))])),(8,(.node [(6,(.node [(4,(.node [(9,(.leaf ⟨2,23,3,true⟩))])),(9,(.node [(4,(.leaf ⟨4,0,0,false⟩))]))]))]))])),(8,(.node [(5,(.node [(6,(.node [(4,(.node [(9,(.leaf ⟨3,23,3,true⟩))])),(9,(.node [(4,(.leaf ⟨5,0,0,false⟩))]))]))])),(9,(.node [(6,(.node [(5,(.node [(4,(.leaf ⟨6,0,0,false⟩))]))]))]))]))])
theorem ok01237 : checkedLeaves maskTest 5 sub01237=true := by decide +kernel
def sub01239 : Cert := (.node [(4,(.node [(6,(.node [(5,(.node [(8,(.node [(7,(.leaf ⟨4,23,3,true⟩))]))])),(8,(.node [(5,(.node [(7,(.leaf ⟨5,23,3,true⟩))]))]))]))])),(8,(.node [(6,(.node [(4,(.node [(5,(.node [(7,(.leaf ⟨6,23,3,true⟩))]))])),(7,(.node [(5,(.node [(4,(.leaf ⟨6,101,7,false⟩))]))]))])),(7,(.node [(6,(.node [(5,(.node [(4,(.leaf ⟨6,24,0,true⟩))]))]))]))]))])
theorem ok01239 : checkedLeaves maskTest 5 sub01239=true := by decide +kernel
def sub01243 : Cert := (.node [(5,(.node [(6,(.node [(7,(.node [(8,(.node [(9,(.leaf ⟨7,0,0,false⟩))]))])),(9,(.node [(8,(.node [(7,(.leaf ⟨8,0,0,false⟩))]))]))])),(7,(.node [(6,(.node [(8,(.node [(9,(.leaf ⟨9,0,0,false⟩))]))]))]))])),(9,(.node [(6,(.node [(5,(.node [(8,(.node [(7,(.leaf ⟨10,0,0,false⟩))]))])),(8,(.node [(5,(.node [(7,(.leaf ⟨3,111,7,true⟩))]))]))]))]))])
theorem ok01243 : checkedLeaves maskTest 5 sub01243=true := by decide +kernel
def sub01245 : Cert := (.node [(3,(.node [(6,(.node [(7,(.node [(8,(.node [(9,(.leaf ⟨11,0,0,false⟩))]))])),(9,(.node [(8,(.node [(7,(.leaf ⟨4,113,8,true⟩))]))]))])),(7,(.node [(6,(.node [(8,(.node [(9,(.leaf ⟨9,119,9,true⟩))]))]))]))])),(7,(.node [(3,(.node [(6,(.node [(8,(.node [(9,(.leaf ⟨0,96,4,false⟩))]))]))]))]))])
theorem ok01245 : checkedLeaves maskTest 5 sub01245=true := by decide +kernel
def sub01273 : Cert := (.node [(5,(.node [(4,(.node [(6,(.node [(8,(.node [(9,(.leaf ⟨12,0,0,false⟩))]))]))])),(8,(.node [(6,(.node [(4,(.node [(9,(.leaf ⟨13,0,0,false⟩))])),(9,(.node [(4,(.leaf ⟨8,117,8,true⟩))]))]))]))])),(8,(.node [(5,(.node [(6,(.node [(4,(.node [(9,(.leaf ⟨10,41,4,false⟩))])),(9,(.node [(4,(.leaf ⟨14,0,0,false⟩))]))]))])),(9,(.node [(6,(.node [(5,(.node [(4,(.leaf ⟨6,107,7,true⟩))]))]))]))]))])
theorem ok01273 : checkedLeaves maskTest 5 sub01273=true := by decide +kernel
def sub01275 : Cert := (.node [(3,(.node [(4,(.node [(6,(.node [(8,(.node [(9,(.leaf ⟨12,119,9,true⟩))]))]))])),(8,(.node [(6,(.node [(4,(.node [(9,(.leaf ⟨12,98,5,false⟩))])),(9,(.node [(4,(.leaf ⟨1,117,8,true⟩))]))]))]))])),(4,(.node [(3,(.node [(6,(.node [(8,(.node [(9,(.leaf ⟨1,96,4,false⟩))]))]))]))]))])
theorem ok01275 : checkedLeaves maskTest 5 sub01275=true := by decide +kernel
end R67.OrderOrbit
