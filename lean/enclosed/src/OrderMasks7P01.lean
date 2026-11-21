import OrderMaskCore
namespace R67.OrderOrbit
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000
def sub708231 : Cert := (.node [(5,(.node [(6,(.node [(4,(.node [(9,(.leaf ⟨9,11,5,true⟩))])),(9,(.node [(4,(.leaf ⟨7,11,5,true⟩))]))]))])),(9,(.node [(6,(.node [(5,(.node [(4,(.leaf ⟨8,11,5,true⟩))]))]))]))])
theorem ok708231 : checkedLeaves maskTest 4 sub708231=true := by decide +kernel
def sub708235 : Cert := (.node [(1,(.node [(6,(.node [(4,(.node [(9,(.leaf ⟨19,95,1,false⟩))])),(9,(.node [(4,(.leaf ⟨19,117,8,true⟩))]))]))])),(6,(.node [(1,(.node [(4,(.node [(9,(.leaf ⟨16,49,3,false⟩))])),(9,(.node [(4,(.leaf ⟨19,40,5,false⟩))]))])),(9,(.node [(1,(.node [(4,(.leaf ⟨7,48,2,false⟩))]))]))]))])
theorem ok708235 : checkedLeaves maskTest 4 sub708235=true := by decide +kernel
def sub708239 : Cert := (.node [(1,(.node [(6,(.node [(5,(.node [(4,(.leaf ⟨13,47,3,false⟩))]))]))])),(6,(.node [(1,(.node [(5,(.node [(4,(.leaf ⟨13,106,6,true⟩))]))])),(5,(.node [(1,(.node [(4,(.leaf ⟨8,48,2,false⟩))]))]))]))])
theorem ok708239 : checkedLeaves maskTest 4 sub708239=true := by decide +kernel
def sub70825 : Cert := (.node [(3,(.node [(1,(.node [(6,(.node [(4,(.node [(9,(.leaf ⟨17,10,6,true⟩))])),(9,(.node [(4,(.leaf ⟨16,10,6,true⟩))]))]))])),(6,(.node [(1,(.node [(4,(.node [(9,(.leaf ⟨17,49,3,false⟩))])),(9,(.node [(4,(.leaf ⟨19,79,4,true⟩))]))])),(9,(.node [(1,(.node [(4,(.leaf ⟨9,48,2,false⟩))]))]))]))]))])
theorem ok70825 : checkedLeaves maskTest 5 sub70825=true := by decide +kernel
def sub7089 : Cert := (.node [(3,(.node [(2,(.node [(1,(.node [(6,(.node [(5,(.node [(4,(.leaf ⟨12,47,3,false⟩))]))]))])),(6,(.node [(1,(.node [(5,(.node [(4,(.leaf ⟨13,112,8,false⟩))]))])),(5,(.node [(1,(.node [(4,(.leaf ⟨10,48,2,false⟩))]))]))]))])),(6,(.node [(2,(.node [(1,(.node [(5,(.node [(4,(.leaf ⟨2,103,5,true⟩))]))])),(5,(.node [(1,(.node [(4,(.leaf ⟨3,103,5,true⟩))]))]))]))]))]))])
theorem ok7089 : checkedLeaves maskTest 6 sub7089=true := by decide +kernel
def sub75201 : Cert := (.node [(3,(.node [(4,(.node [(6,(.node [(8,(.node [(9,(.leaf ⟨6,12,8,false⟩))]))]))])),(8,(.node [(6,(.node [(4,(.node [(9,(.leaf ⟨6,72,2,true⟩))])),(9,(.node [(4,(.leaf ⟨6,98,5,false⟩))]))]))]))])),(4,(.node [(3,(.node [(6,(.node [(8,(.node [(9,(.leaf ⟨6,119,9,true⟩))]))]))]))]))])
theorem ok75201 : checkedLeaves maskTest 5 sub75201=true := by decide +kernel
def sub75208 : Cert := (.node [(3,(.node [(1,(.node [(6,(.node [(4,(.node [(9,(.leaf ⟨5,72,2,true⟩))])),(9,(.node [(4,(.leaf ⟨14,72,2,true⟩))]))]))])),(6,(.node [(1,(.node [(4,(.node [(9,(.leaf ⟨4,72,2,true⟩))])),(9,(.node [(4,(.leaf ⟨8,108,6,false⟩))]))])),(9,(.node [(1,(.node [(4,(.leaf ⟨1,108,6,false⟩))]))]))]))]))])
theorem ok75208 : checkedLeaves maskTest 5 sub75208=true := by decide +kernel
def sub75241 : Cert := (.node [(0,(.node [(3,(.node [(6,(.node [(8,(.node [(9,(.leaf ⟨6,95,1,false⟩))]))]))]))])),(6,(.node [(3,(.node [(0,(.node [(8,(.node [(9,(.leaf ⟨5,95,1,false⟩))]))])),(8,(.node [(0,(.node [(9,(.leaf ⟨3,72,2,true⟩))])),(9,(.node [(0,(.leaf ⟨3,102,5,false⟩))]))]))]))]))])
theorem ok75241 : checkedLeaves maskTest 5 sub75241=true := by decide +kernel
end R67.OrderOrbit
