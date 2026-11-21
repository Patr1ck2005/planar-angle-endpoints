import OrderMaskCore
namespace R67.OrderOrbit
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000
def sub7890 : Cert := (.node [(3,(.node [(2,(.node [(1,(.node [(6,(.node [(5,(.node [(4,(.leaf ⟨1,5,7,false⟩))]))]))])),(6,(.node [(1,(.node [(5,(.node [(4,(.leaf ⟨8,5,7,false⟩))]))])),(5,(.node [(1,(.node [(4,(.leaf ⟨4,71,1,true⟩))]))]))]))])),(6,(.node [(2,(.node [(1,(.node [(5,(.node [(4,(.leaf ⟨14,71,1,true⟩))]))])),(5,(.node [(1,(.node [(4,(.leaf ⟨5,71,1,true⟩))]))]))]))]))]))])
theorem ok7890 : checkedLeaves maskTest 6 sub7890=true := by decide +kernel
def sub78963 : Cert := (.node [(0,(.node [(2,(.node [(1,(.node [(5,(.node [(4,(.leaf ⟨6,19,6,false⟩))]))])),(5,(.node [(1,(.node [(4,(.leaf ⟨6,71,1,true⟩))]))]))]))])),(5,(.node [(2,(.node [(0,(.node [(1,(.node [(4,(.leaf ⟨6,113,9,false⟩))]))])),(4,(.node [(1,(.node [(0,(.leaf ⟨5,113,9,false⟩))]))]))])),(4,(.node [(2,(.node [(1,(.node [(0,(.leaf ⟨4,113,9,false⟩))]))]))]))]))])
theorem ok78963 : checkedLeaves maskTest 5 sub78963=true := by decide +kernel
def sub78965 : Cert := (.node [(3,(.node [(2,(.node [(0,(.node [(1,(.node [(4,(.leaf ⟨6,6,8,true⟩))]))])),(4,(.node [(1,(.node [(0,(.leaf ⟨14,113,9,false⟩))]))]))])),(4,(.node [(2,(.node [(1,(.node [(0,(.leaf ⟨8,0,9,true⟩))]))]))]))])),(4,(.node [(3,(.node [(2,(.node [(1,(.node [(0,(.leaf ⟨1,0,9,true⟩))]))]))]))]))])
theorem ok78965 : checkedLeaves maskTest 5 sub78965=true := by decide +kernel
end R67.OrderOrbit
