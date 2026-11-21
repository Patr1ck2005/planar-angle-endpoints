import OrderMaskCore
namespace R67.OrderOrbit
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000
def sub98765 : Cert := (.node [(3,(.node [(2,(.node [(0,(.node [(1,(.node [(4,(.leaf ⟨5,6,8,true⟩))]))])),(4,(.node [(1,(.node [(0,(.leaf ⟨15,0,9,true⟩))]))]))])),(4,(.node [(2,(.node [(1,(.node [(0,(.leaf ⟨7,0,9,true⟩))]))]))]))])),(4,(.node [(3,(.node [(2,(.node [(1,(.node [(0,(.leaf ⟨0,0,9,true⟩))]))]))]))]))])
theorem ok98765 : checkedLeaves maskTest 5 sub98765=true := by decide +kernel
end R67.OrderOrbit
