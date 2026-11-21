import OrderMaskCore
namespace R67.OrderOrbit
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000
def sub49685 : Cert := (.node [(3,(.node [(1,(.node [(2,(.node [(0,(.node [(7,(.leaf ⟨3,2,8,true⟩))])),(7,(.node [(0,(.leaf ⟨10,117,9,false⟩))]))]))])),(7,(.node [(2,(.node [(1,(.node [(0,(.leaf ⟨8,117,9,false⟩))]))]))]))])),(7,(.node [(3,(.node [(2,(.node [(1,(.node [(0,(.leaf ⟨4,0,9,true⟩))]))]))]))]))])
theorem ok49685 : checkedLeaves maskTest 5 sub49685=true := by decide +kernel
end R67.OrderOrbit
