import OrderMaskCore
namespace R67.OrderOrbit
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000
def sub90132 : Cert := (.node [(4,(.node [(6,(.node [(5,(.node [(8,(.node [(7,(.leaf ⟨0,1,9,false⟩))]))])),(8,(.node [(5,(.node [(7,(.leaf ⟨0,17,4,true⟩))]))]))]))])),(8,(.node [(6,(.node [(4,(.node [(5,(.node [(7,(.leaf ⟨1,17,4,true⟩))]))])),(7,(.node [(5,(.node [(4,(.leaf ⟨2,17,4,true⟩))]))]))])),(7,(.node [(6,(.node [(5,(.node [(4,(.leaf ⟨3,17,4,true⟩))]))]))]))]))])
theorem ok90132 : checkedLeaves maskTest 5 sub90132=true := by decide +kernel
def sub90134 : Cert := (.node [(2,(.node [(6,(.node [(5,(.node [(8,(.node [(7,(.leaf ⟨7,1,9,false⟩))]))])),(8,(.node [(5,(.node [(7,(.leaf ⟨9,1,9,false⟩))]))]))]))])),(6,(.node [(2,(.node [(5,(.node [(8,(.node [(7,(.leaf ⟨11,1,9,false⟩))]))])),(8,(.node [(5,(.node [(7,(.leaf ⟨9,95,0,true⟩))]))]))])),(8,(.node [(2,(.node [(5,(.node [(7,(.leaf ⟨0,72,3,false⟩))]))]))]))]))])
theorem ok90134 : checkedLeaves maskTest 5 sub90134=true := by decide +kernel
def sub90138 : Cert := (.node [(2,(.node [(6,(.node [(4,(.node [(5,(.node [(7,(.leaf ⟨12,1,9,false⟩))]))])),(7,(.node [(5,(.node [(4,(.leaf ⟨13,1,9,false⟩))]))]))])),(7,(.node [(6,(.node [(5,(.node [(4,(.leaf ⟨10,47,3,false⟩))]))]))]))])),(6,(.node [(2,(.node [(4,(.node [(5,(.node [(7,(.leaf ⟨12,95,0,true⟩))]))])),(7,(.node [(5,(.node [(4,(.leaf ⟨12,74,4,false⟩))]))]))])),(4,(.node [(2,(.node [(5,(.node [(7,(.leaf ⟨1,72,3,false⟩))]))]))]))]))])
theorem ok90138 : checkedLeaves maskTest 5 sub90138=true := by decide +kernel
def sub9014 : Cert := (.node [(3,(.node [(2,(.node [(6,(.node [(5,(.node [(8,(.node [(7,(.leaf ⟨15,1,9,false⟩))]))])),(8,(.node [(5,(.node [(7,(.leaf ⟨11,95,0,true⟩))]))]))]))])),(6,(.node [(2,(.node [(5,(.node [(8,(.node [(7,(.leaf ⟨15,95,0,true⟩))]))])),(8,(.node [(5,(.node [(7,(.leaf ⟨7,95,0,true⟩))]))]))])),(8,(.node [(2,(.node [(5,(.node [(7,(.leaf ⟨0,95,0,true⟩))]))]))]))]))]))])
theorem ok9014 : checkedLeaves maskTest 6 sub9014=true := by decide +kernel
def sub90831 : Cert := (.node [(2,(.node [(6,(.node [(4,(.node [(5,(.node [(7,(.leaf ⟨12,15,5,true⟩))]))])),(7,(.node [(5,(.node [(4,(.leaf ⟨13,15,5,true⟩))]))]))])),(7,(.node [(6,(.node [(5,(.node [(4,(.leaf ⟨8,47,3,false⟩))]))]))]))])),(6,(.node [(2,(.node [(4,(.node [(5,(.node [(7,(.leaf ⟨13,95,0,true⟩))]))])),(7,(.node [(5,(.node [(4,(.leaf ⟨13,74,4,false⟩))]))]))])),(4,(.node [(2,(.node [(5,(.node [(7,(.leaf ⟨2,72,3,false⟩))]))]))]))]))])
theorem ok90831 : checkedLeaves maskTest 5 sub90831=true := by decide +kernel
def sub90836 : Cert := (.node [(1,(.node [(2,(.node [(4,(.node [(5,(.node [(7,(.leaf ⟨10,102,4,true⟩))]))])),(7,(.node [(5,(.node [(4,(.leaf ⟨8,102,4,true⟩))]))]))])),(4,(.node [(2,(.node [(5,(.node [(7,(.leaf ⟨3,72,3,false⟩))]))]))]))])),(7,(.node [(2,(.node [(1,(.node [(5,(.node [(4,(.leaf ⟨7,102,4,true⟩))]))])),(5,(.node [(1,(.node [(4,(.leaf ⟨9,102,4,true⟩))]))]))]))]))])
theorem ok90836 : checkedLeaves maskTest 5 sub90836=true := by decide +kernel
end R67.OrderOrbit
