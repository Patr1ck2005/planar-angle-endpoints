import OrderMaskCore
namespace R67.OrderOrbit
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000
def sub09138 : Cert := (.node [(2,(.node [(6,(.node [(4,(.node [(5,(.node [(7,(.leaf ⟨13,45,4,false⟩))]))])),(7,(.node [(5,(.node [(4,(.leaf ⟨13,24,0,true⟩))]))]))])),(7,(.node [(6,(.node [(5,(.node [(4,(.leaf ⟨2,47,3,false⟩))]))]))]))])),(6,(.node [(2,(.node [(4,(.node [(5,(.node [(7,(.leaf ⟨13,104,5,true⟩))]))])),(7,(.node [(5,(.node [(4,(.leaf ⟨12,104,5,true⟩))]))]))])),(4,(.node [(2,(.node [(5,(.node [(7,(.leaf ⟨8,72,3,false⟩))]))]))]))]))])
theorem ok09138 : checkedLeaves maskTest 5 sub09138=true := by decide +kernel
def sub0914 : Cert := (.node [(3,(.node [(2,(.node [(6,(.node [(5,(.node [(8,(.node [(7,(.leaf ⟨17,16,5,true⟩))]))])),(8,(.node [(5,(.node [(7,(.leaf ⟨16,16,5,true⟩))]))]))]))])),(6,(.node [(2,(.node [(5,(.node [(8,(.node [(7,(.leaf ⟨17,73,4,false⟩))]))])),(8,(.node [(5,(.node [(7,(.leaf ⟨19,55,3,true⟩))]))]))])),(8,(.node [(2,(.node [(5,(.node [(7,(.leaf ⟨9,72,3,false⟩))]))]))]))]))]))])
theorem ok0914 : checkedLeaves maskTest 6 sub0914=true := by decide +kernel
def sub09831 : Cert := (.node [(2,(.node [(6,(.node [(4,(.node [(5,(.node [(7,(.leaf ⟨12,45,4,false⟩))]))])),(7,(.node [(5,(.node [(4,(.leaf ⟨12,24,0,true⟩))]))]))])),(7,(.node [(6,(.node [(5,(.node [(4,(.leaf ⟨1,47,3,false⟩))]))]))]))])),(6,(.node [(2,(.node [(4,(.node [(5,(.node [(7,(.leaf ⟨13,118,9,false⟩))]))])),(7,(.node [(5,(.node [(4,(.leaf ⟨12,118,9,false⟩))]))]))])),(4,(.node [(2,(.node [(5,(.node [(7,(.leaf ⟨10,72,3,false⟩))]))]))]))]))])
theorem ok09831 : checkedLeaves maskTest 5 sub09831=true := by decide +kernel
def sub09836 : Cert := (.node [(1,(.node [(2,(.node [(4,(.node [(5,(.node [(7,(.leaf ⟨2,102,4,true⟩))]))])),(7,(.node [(5,(.node [(4,(.leaf ⟨1,102,4,true⟩))]))]))])),(4,(.node [(2,(.node [(5,(.node [(7,(.leaf ⟨3,102,4,true⟩))]))]))]))])),(7,(.node [(2,(.node [(1,(.node [(5,(.node [(4,(.leaf ⟨0,102,4,true⟩))]))])),(5,(.node [(1,(.node [(4,(.leaf ⟨0,118,9,false⟩))]))]))]))]))])
theorem ok09836 : checkedLeaves maskTest 5 sub09836=true := by decide +kernel
def sub09837 : Cert := (.node [(2,(.node [(1,(.node [(6,(.node [(5,(.node [(4,(.leaf ⟨0,47,3,false⟩))]))]))])),(6,(.node [(1,(.node [(5,(.node [(4,(.leaf ⟨9,24,0,true⟩))]))])),(5,(.node [(1,(.node [(4,(.leaf ⟨11,118,9,false⟩))]))]))]))])),(6,(.node [(2,(.node [(1,(.node [(5,(.node [(4,(.leaf ⟨9,118,9,false⟩))]))])),(5,(.node [(1,(.node [(4,(.leaf ⟨7,118,9,false⟩))]))]))]))]))])
theorem ok09837 : checkedLeaves maskTest 5 sub09837=true := by decide +kernel
def sub0987 : Cert := (.node [(3,(.node [(2,(.node [(1,(.node [(6,(.node [(5,(.node [(4,(.leaf ⟨0,24,0,true⟩))]))]))])),(6,(.node [(1,(.node [(5,(.node [(4,(.leaf ⟨7,24,0,true⟩))]))])),(5,(.node [(1,(.node [(4,(.leaf ⟨15,24,0,true⟩))]))]))]))])),(6,(.node [(2,(.node [(1,(.node [(5,(.node [(4,(.leaf ⟨11,24,0,true⟩))]))])),(5,(.node [(1,(.node [(4,(.leaf ⟨15,118,9,false⟩))]))]))]))]))]))])
theorem ok0987 : checkedLeaves maskTest 6 sub0987=true := by decide +kernel
end R67.OrderOrbit
