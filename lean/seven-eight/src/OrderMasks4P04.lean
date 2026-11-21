import OrderMaskCore
namespace R67.OrderOrbit
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000
def sub45721 : Cert := (.node [(0,(.node [(3,(.node [(6,(.node [(8,(.node [(9,(.leaf ⟨6,96,4,false⟩))]))]))]))])),(6,(.node [(3,(.node [(0,(.node [(8,(.node [(9,(.leaf ⟨14,74,3,true⟩))]))])),(8,(.node [(0,(.node [(9,(.leaf ⟨8,102,5,false⟩))])),(9,(.node [(0,(.leaf ⟨1,102,5,false⟩))]))]))]))]))])
theorem ok45721 : checkedLeaves maskTest 5 sub45721=true := by decide +kernel
def sub45726 : Cert := (.node [(1,(.node [(3,(.node [(0,(.node [(8,(.node [(9,(.leaf ⟨10,4,7,true⟩))]))])),(8,(.node [(0,(.node [(9,(.leaf ⟨13,74,3,true⟩))])),(9,(.node [(0,(.leaf ⟨12,118,8,true⟩))]))]))]))])),(8,(.node [(3,(.node [(1,(.node [(0,(.node [(9,(.leaf ⟨12,74,3,true⟩))])),(9,(.node [(0,(.leaf ⟨12,104,6,false⟩))]))])),(9,(.node [(1,(.node [(0,(.leaf ⟨1,115,7,true⟩))]))]))]))]))])
theorem ok45726 : checkedLeaves maskTest 5 sub45726=true := by decide +kernel
def sub45762 : Cert := (.node [(1,(.node [(3,(.node [(0,(.node [(8,(.node [(9,(.leaf ⟨2,4,7,true⟩))]))])),(8,(.node [(0,(.node [(9,(.leaf ⟨13,15,6,false⟩))])),(9,(.node [(0,(.leaf ⟨12,24,1,false⟩))]))]))]))])),(8,(.node [(3,(.node [(1,(.node [(0,(.node [(9,(.leaf ⟨13,1,8,true⟩))])),(9,(.node [(0,(.leaf ⟨13,24,1,false⟩))]))])),(9,(.node [(1,(.node [(0,(.leaf ⟨8,115,7,true⟩))]))]))]))]))])
theorem ok45762 : checkedLeaves maskTest 5 sub45762=true := by decide +kernel
def sub45768 : Cert := (.node [(2,(.node [(3,(.node [(1,(.node [(0,(.node [(9,(.leaf ⟨2,17,5,false⟩))])),(9,(.node [(0,(.leaf ⟨10,17,5,false⟩))]))])),(9,(.node [(1,(.node [(0,(.leaf ⟨14,24,1,false⟩))]))]))]))])),(9,(.node [(3,(.node [(2,(.node [(1,(.node [(0,(.leaf ⟨6,101,6,true⟩))]))]))]))]))])
theorem ok45768 : checkedLeaves maskTest 5 sub45768=true := by decide +kernel
def sub4910 : Cert := (.node [(3,(.node [(2,(.node [(6,(.node [(5,(.node [(8,(.node [(7,(.leaf ⟨3,16,5,true⟩))]))])),(8,(.node [(5,(.node [(7,(.leaf ⟨2,16,5,true⟩))]))]))]))])),(6,(.node [(2,(.node [(5,(.node [(8,(.node [(7,(.leaf ⟨10,71,2,false⟩))]))])),(8,(.node [(5,(.node [(7,(.leaf ⟨13,7,8,false⟩))]))]))])),(8,(.node [(2,(.node [(5,(.node [(7,(.leaf ⟨12,72,3,false⟩))]))]))]))]))]))])
theorem ok4910 : checkedLeaves maskTest 6 sub4910=true := by decide +kernel
def sub491630 : Cert := (.node [(2,(.node [(5,(.node [(8,(.node [(7,(.leaf ⟨8,71,2,false⟩))]))])),(8,(.node [(5,(.node [(7,(.leaf ⟨13,13,6,true⟩))]))]))])),(8,(.node [(2,(.node [(5,(.node [(7,(.leaf ⟨13,72,3,false⟩))]))]))]))])
theorem ok491630 : checkedLeaves maskTest 4 sub491630=true := by decide +kernel
def sub491635 : Cert := (.node [(2,(.node [(0,(.node [(8,(.node [(7,(.leaf ⟨7,71,2,false⟩))]))])),(8,(.node [(0,(.node [(7,(.leaf ⟨19,79,5,false⟩))])),(7,(.node [(0,(.leaf ⟨16,70,3,false⟩))]))]))])),(8,(.node [(2,(.node [(0,(.node [(7,(.leaf ⟨19,2,8,true⟩))])),(7,(.node [(0,(.leaf ⟨19,24,1,false⟩))]))]))]))])
theorem ok491635 : checkedLeaves maskTest 4 sub491635=true := by decide +kernel
def sub491638 : Cert := (.node [(0,(.node [(2,(.node [(5,(.node [(7,(.leaf ⟨8,108,5,true⟩))]))]))])),(5,(.node [(2,(.node [(0,(.node [(7,(.leaf ⟨7,108,5,true⟩))])),(7,(.node [(0,(.leaf ⟨9,108,5,true⟩))]))]))]))])
theorem ok491638 : checkedLeaves maskTest 4 sub491638=true := by decide +kernel
end R67.OrderOrbit
