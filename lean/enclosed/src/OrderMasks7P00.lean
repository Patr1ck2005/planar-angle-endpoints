import OrderMaskCore
namespace R67.OrderOrbit
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000
def sub70213 : Cert := (.node [(5,(.node [(4,(.node [(6,(.node [(8,(.node [(9,(.leaf ⟨1,2,9,false⟩))]))]))])),(8,(.node [(6,(.node [(4,(.node [(9,(.leaf ⟨2,2,9,false⟩))])),(9,(.node [(4,(.leaf ⟨3,2,9,false⟩))]))]))]))])),(8,(.node [(5,(.node [(6,(.node [(4,(.node [(9,(.leaf ⟨4,21,4,true⟩))])),(9,(.node [(4,(.leaf ⟨5,21,4,true⟩))]))]))])),(9,(.node [(6,(.node [(5,(.node [(4,(.leaf ⟨6,21,4,true⟩))]))]))]))]))])
theorem ok70213 : checkedLeaves maskTest 5 sub70213=true := by decide +kernel
def sub70215 : Cert := (.node [(3,(.node [(4,(.node [(6,(.node [(8,(.node [(9,(.leaf ⟨8,2,9,false⟩))]))]))])),(8,(.node [(6,(.node [(4,(.node [(9,(.leaf ⟨10,2,9,false⟩))])),(9,(.node [(4,(.leaf ⟨3,117,8,true⟩))]))]))]))])),(4,(.node [(3,(.node [(6,(.node [(8,(.node [(9,(.leaf ⟨4,119,9,true⟩))]))]))]))]))])
theorem ok70215 : checkedLeaves maskTest 5 sub70215=true := by decide +kernel
def sub70251 : Cert := (.node [(3,(.node [(4,(.node [(6,(.node [(8,(.node [(9,(.leaf ⟨14,119,9,true⟩))]))]))])),(8,(.node [(6,(.node [(4,(.node [(9,(.leaf ⟨14,98,5,false⟩))])),(9,(.node [(4,(.leaf ⟨5,98,5,false⟩))]))]))]))])),(4,(.node [(3,(.node [(6,(.node [(8,(.node [(9,(.leaf ⟨5,119,9,true⟩))]))]))]))]))])
theorem ok70251 : checkedLeaves maskTest 5 sub70251=true := by decide +kernel
def sub70258 : Cert := (.node [(3,(.node [(1,(.node [(6,(.node [(4,(.node [(9,(.leaf ⟨15,78,3,true⟩))])),(9,(.node [(4,(.leaf ⟨15,108,6,false⟩))]))]))])),(6,(.node [(1,(.node [(4,(.node [(9,(.leaf ⟨11,108,6,false⟩))])),(9,(.node [(4,(.leaf ⟨7,108,6,false⟩))]))])),(9,(.node [(1,(.node [(4,(.leaf ⟨0,108,6,false⟩))]))]))]))]))])
theorem ok70258 : checkedLeaves maskTest 5 sub70258=true := by decide +kernel
def sub702831 : Cert := (.node [(5,(.node [(6,(.node [(4,(.node [(9,(.leaf ⟨11,41,4,false⟩))])),(9,(.node [(4,(.leaf ⟨15,11,5,true⟩))]))]))])),(9,(.node [(6,(.node [(5,(.node [(4,(.leaf ⟨14,47,3,false⟩))]))]))]))])
theorem ok702831 : checkedLeaves maskTest 4 sub702831=true := by decide +kernel
def sub702835 : Cert := (.node [(1,(.node [(6,(.node [(4,(.node [(9,(.leaf ⟨16,2,9,false⟩))])),(9,(.node [(4,(.leaf ⟨17,2,9,false⟩))]))]))])),(6,(.node [(1,(.node [(4,(.node [(9,(.leaf ⟨18,2,9,false⟩))])),(9,(.node [(4,(.leaf ⟨16,109,7,false⟩))]))])),(9,(.node [(1,(.node [(4,(.leaf ⟨11,48,2,false⟩))]))]))]))])
theorem ok702835 : checkedLeaves maskTest 4 sub702835=true := by decide +kernel
def sub702839 : Cert := (.node [(1,(.node [(6,(.node [(5,(.node [(4,(.leaf ⟨10,109,7,false⟩))]))]))])),(6,(.node [(1,(.node [(5,(.node [(4,(.leaf ⟨2,109,7,false⟩))]))])),(5,(.node [(1,(.node [(4,(.leaf ⟨4,106,6,true⟩))]))]))]))])
theorem ok702839 : checkedLeaves maskTest 4 sub702839=true := by decide +kernel
def sub70285 : Cert := (.node [(3,(.node [(1,(.node [(6,(.node [(4,(.node [(9,(.leaf ⟨17,95,1,false⟩))])),(9,(.node [(4,(.leaf ⟨17,117,8,true⟩))]))]))])),(6,(.node [(1,(.node [(4,(.node [(9,(.leaf ⟨16,95,1,false⟩))])),(9,(.node [(4,(.leaf ⟨19,2,9,false⟩))]))])),(9,(.node [(1,(.node [(4,(.leaf ⟨9,116,7,true⟩))]))]))]))]))])
theorem ok70285 : checkedLeaves maskTest 5 sub70285=true := by decide +kernel
end R67.OrderOrbit
