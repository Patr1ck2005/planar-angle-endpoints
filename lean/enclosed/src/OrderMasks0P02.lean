import OrderMaskCore
namespace R67.OrderOrbit
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000
def sub07213 : Cert := (.node [(5,(.node [(4,(.node [(6,(.node [(8,(.node [(9,(.leaf ⟨12,21,4,true⟩))]))]))])),(8,(.node [(6,(.node [(4,(.node [(9,(.leaf ⟨13,21,4,true⟩))])),(9,(.node [(4,(.leaf ⟨10,117,8,true⟩))]))]))]))])),(8,(.node [(5,(.node [(6,(.node [(4,(.node [(9,(.leaf ⟨8,41,4,false⟩))])),(9,(.node [(4,(.leaf ⟨14,21,4,true⟩))]))]))])),(9,(.node [(6,(.node [(5,(.node [(4,(.leaf ⟨6,47,3,false⟩))]))]))]))]))])
theorem ok07213 : checkedLeaves maskTest 5 sub07213=true := by decide +kernel
def sub07215 : Cert := (.node [(3,(.node [(4,(.node [(6,(.node [(8,(.node [(9,(.leaf ⟨13,119,9,true⟩))]))]))])),(8,(.node [(6,(.node [(4,(.node [(9,(.leaf ⟨13,98,5,false⟩))])),(9,(.node [(4,(.leaf ⟨2,117,8,true⟩))]))]))]))])),(4,(.node [(3,(.node [(6,(.node [(8,(.node [(9,(.leaf ⟨2,96,4,false⟩))]))]))]))]))])
theorem ok07215 : checkedLeaves maskTest 5 sub07215=true := by decide +kernel
def sub07251 : Cert := (.node [(3,(.node [(4,(.node [(6,(.node [(8,(.node [(9,(.leaf ⟨10,78,3,true⟩))]))]))])),(8,(.node [(6,(.node [(4,(.node [(9,(.leaf ⟨8,78,3,true⟩))])),(9,(.node [(4,(.leaf ⟨4,98,5,false⟩))]))]))]))])),(4,(.node [(3,(.node [(6,(.node [(8,(.node [(9,(.leaf ⟨3,96,4,false⟩))]))]))]))]))])
theorem ok07251 : checkedLeaves maskTest 5 sub07251=true := by decide +kernel
def sub07258 : Cert := (.node [(3,(.node [(1,(.node [(6,(.node [(4,(.node [(9,(.leaf ⟨7,78,3,true⟩))])),(9,(.node [(4,(.leaf ⟨11,78,3,true⟩))]))]))])),(6,(.node [(1,(.node [(4,(.node [(9,(.leaf ⟨9,78,3,true⟩))])),(9,(.node [(4,(.leaf ⟨9,108,6,false⟩))]))])),(9,(.node [(1,(.node [(4,(.leaf ⟨0,116,7,true⟩))]))]))]))]))])
theorem ok07258 : checkedLeaves maskTest 5 sub07258=true := by decide +kernel
def sub072831 : Cert := (.node [(5,(.node [(6,(.node [(4,(.node [(9,(.leaf ⟨7,41,4,false⟩))])),(9,(.node [(4,(.leaf ⟨15,41,4,false⟩))]))]))])),(9,(.node [(6,(.node [(5,(.node [(4,(.leaf ⟨5,47,3,false⟩))]))]))]))])
theorem ok072831 : checkedLeaves maskTest 4 sub072831=true := by decide +kernel
def sub072835 : Cert := (.node [(1,(.node [(6,(.node [(4,(.node [(9,(.leaf ⟨19,109,7,false⟩))])),(9,(.node [(4,(.leaf ⟨17,24,0,true⟩))]))]))])),(6,(.node [(1,(.node [(4,(.node [(9,(.leaf ⟨16,40,5,false⟩))])),(9,(.node [(4,(.leaf ⟨17,109,7,false⟩))]))])),(9,(.node [(1,(.node [(4,(.leaf ⟨15,116,7,true⟩))]))]))]))])
theorem ok072835 : checkedLeaves maskTest 4 sub072835=true := by decide +kernel
def sub072839 : Cert := (.node [(1,(.node [(6,(.node [(5,(.node [(4,(.leaf ⟨3,24,0,true⟩))]))]))])),(6,(.node [(1,(.node [(5,(.node [(4,(.leaf ⟨3,109,7,false⟩))]))])),(5,(.node [(1,(.node [(4,(.leaf ⟨5,106,6,true⟩))]))]))]))])
theorem ok072839 : checkedLeaves maskTest 4 sub072839=true := by decide +kernel
def sub07285 : Cert := (.node [(3,(.node [(1,(.node [(6,(.node [(4,(.node [(9,(.leaf ⟨19,10,6,true⟩))])),(9,(.node [(4,(.leaf ⟨16,117,8,true⟩))]))]))])),(6,(.node [(1,(.node [(4,(.node [(9,(.leaf ⟨19,49,3,false⟩))])),(9,(.node [(4,(.leaf ⟨19,24,0,true⟩))]))])),(9,(.node [(1,(.node [(4,(.leaf ⟨7,116,7,true⟩))]))]))]))]))])
theorem ok07285 : checkedLeaves maskTest 5 sub07285=true := by decide +kernel
end R67.OrderOrbit
