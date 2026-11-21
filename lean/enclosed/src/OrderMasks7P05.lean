import OrderMaskCore
namespace R67.OrderOrbit
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000
def sub78520 : Cert := (.node [(3,(.node [(1,(.node [(6,(.node [(4,(.node [(9,(.leaf ⟨5,13,7,false⟩))])),(9,(.node [(4,(.leaf ⟨4,13,7,false⟩))]))]))])),(6,(.node [(1,(.node [(4,(.node [(9,(.leaf ⟨14,13,7,false⟩))])),(9,(.node [(4,(.leaf ⟨8,71,1,true⟩))]))])),(9,(.node [(1,(.node [(4,(.leaf ⟨1,71,1,true⟩))]))]))]))]))])
theorem ok78520 : checkedLeaves maskTest 5 sub78520=true := by decide +kernel
def sub7852630 : Cert := (.node [(1,(.node [(4,(.node [(9,(.leaf ⟨14,7,7,true⟩))])),(9,(.node [(4,(.leaf ⟨10,71,1,true⟩))]))])),(9,(.node [(1,(.node [(4,(.leaf ⟨2,71,1,true⟩))]))]))])
theorem ok7852630 : checkedLeaves maskTest 3 sub7852630=true := by decide +kernel
def sub7852634 : Cert := (.node [(1,(.node [(0,(.node [(9,(.leaf ⟨15,95,1,false⟩))])),(9,(.node [(0,(.leaf ⟨17,73,3,true⟩))]))])),(9,(.node [(1,(.node [(0,(.leaf ⟨16,71,1,true⟩))]))]))])
theorem ok7852634 : checkedLeaves maskTest 3 sub7852634=true := by decide +kernel
def sub7852639 : Cert := (.node [(0,(.node [(1,(.node [(4,(.leaf ⟨4,48,2,false⟩))]))])),(4,(.node [(1,(.node [(0,(.leaf ⟨11,114,6,true⟩))]))]))])
theorem ok7852639 : checkedLeaves maskTest 3 sub7852639=true := by decide +kernel
def sub785264 : Cert := (.node [(3,(.node [(1,(.node [(0,(.node [(9,(.leaf ⟨11,1,8,true⟩))])),(9,(.node [(0,(.leaf ⟨16,73,3,true⟩))]))])),(9,(.node [(1,(.node [(0,(.leaf ⟨18,0,9,true⟩))]))]))]))])
theorem ok785264 : checkedLeaves maskTest 4 sub785264=true := by decide +kernel
def sub7856230 : Cert := (.node [(1,(.node [(4,(.node [(9,(.leaf ⟨5,7,7,true⟩))])),(9,(.node [(4,(.leaf ⟨3,16,6,false⟩))]))])),(9,(.node [(1,(.node [(4,(.leaf ⟨3,71,1,true⟩))]))]))])
theorem ok7856230 : checkedLeaves maskTest 3 sub7856230=true := by decide +kernel
def sub7856234 : Cert := (.node [(1,(.node [(0,(.node [(9,(.leaf ⟨15,1,8,true⟩))])),(9,(.node [(0,(.leaf ⟨17,16,6,false⟩))]))])),(9,(.node [(1,(.node [(0,(.leaf ⟨17,71,1,true⟩))]))]))])
theorem ok7856234 : checkedLeaves maskTest 3 sub7856234=true := by decide +kernel
def sub7856239 : Cert := (.node [(0,(.node [(1,(.node [(4,(.leaf ⟨5,48,2,false⟩))]))])),(4,(.node [(1,(.node [(0,(.leaf ⟨15,54,3,false⟩))]))]))])
theorem ok7856239 : checkedLeaves maskTest 3 sub7856239=true := by decide +kernel
def sub785624 : Cert := (.node [(3,(.node [(1,(.node [(0,(.node [(9,(.leaf ⟨7,1,8,true⟩))])),(9,(.node [(0,(.leaf ⟨19,71,1,true⟩))]))])),(9,(.node [(1,(.node [(0,(.leaf ⟨16,0,9,true⟩))]))]))]))])
theorem ok785624 : checkedLeaves maskTest 4 sub785624=true := by decide +kernel
def sub78564 : Cert := (.node [(2,(.node [(3,(.node [(1,(.node [(0,(.node [(9,(.leaf ⟨0,1,8,true⟩))])),(9,(.node [(0,(.leaf ⟨9,17,5,false⟩))]))])),(9,(.node [(1,(.node [(0,(.leaf ⟨11,35,4,true⟩))]))]))]))])),(9,(.node [(3,(.node [(2,(.node [(1,(.node [(0,(.leaf ⟨4,23,4,false⟩))]))]))]))]))])
theorem ok78564 : checkedLeaves maskTest 5 sub78564=true := by decide +kernel
def sub78569 : Cert := (.node [(3,(.node [(2,(.node [(0,(.node [(1,(.node [(4,(.leaf ⟨6,48,2,false⟩))]))])),(4,(.node [(1,(.node [(0,(.leaf ⟨14,100,5,true⟩))]))]))])),(4,(.node [(2,(.node [(1,(.node [(0,(.leaf ⟨10,0,9,true⟩))]))]))]))])),(4,(.node [(3,(.node [(2,(.node [(1,(.node [(0,(.leaf ⟨2,0,9,true⟩))]))]))]))]))])
theorem ok78569 : checkedLeaves maskTest 5 sub78569=true := by decide +kernel
end R67.OrderOrbit
