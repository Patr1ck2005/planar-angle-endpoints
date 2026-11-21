import OrderMaskCore
namespace R67.OrderOrbit
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000
def sub4156237 : Cert := (.node [(0,(.node [(8,(.node [(9,(.leaf ⟨16,48,1,true⟩))]))])),(8,(.node [(0,(.node [(9,(.leaf ⟨17,46,3,true⟩))])),(9,(.node [(0,(.leaf ⟨15,24,1,false⟩))]))]))])
theorem ok4156237 : checkedLeaves maskTest 3 sub4156237=true := by decide +kernel
def sub4156239 : Cert := (.node [(0,(.node [(8,(.node [(7,(.leaf ⟨2,48,1,true⟩))]))])),(8,(.node [(0,(.node [(7,(.leaf ⟨10,48,1,true⟩))])),(7,(.node [(0,(.leaf ⟨14,112,7,true⟩))]))]))])
theorem ok4156239 : checkedLeaves maskTest 3 sub4156239=true := by decide +kernel
def sub415627 : Cert := (.node [(3,(.node [(0,(.node [(8,(.node [(9,(.leaf ⟨18,4,7,true⟩))]))])),(8,(.node [(0,(.node [(9,(.leaf ⟨16,46,3,true⟩))])),(9,(.node [(0,(.leaf ⟨11,118,8,true⟩))]))]))]))])
theorem ok415627 : checkedLeaves maskTest 4 sub415627=true := by decide +kernel
def sub41569 : Cert := (.node [(3,(.node [(2,(.node [(0,(.node [(8,(.node [(7,(.leaf ⟨1,48,1,true⟩))]))])),(8,(.node [(0,(.node [(7,(.leaf ⟨8,48,1,true⟩))])),(7,(.node [(0,(.leaf ⟨14,106,7,false⟩))]))]))])),(8,(.node [(2,(.node [(0,(.node [(7,(.leaf ⟨4,106,7,false⟩))])),(7,(.node [(0,(.leaf ⟨5,106,7,false⟩))]))]))]))]))])
theorem ok41569 : checkedLeaves maskTest 5 sub41569=true := by decide +kernel
def sub4190 : Cert := (.node [(3,(.node [(2,(.node [(6,(.node [(5,(.node [(8,(.node [(7,(.leaf ⟨3,71,2,false⟩))]))])),(8,(.node [(5,(.node [(7,(.leaf ⟨10,16,5,true⟩))]))]))]))])),(6,(.node [(2,(.node [(5,(.node [(8,(.node [(7,(.leaf ⟨2,71,2,false⟩))]))])),(8,(.node [(5,(.node [(7,(.leaf ⟨13,48,1,true⟩))]))]))])),(8,(.node [(2,(.node [(5,(.node [(7,(.leaf ⟨12,110,6,true⟩))]))]))]))]))]))])
theorem ok4190 : checkedLeaves maskTest 6 sub4190=true := by decide +kernel
def sub419630 : Cert := (.node [(2,(.node [(5,(.node [(8,(.node [(7,(.leaf ⟨1,71,2,false⟩))]))])),(8,(.node [(5,(.node [(7,(.leaf ⟨12,48,1,true⟩))]))]))])),(8,(.node [(2,(.node [(5,(.node [(7,(.leaf ⟨12,116,8,false⟩))]))]))]))])
theorem ok419630 : checkedLeaves maskTest 4 sub419630=true := by decide +kernel
def sub419635 : Cert := (.node [(2,(.node [(0,(.node [(8,(.node [(7,(.leaf ⟨0,71,2,false⟩))]))])),(8,(.node [(0,(.node [(7,(.leaf ⟨9,48,1,true⟩))])),(7,(.node [(0,(.leaf ⟨11,116,8,false⟩))]))]))])),(8,(.node [(2,(.node [(0,(.node [(7,(.leaf ⟨9,116,8,false⟩))])),(7,(.node [(0,(.leaf ⟨7,116,8,false⟩))]))]))]))])
theorem ok419635 : checkedLeaves maskTest 4 sub419635=true := by decide +kernel
def sub419638 : Cert := (.node [(0,(.node [(2,(.node [(5,(.node [(7,(.leaf ⟨1,108,5,true⟩))]))]))])),(5,(.node [(2,(.node [(0,(.node [(7,(.leaf ⟨0,108,5,true⟩))])),(7,(.node [(0,(.leaf ⟨0,116,8,false⟩))]))]))]))])
theorem ok419638 : checkedLeaves maskTest 4 sub419638=true := by decide +kernel
def sub41965 : Cert := (.node [(3,(.node [(2,(.node [(0,(.node [(8,(.node [(7,(.leaf ⟨0,48,1,true⟩))]))])),(8,(.node [(0,(.node [(7,(.leaf ⟨7,48,1,true⟩))])),(7,(.node [(0,(.leaf ⟨15,48,1,true⟩))]))]))])),(8,(.node [(2,(.node [(0,(.node [(7,(.leaf ⟨11,48,1,true⟩))])),(7,(.node [(0,(.leaf ⟨15,116,8,false⟩))]))]))]))]))])
theorem ok41965 : checkedLeaves maskTest 5 sub41965=true := by decide +kernel
end R67.OrderOrbit
