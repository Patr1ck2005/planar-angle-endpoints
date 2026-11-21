import OrderMaskCore
namespace R67.OrderOrbit
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000
def sub41023 : Cert := (.node [(5,(.node [(6,(.node [(7,(.node [(8,(.node [(9,(.leaf ⟨5,6,9,false⟩))]))])),(9,(.node [(8,(.node [(7,(.leaf ⟨6,6,9,false⟩))]))]))])),(7,(.node [(6,(.node [(8,(.node [(9,(.leaf ⟨4,6,9,false⟩))]))]))]))])),(9,(.node [(6,(.node [(5,(.node [(8,(.node [(7,(.leaf ⟨6,48,1,true⟩))]))])),(8,(.node [(5,(.node [(7,(.leaf ⟨6,100,6,false⟩))]))]))]))]))])
theorem ok41023 : checkedLeaves maskTest 5 sub41023=true := by decide +kernel
def sub41025 : Cert := (.node [(3,(.node [(6,(.node [(7,(.node [(8,(.node [(9,(.leaf ⟨14,6,9,false⟩))]))])),(9,(.node [(8,(.node [(7,(.leaf ⟨6,113,8,true⟩))]))]))])),(7,(.node [(6,(.node [(8,(.node [(9,(.leaf ⟨8,119,9,true⟩))]))]))]))])),(7,(.node [(3,(.node [(6,(.node [(8,(.node [(9,(.leaf ⟨1,119,9,true⟩))]))]))]))]))])
theorem ok41025 : checkedLeaves maskTest 5 sub41025=true := by decide +kernel
def sub4109 : Cert := (.node [(3,(.node [(2,(.node [(6,(.node [(5,(.node [(8,(.node [(7,(.leaf ⟨5,48,1,true⟩))]))])),(8,(.node [(5,(.node [(7,(.leaf ⟨14,48,1,true⟩))]))]))]))])),(6,(.node [(2,(.node [(5,(.node [(8,(.node [(7,(.leaf ⟨4,48,1,true⟩))]))])),(8,(.node [(5,(.node [(7,(.leaf ⟨8,114,7,false⟩))]))]))])),(8,(.node [(2,(.node [(5,(.node [(7,(.leaf ⟨1,114,7,false⟩))]))]))]))]))]))])
theorem ok4109 : checkedLeaves maskTest 6 sub4109=true := by decide +kernel
def sub41520 : Cert := (.node [(3,(.node [(6,(.node [(7,(.node [(8,(.node [(9,(.leaf ⟨14,19,5,true⟩))]))])),(9,(.node [(8,(.node [(7,(.leaf ⟨6,71,2,false⟩))]))]))])),(7,(.node [(6,(.node [(8,(.node [(9,(.leaf ⟨10,119,9,true⟩))]))]))]))])),(7,(.node [(3,(.node [(6,(.node [(8,(.node [(9,(.leaf ⟨2,119,9,true⟩))]))]))]))]))])
theorem ok41520 : checkedLeaves maskTest 5 sub41520=true := by decide +kernel
def sub4152630 : Cert := (.node [(7,(.node [(8,(.node [(9,(.leaf ⟨15,65,3,false⟩))]))])),(9,(.node [(8,(.node [(7,(.leaf ⟨5,71,2,false⟩))]))]))])
theorem ok4152630 : checkedLeaves maskTest 3 sub4152630=true := by decide +kernel
def sub4152637 : Cert := (.node [(0,(.node [(8,(.node [(9,(.leaf ⟨17,48,1,true⟩))]))])),(8,(.node [(0,(.node [(9,(.leaf ⟨17,103,6,false⟩))])),(9,(.node [(0,(.leaf ⟨15,118,8,true⟩))]))]))])
theorem ok4152637 : checkedLeaves maskTest 3 sub4152637=true := by decide +kernel
def sub4152639 : Cert := (.node [(0,(.node [(8,(.node [(7,(.leaf ⟨3,48,1,true⟩))]))])),(8,(.node [(0,(.node [(7,(.leaf ⟨3,103,6,false⟩))])),(7,(.node [(0,(.leaf ⟨5,112,7,true⟩))]))]))])
theorem ok4152639 : checkedLeaves maskTest 3 sub4152639=true := by decide +kernel
def sub415267 : Cert := (.node [(3,(.node [(0,(.node [(8,(.node [(9,(.leaf ⟨16,119,9,true⟩))]))])),(8,(.node [(0,(.node [(9,(.leaf ⟨19,48,1,true⟩))])),(9,(.node [(0,(.leaf ⟨7,118,8,true⟩))]))]))]))])
theorem ok415267 : checkedLeaves maskTest 4 sub415267=true := by decide +kernel
def sub41527 : Cert := (.node [(0,(.node [(3,(.node [(6,(.node [(8,(.node [(9,(.leaf ⟨4,96,4,false⟩))]))]))]))])),(6,(.node [(3,(.node [(0,(.node [(8,(.node [(9,(.leaf ⟨11,84,4,true⟩))]))])),(8,(.node [(0,(.node [(9,(.leaf ⟨9,102,5,false⟩))])),(9,(.node [(0,(.leaf ⟨0,118,8,true⟩))]))]))]))]))])
theorem ok41527 : checkedLeaves maskTest 5 sub41527=true := by decide +kernel
def sub4156230 : Cert := (.node [(7,(.node [(8,(.node [(9,(.leaf ⟨11,5,6,true⟩))]))])),(9,(.node [(8,(.node [(7,(.leaf ⟨4,71,2,false⟩))]))]))])
theorem ok4156230 : checkedLeaves maskTest 3 sub4156230=true := by decide +kernel
end R67.OrderOrbit
