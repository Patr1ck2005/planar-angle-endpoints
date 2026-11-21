import OrderOrb0
import OrderMasks0P00
import OrderMasks0P01
import OrderMasks0P02
import OrderMasks0P03
import OrderMasks0P04
namespace R67.OrderOrbit
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000
private theorem consPass {P : Sym→Bool} {n : ℕ} (e : E) {t : Cert} {ts : List (E×Cert)} (h : checkedLeaves P n t=true)
    (hs : ts.all (fun x=>checkedLeaves P n x.2)=true) :
    ((e,t)::ts).all (fun x=>checkedLeaves P n x.2)=true := by simp only [List.all_cons,h,hs,Bool.and_true]
private theorem nodePass {P : Sym→Bool} {n : ℕ} {ts : List (E×Cert)}
    (hs : ts.all (fun x=>checkedLeaves P n x.2)=true) :
    checkedLeaves P (n+1) (.node ts)=true := hs
theorem masks0 : checkedLeaves maskTest 9 tree0=true :=
  (nodePass (consPass 1 (nodePass (consPass 2 (nodePass (consPass 3 (nodePass (consPass 4 ok01234 (consPass 7 ok01237 (consPass 9 ok01239 (rfl : (List.all [] _) = true))))) (consPass 4 (nodePass (consPass 3 ok01243 (consPass 5 ok01245 (rfl : (List.all [] _) = true)))) (consPass 7 (nodePass (consPass 3 ok01273 (consPass 5 ok01275 (rfl : (List.all [] _) = true)))) (rfl : (List.all [] _) = true))))) (consPass 4 (nodePass (consPass 2 (nodePass (consPass 3 ok01423 (consPass 5 ok01425 (rfl : (List.all [] _) = true)))) (consPass 9 ok0149 (rfl : (List.all [] _) = true)))) (consPass 9 (nodePass (consPass 3 (nodePass (consPass 2 ok01932 (consPass 4 ok01934 (consPass 8 ok01938 (rfl : (List.all [] _) = true))))) (consPass 4 ok0194 (rfl : (List.all [] _) = true)))) (rfl : (List.all [] _) = true))))) (consPass 7 (nodePass (consPass 2 (nodePass (consPass 1 (nodePass (consPass 3 ok07213 (consPass 5 ok07215 (rfl : (List.all [] _) = true)))) (consPass 5 (nodePass (consPass 1 ok07251 (consPass 8 ok07258 (rfl : (List.all [] _) = true)))) (consPass 8 (nodePass (consPass 3 (nodePass (consPass 1 ok072831 (consPass 5 ok072835 (consPass 9 ok072839 (rfl : (List.all [] _) = true))))) (consPass 5 ok07285 (rfl : (List.all [] _) = true)))) (rfl : (List.all [] _) = true))))) (consPass 8 (nodePass (consPass 2 (nodePass (consPass 3 (nodePass (consPass 1 ok078231 (consPass 5 ok078235 (consPass 9 ok078239 (rfl : (List.all [] _) = true))))) (consPass 5 ok07825 (rfl : (List.all [] _) = true)))) (consPass 9 ok0789 (rfl : (List.all [] _) = true)))) (rfl : (List.all [] _) = true)))) (consPass 9 (nodePass (consPass 1 (nodePass (consPass 3 (nodePass (consPass 2 ok09132 (consPass 4 ok09134 (consPass 8 ok09138 (rfl : (List.all [] _) = true))))) (consPass 4 ok0914 (rfl : (List.all [] _) = true)))) (consPass 8 (nodePass (consPass 3 (nodePass (consPass 1 ok09831 (consPass 6 ok09836 (consPass 7 ok09837 (rfl : (List.all [] _) = true))))) (consPass 7 ok0987 (rfl : (List.all [] _) = true)))) (rfl : (List.all [] _) = true)))) (rfl : (List.all [] _) = true)))))
end R67.OrderOrbit
