import OrderOrb9
import OrderMasks9P00
import OrderMasks9P01
import OrderMasks9P02
import OrderMasks9P03
import OrderMasks9P04
import OrderMasks9P05
namespace R67.OrderOrbit
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000
private theorem consPass {P : Sym→Bool} {n : ℕ} (e : E) {t : Cert} {ts : List (E×Cert)} (h : checkedLeaves P n t=true)
    (hs : ts.all (fun x=>checkedLeaves P n x.2)=true) :
    ((e,t)::ts).all (fun x=>checkedLeaves P n x.2)=true := by simp only [List.all_cons,h,hs,Bool.and_true]
private theorem nodePass {P : Sym→Bool} {n : ℕ} {ts : List (E×Cert)}
    (hs : ts.all (fun x=>checkedLeaves P n x.2)=true) :
    checkedLeaves P (n+1) (.node ts)=true := hs
theorem masks9 : checkedLeaves maskTest 9 tree9=true :=
  (nodePass (consPass 0 (nodePass (consPass 1 (nodePass (consPass 3 (nodePass (consPass 2 ok90132 (consPass 4 ok90134 (consPass 8 ok90138 (rfl : (List.all [] _) = true))))) (consPass 4 ok9014 (rfl : (List.all [] _) = true)))) (consPass 8 (nodePass (consPass 3 (nodePass (consPass 1 ok90831 (consPass 6 ok90836 (consPass 7 ok90837 (rfl : (List.all [] _) = true))))) (consPass 7 ok9087 (rfl : (List.all [] _) = true)))) (rfl : (List.all [] _) = true)))) (consPass 4 (nodePass (consPass 1 (nodePass (consPass 0 ok9410 (consPass 6 (nodePass (consPass 3 (nodePass (consPass 0 ok941630 (consPass 5 ok941635 (consPass 8 ok941638 (rfl : (List.all [] _) = true))))) (consPass 5 ok94165 (rfl : (List.all [] _) = true)))) (rfl : (List.all [] _) = true)))) (consPass 6 (nodePass (consPass 1 (nodePass (consPass 3 (nodePass (consPass 0 ok946130 (consPass 5 ok946135 (consPass 8 ok946138 (rfl : (List.all [] _) = true))))) (consPass 5 ok94615 (rfl : (List.all [] _) = true)))) (consPass 5 (nodePass (consPass 1 ok94651 (consPass 8 ok94658 (rfl : (List.all [] _) = true)))) (consPass 8 (nodePass (consPass 3 ok94683 (consPass 5 ok94685 (rfl : (List.all [] _) = true)))) (rfl : (List.all [] _) = true))))) (rfl : (List.all [] _) = true)))) (consPass 8 (nodePass (consPass 0 (nodePass (consPass 3 (nodePass (consPass 1 ok98031 (consPass 6 ok98036 (consPass 7 ok98037 (rfl : (List.all [] _) = true))))) (consPass 7 ok9807 (rfl : (List.all [] _) = true)))) (consPass 6 (nodePass (consPass 3 (nodePass (consPass 0 ok98630 (consPass 4 ok98634 (consPass 7 ok98637 (rfl : (List.all [] _) = true))))) (consPass 4 (nodePass (consPass 3 ok98643 (consPass 5 ok98645 (rfl : (List.all [] _) = true)))) (consPass 7 (nodePass (consPass 3 ok98673 (consPass 5 ok98675 (rfl : (List.all [] _) = true)))) (rfl : (List.all [] _) = true))))) (consPass 7 (nodePass (consPass 0 ok9870 (consPass 6 (nodePass (consPass 3 ok98763 (consPass 5 ok98765 (rfl : (List.all [] _) = true)))) (rfl : (List.all [] _) = true)))) (rfl : (List.all [] _) = true))))) (rfl : (List.all [] _) = true)))))
end R67.OrderOrbit
